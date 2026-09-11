import LeanUtils.ExtractSorry
import Lean.Meta.Basic

/-!
# Locating one `sorry` in a file's info trees

Given a `ParsedSorry` (position, parent declaration, goal text) this module
re-elaborates the file and recovers the elaboration state at that token: the
`ContextInfo`, the local context, and the goal type.  `KernelCheck` uses it to
check a candidate proof term against that goal, and `ExtractGoal` uses it to
restate the goal as a standalone theorem.

Two situations need care:
* a `sorry` tactic also elaborates to a `sorry` term, so one token yields two
  nodes; they carry the same type and either will do;
* one token can close several goals (`constructor <;> sorry`, `all_goals sorry`).
  The recorded goal text then selects the intended one, compared with whitespace
  collapsed because different tools wrap goals at different widths.
-/

open Lean Meta Elab Term Expr Meta Tactic

/-- The elaboration state at one `sorry`. -/
structure TargetEnvData where
  ctx : ContextInfo
  lctx : LocalContext
  type : Expr
  /-- Start positions of the enclosing commands, outermost first: the
  declaration's own command and any `… in` wrappers around it. -/
  commandPositions : List Position

private structure MatchedTarget where
  ctx : ContextInfo
  type? : Option Expr
  goal? : Option MVarId
  lctx : LocalContext
  commandPositions : List Position := []

/-- Collapse all whitespace, so goals that differ only in line wrapping compare equal.

The dataset's goal text was rendered by SorryDB's REPL at a different line width than
`ExtractSorry` uses here; the content is identical, the line breaks are not. -/
def goalConclusion (s : String) : String :=
  -- everything after the LAST turnstile; resets the accumulator at each one
  s.foldl (fun acc c => if c == '⊢' then "" else acc.push c) ""

def normalizeGoalText (s : String) : String :=
  -- character fold rather than `String.split`: the latter returns `List String` on
  -- some toolchains and `Std.Iter String.Slice` on others, which breaks the build
  -- for whichever Lean versions the fleet does not happen to be tested against.
  (s.foldl (fun acc c =>
      if c.isWhitespace then
        if acc.endsWith " " then acc else acc.push ' '
      else acc.push c) "").trim

def findTargetEnv (tree : InfoTree) (targetSorry : ParsedSorry) : IO (List TargetEnvData) := do
  let matched ← tree.visitM (m := IO) (postNode := fun ctx info _ children => do
    let targets : List MatchedTarget := (children.flatMap' Option.toList).flatten'
    match info with
    | .ofTermInfo ti =>
        if !targetSorry.acceptsKind "term" || !isSorryTerm ti.stx then
          return targets
        let some pos := ti.stx.getPos? | return targets
        if targetSorry.startPos != ctx.fileMap.toPosition pos then
          return targets
        let some type := ti.expectedType? | return targets
        return targets ++ [{
          ctx
          type? := some type
          goal? := none
          lctx := ti.lctx
        }]
    | .ofTacticInfo ti =>
        if !targetSorry.acceptsKind "tactic" || !isSorryTactic ti.stx then
          return targets
        let some pos := ti.stx.getPos? | return targets
        if targetSorry.startPos != ctx.fileMap.toPosition pos then
          return targets
        let goal ← match ti.goalsBefore with
          | [goal] => pure goal
          | goals => do
            -- A single `sorry` token can close several goals (`constructor <;> sorry`).
            -- SorryDB records one entry per goal, all sharing this source position, so
            -- the entry's printed goal is what distinguishes them.  Select the matching
            -- one instead of refusing; still refuse if it is ambiguous.
            let mut matching : List MVarId := []
            for candidate in goals do
              if let some mdecl := ti.mctxBefore.decls.find? candidate then
                let rendered ← ctx.runMetaM mdecl.lctx do
                  return toString (← ppGoal candidate)
                if normalizeGoalText rendered == normalizeGoalText targetSorry.goal then
                  matching := matching ++ [candidate]
            match matching with
            | [goal] => pure goal
            | _ =>
              -- report how the selection went, so a rendering mismatch (0 matched)
              -- can be told apart from a genuinely ambiguous token (>1 matched)
              let rendered ← goals.mapM fun candidate => do
                match ti.mctxBefore.decls.find? candidate with
                | some mdecl => ctx.runMetaM mdecl.lctx do return toString (← ppGoal candidate)
                | none => pure "<no mvar decl>"
              throw (IO.userError s!"Found more than one goal ({goals.length} goals, \
                {matching.length} matched target); target={(normalizeGoalText targetSorry.goal).take 300}; \
                candidates={(rendered.map fun r => (normalizeGoalText r).take 300)}")
        let some mdecl := ti.mctxBefore.decls.find? goal
          | throw (IO.userError "Could not recover the target goal's local context")
        return targets ++ [{
          ctx
          type? := none
          goal? := some goal
          lctx := mdecl.lctx
        }]
    | .ofCommandInfo ci =>
        let some pos := ci.stx.getPos? | return targets
        let commandPos := ctx.fileMap.toPosition pos
        return targets.map fun target =>
          { target with commandPositions := commandPos :: target.commandPositions }
    | _ => return targets)

  let matched := matched.get!
  let targetDatas ← matched.mapM fun target => do
    target.ctx.runMetaM target.lctx do
      let type ← match target.type?, target.goal? with
        | some type, none => pure type
        | none, some goal => goal.getType
        | _, _ => throwError "Bad case"
      return [{
        ctx := target.ctx
        lctx := target.lctx
        type
        commandPositions :=
          if target.commandPositions.isEmpty then [targetSorry.startPos]
          else target.commandPositions
      }]

  return targetDatas.flatten'.filter fun data =>
    data.ctx.parentDecl? == some targetSorry.parentDecl


def findSorryTargetFromFile (path rawSorry : String) : IO (Except String (FileMap × TargetEnvData)) := do
  unsafe enableInitializersExecution
  let path : System.FilePath := { toString := path }
  let path ← IO.FS.realPath path
  let projectSearchPath ← getProjectSearchPath path
  searchPathRef.set projectSearchPath
  let a := Json.parse rawSorry
  let json ← match a with
    | .ok json => pure json
    | .error e => return .error s!"Failed to parse input as valid JSON {e}"

  let parsedSorry : ParsedSorry ← match (Lean.FromJson.fromJson? json) with
  | .ok parsedSorry => pure parsedSorry
  | .error e => return .error s!"Failed to deserialize ParsedSorry: {e}"

  let (fileMap, trees) ← extractInfoTrees path

  let targetEnvs ← trees.mapM (fun t => findTargetEnv t parsedSorry)

  let targetEnvs := targetEnvs.flatten'
  -- We might have both term-mode and tactic-mode info trees for the same source-level 'sorry'
  -- (since the 'sorry' tactic will end up emitting a 'sorry' term)
  -- We just pick the first one - as long as they all have the same type (which we check),
  -- shouldn't matter
  let some singleData := targetEnvs[0]? | return .error s!"Did not find any targetEnv"
  if targetEnvs.all (fun d => d.type == singleData.type) then
    return .ok (fileMap, singleData)
  -- One source `sorry` can legitimately close SEVERAL goals (`all_goals sorry`,
  -- `<;> sorry`), so the infotrees genuinely carry different types.  That is not an
  -- ambiguity to give up on: the recorded goal says which one this task is.  Match on
  -- the conclusion -- sibling goals share a local context and differ only in the target.
  let wantConcl := normalizeGoalText (goalConclusion parsedSorry.goal)
  let mut matching : List TargetEnvData := []
  let mut rendered : List String := []
  for d in targetEnvs do
    let txt ← d.ctx.runMetaM d.lctx do
      return toString (← ppExpr (← instantiateMVars d.type))
    rendered := rendered ++ [normalizeGoalText txt]
    if normalizeGoalText txt == wantConcl then
      matching := matching ++ [d]
  match matching with
  | d :: _ => return .ok (fileMap, d)
  | [] =>
    return .error s!"Found different types for infotrees corresponding to same sorry; \
      target={wantConcl.take 200}; candidates={rendered.map (·.take 200)}"
