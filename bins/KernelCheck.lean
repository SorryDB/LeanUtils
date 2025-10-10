import LeanUtils.ExtractSorry
import Lean.Meta.Basic

open Lean Meta Elab Term Expr Meta Tactic

-- TODO - decide on a format (something like lean4export)
-- that lets us roundtrip Exprs without running tactics/elab
structure SerializedExpr where
  expr: Expr

def serializeExpr (expr: Expr): SerializedExpr := { expr := expr }
def deserializeExpr (expr: SerializedExpr): Expr := expr.expr




def extractHypsFromGoal (mvarId : MVarId) : MetaM (Array LocalDecl) := do
  mvarId.withContext do
    pure <| (← getLCtx).foldl (init := #[]) fun acc decl =>
      if decl.isAuxDecl || decl.isImplementationDetail then acc else acc.push decl



structure TargetEnvData where
  ctx: ContextInfo
  theoremVal: TheoremVal
  type: Expr
  goal : Option MVarId
  mctx : Option MetavarContext


def elabStringAsExpr (code : String) (data : TargetEnvData) : TermElabM Expr := do
  setEnv data.ctx.env
  withMCtx data.mctx.get! do



  -- let a := trace.Elab.debug.set · true
  -- withOptions (trace.Elab.debug.set · true) <| do
  -- parse the string as a syntax tree



  -- https://github.com/dwrensha/tryAtEachStep/blob/6c5d6d5913ab7cdf24a512c42211dc552d279519/tryAtEachStep.lean#L328
  if let some goal := data.goal then

    let lctx ← getLCtx


    let inputCtx := Parser.mkInputContext code "<argument>"
    let tokens := Parser.Module.updateTokens (Parser.getTokenTable data.ctx.env)
    IO.eprintln s!"Got new tokens: {inputCtx.input}"
    let s := Parser.tacticParser.fn.run
                inputCtx {env := data.ctx.env, options := {}} tokens (Parser.mkParserState inputCtx.input)

    let stx ← match s.errorMsg with
    | some errorMsg =>
      IO.eprintln s!"failed to parse {code}: {errorMsg}"
      panic! "parse error"
    | none =>
      pure (if s.stxStack.isEmpty then .missing else s.stxStack.back)

    let results ← Tactic.run goal (Tactic.evalTactic stx)
    if !results.isEmpty then
      throwError s!"Tactic produced subgoals: {repr results}"
    else
      let expr ← Lean.instantiateMVars (Expr.mvar goal)
      IO.eprintln s!"Expr: {expr}"

      let hyps ← extractHypsFromGoal goal
      let fvars := hyps.map (fun d => Expr.fvar d.fvarId)
      --let fvars :=  ((lctx.decls.toArray.toList.flatMap (Option.toList))).map (fun d => Expr.fvar d.fvarId)
      --IO.eprintln s!"Fvars:"
      let newTerm ← Lean.Meta.mkForallFVars fvars expr
      IO.eprintln s!"New term: {newTerm}"
      pure expr

  else
    let stx := (Parser.runParserCategory (← getEnv) `term code)
    let stx ← match stx with
    | .ok stx => pure stx
    | .error msg => throwError msg
    -- elaborate it into an expression
    withoutErrToSorry do
      -- Just running 'elabTerm' is not enough, since we may have a 'by' term,
      -- which requires us to run tactics (which is done by elabTermAndSynthesize)
      -- See also: https://github.com/leanprover-community/mathlib4/wiki/Metaprogramming-gotchas#forgetting-to-complete-elaboration-by-synthesizing-pending-synthetic-metavariables
      elabTermAndSynthesize stx (some data.type)

/-
  Find all constant names in `e` that occur in `names` list
  We don't unfold any constant definitions
-/
partial def Lean.Expr.collectNames (e : Expr) (names : List Name) : List Name :=
  let go a := Lean.Expr.collectNames a names
  match e with
  | .const name _ => if name ∈ names then [name] else []
  | .app f a        => go f ++ go a
  | .lam _ ty bd _  => go ty ++ go bd
  | .forallE _ ty bd _ => go ty ++ go bd
  | .letE _ ty val bd _ => go ty ++ go val ++ go bd
  | .mdata _ b      => go b
  | .lit _ | .sort _ | .proj _ _ _|  .mvar _ | .fvar _ | .bvar _ => []

inductive KernelCheckResult where
| success
| error (e: String)
deriving Repr


def findTargetEnv (tree: InfoTree) (targetSorry: ParsedSorry): IO (List TargetEnvData) := do
  -- TODO - explain why an empty LocalContext is okay. Maybe - local context occurs within TermElabM - we're at top-level decl, so no local context
  let a ←  (do (tree.visitM (m := IO) (postNode := fun ctx i _ as => do
    let head := (as.flatMap' Option.toList).flatten'
    match i with
    -- TODO - deduplicate this
    | .ofTermInfo ti =>
      if targetSorry.pos == ctx.fileMap.toPosition ti.stx.getPos?.get! && isSorryTerm ti.stx then do
        return head
        -- if let some type := ti.expectedType? then
        --   return head ++ ([(ctx, some (type), none)])
        -- else
        --   return head ++ [(ctx, none, none)]
      else
        return head
    | .ofTacticInfo ti =>
      -- TODO - do we need the 'mctxBefore' stuff from 'visitSorryNode'?
      if targetSorry.pos == ctx.fileMap.toPosition ti.stx.getPos?.get! && isSorryTactic ti.stx then do
        let goal ← if let [goal] := ti.goalsBefore then pure goal else (throw (IO.userError "Found more than one goal"))
        IO.println s!"Got goal: {repr goal}"
        return head ++ ([(ctx, none, some goal, some ti.mctxBefore)])
      else
        return head
    | _ => return head

  )))

  let matchedCtxs := a.get!
  let targetDatas ← (matchedCtxs.mapM (fun (ctx, type, goal, mctx) => do
    ctx.runMetaM {} do
      if let some oldDecl :=  ctx.env.find? targetSorry.parentDecl then
        match oldDecl with
        | .thmInfo info =>
          match (type, goal, mctx) with
          | (some type, none, mctx) => return [({ctx := ctx, theoremVal := info, type := type, goal := none, mctx := mctx} : TargetEnvData)]
          | (none, some goal, mctx) =>
              let goalType ← goal.getType
              return [({ctx := ctx, theoremVal := info, type := goalType, goal := some goal, mctx := mctx} : TargetEnvData)]
          | _ => throwError "Bad case"
        | _ => throwError "Bad decl type"
      else
        throwError ("Missing parentDecl in environment")
  ))
  let allTargets := targetDatas.flatten'.filter (fun data => data.ctx.parentDecl? == (some targetSorry.parentDecl))
  return allTargets


structure KernelCheckOutput where
  success: Bool
  error: Option String
deriving ToJson

/-
check that `expr` has type `type`
-/
-- TODO - change the error type to make it harder to accidentally return success
-- remove the 'panics'
def kernelCheck (sorryFilePath: System.FilePath) (targetData: TargetEnvData) (expr : SerializedExpr) (type: Expr) (fileMap: FileMap) (bannedNames : List Name) : IO (KernelCheckOutput) := do
  let expr := deserializeExpr expr
  let (res, _) ← Core.CoreM.toIO (ctx := {fileName := sorryFilePath.fileName.get!, fileMap := fileMap}) (s := { env := targetData.ctx.env }) do
    let bannedNames := (expr.collectNames bannedNames).dedup'
    if !bannedNames.isEmpty then
      return {
        success := false,
        error := some s!"Contains banned constant names: {bannedNames}"
      }
    else
      try
        addDecl (Declaration.thmDecl {targetData.theoremVal with value := expr, type := type, name := ← mkFreshId})
        return {
          success := true,
          error := none
        }
      catch e =>
        return {
          success := true,
          error := ← e.toMessageData.toString
        }
  return res

def parseAndCheck (args : List String): IO KernelCheckOutput := do
  if let [path, rawSorry, rawExpr] := args then
    unsafe enableInitializersExecution
    let path : System.FilePath := { toString := path }
    let path ← IO.FS.realPath path
    let projectSearchPath ← getProjectSearchPath path
    searchPathRef.set projectSearchPath
    let a := Json.parse rawSorry
    let json ← match a with
      | .ok json => pure json
      | .error e => return {
        success := false,
        error := some s!"Failed to parse input as valid JSON {e}"
      }

    let parsedSorry: ParsedSorry ← match (Lean.FromJson.fromJson? json) with
    | .ok parsedSorry => pure parsedSorry
    | .error e => return {
      success := false
      error := some s!"Failed to deserialize ParsedSorry: {e}"
    }

    let (fileMap, trees) ← extractInfoTrees path

    let targetEnvs ← trees.mapM (fun t => findTargetEnv t parsedSorry)

    let targetEnvs := targetEnvs.flatten'
    -- We might have both term-mode and tactic-mode info trees for the same source-level 'sorry'
    -- (since the 'sorry' tactic will end up emitting a 'sorry' term)
    -- We just pick the first one - as long as they all have the same type (which we check),
    -- shouldn't matter
    let some singleData := targetEnvs[0]? | throw (IO.userError s!"Did not find any targetEnv")
    if !targetEnvs.all (fun d => d.type == singleData.type) then
      throw (IO.userError "Found different types for infotrees corresponding to same sorry")


    let lctx ← match singleData.mctx with
    | .some mctx => do
      let some mvarDecl := mctx.findDecl? singleData.goal.get! | throw (IO.userError "Failed to get mvar decl")
      let lctx := mvarDecl.lctx
      pure lctx
    | none => pure {}
    IO.println s!"Got lxtx: {lctx.lastDecl.map (fun l => l.userName)}"
    -- let some mvarDecl := data.mctx.get!.findDecl? goal
    --   | throwError "unknown goal {goal.name}"
    -- let lctx := mvarDecl.lctx
    -- withLCtx lctx do

    singleData.ctx.runMetaM lctx do
      --setEnv singleData.ctx.env
      let mut elabedExpr := none
      try
        let a ← TermElabM.run (elabStringAsExpr rawExpr singleData)
        elabedExpr := some a.fst
      catch e =>
        return {
          success := false,
          error := some s!"Elaboration error: {(← e.toMessageData.format).pretty}"
        }

      kernelCheck path singleData (serializeExpr elabedExpr.get!) singleData.type fileMap [`sorryAx]
  else
    return {
      success := false,
      error := some "Requires a path, sorry, and expr string"
    }

def main (args : List String) : IO UInt32  := do
  let res ← parseAndCheck args
  IO.println (toJson res)
  return 0
