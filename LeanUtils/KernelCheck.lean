import Lean
import LeanUtils.Utils
-- TODO - remove this once we have a real frontend
import LeanUtils.ExtractSorry
import Lean.Meta.Basic

open Lean Meta Elab Term Expr Meta Tactic

-- TODO - decide on a format (something like lean4export)
-- that lets us roundtrip Exprs without running tactics/elab
structure SerializedExpr where
  expr: Expr

def serializeExpr (expr: Expr): SerializedExpr := { expr := expr }
def deserializeExpr (expr: SerializedExpr): Expr := expr.expr

def elabStringAsExpr (code : String) (type : Expr) : TermElabM Expr := do
  -- let a := trace.Elab.debug.set · true
  -- withOptions (trace.Elab.debug.set · true) <| do
  -- parse the string as a syntax tree
  let stx := (Parser.runParserCategory (← getEnv) `term code)
  let stx ← match stx with
  | .ok stx => pure stx
  | .error msg => throwError msg

  -- elaborate it into an expression
  withoutErrToSorry do
    -- Just running 'elabTerm' is not enough, since we may have a 'by' term,
    -- which requires us to run tactics (which is done by elabTermAndSynthesize)
    -- See also: https://github.com/leanprover-community/mathlib4/wiki/Metaprogramming-gotchas#forgetting-to-complete-elaboration-by-synthesizing-pending-synthetic-metavariables
    elabTermAndSynthesize stx (some type)

partial def Lean.Expr.containsConstantNames (e : Expr) (names : List Name) : Bool :=
  let go a := Lean.Expr.containsConstantNames a names
  match e with
  | .const name _ => name ∈ names
  | .app f a        => go f || go a
  | .lam _ ty bd _  => go ty|| go bd
  | .forallE _ ty bd _ => go ty || go bd
  | .letE _ ty val bd _ => go ty || go val || go bd
  | .mdata _ b      => go b
  | .lit _ | .sort _ | .proj _ _ _|  .mvar _ | .fvar _ | .bvar _ => false

inductive KernelCheckResult where
| success
| error (e: String)
deriving Repr


structure TargetEnvData where
  ctx: ContextInfo
  theoremVal: TheoremVal
  type: Expr



def findTargetEnv (tree: InfoTree) (targetSorry: ParsedSorry): IO (List TargetEnvData) := do
  -- TODO - explain why an empty LocalContext is okay. Maybe - local context occurs within TermElabM - we're at top-level decl, so no local context
  let a ←  (do (tree.visitM (m := IO) (postNode := fun ctx i _ as => do
    let head := (as.flatMap Option.toList).flatten
    match i with
    -- TODO - deduplicate this
    | .ofTermInfo ti =>
      if targetSorry.pos == ctx.fileMap.toPosition ti.stx.getPos?.get! && isSorryTerm ti.stx then do
        if let some type := ti.expectedType? then
          return head ++ ([(ctx, some (type), none)])
        else
          return head ++ [(ctx, none, none)]
      else
        return head
    | .ofTacticInfo ti =>
      -- TODO - do we need the 'mctxBefore' stuff from 'visitSorryNode'?
      if targetSorry.pos == ctx.fileMap.toPosition ti.stx.getPos?.get! && isSorryTactic ti.stx then do
        let goal ← if let [goal] := ti.goalsBefore then pure goal else (throw (IO.userError "Found more than one goal"))
        return head ++ ([(ctx, none, some goal)])
      else
        return head
    | _ => return head

  )))

  let matchedCtxs := a.get!
  let targetDatas ← (matchedCtxs.mapM (fun (ctx, type, goal) => do
    ctx.runMetaM {} do
      if let some oldDecl :=  ctx.env.find? targetSorry.parentDecl then
        match oldDecl with
        | .thmInfo info =>
          match (type, goal) with
          | (some type, none) => return [({ctx := ctx, theoremVal := info, type := type} : TargetEnvData)]
          | (none, some goal) =>
              let goalType ← goal.getType
              return [({ctx := ctx, theoremVal := info, type := goalType} : TargetEnvData)]
          | _ => throwError "Bad case"
        | _ => throwError "Bad decl type"
      else
        throwError ("Missing parentDecl in environment")
  ))
  let allTargets := targetDatas.flatten.filter (fun data => data.ctx.parentDecl? == (some targetSorry.parentDecl))
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
    IO.println s!"Got expr: {repr expr}"
    if expr.containsConstantNames bannedNames then
      return {
        success := false,
        error := some "Contains banned constant name"
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



theorem foo: True := True.intro

def parseAndCheck (args : List String): IO KernelCheckOutput := do
  if let [path, rawExpr] := args then
    unsafe enableInitializersExecution
    let path : System.FilePath := { toString := path }
    let path ← IO.FS.realPath path
    let projectSearchPath ← getProjectSearchPath path
    searchPathRef.set projectSearchPath
    let out := (← parseFile path)
    -- TODO - take sorry coordinates on command line, find first one matching
    let [firstSorry] := out | throw (IO.userError "Expected exactly one sorry")

    let (fileMap, trees) ← extractInfoTrees path

    let targetEnvs ← trees.mapM (fun t => findTargetEnv t firstSorry)

    let targetEnvs := targetEnvs.flatten
    -- We might have both term-mode and tactic-mode info trees for the same source-level 'sorry'
    -- (since the 'sorry' tactic will end up emitting a 'sorry' term)
    -- We just pick the first one - as long as they all have the same type (which we check),
    -- shouldn't matter
    let some singleData := targetEnvs[0]? | throw (IO.userError s!"Did not find any targetEnv")
    if !targetEnvs.all (fun d => d.type == singleData.type) then
      throw (IO.userError "Found different types for infotrees corresponding to same sorry")

    singleData.ctx.runMetaM {} do
      let mut elabedExpr := none
      try
        let a ← TermElabM.run (elabStringAsExpr rawExpr singleData.type)
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
      error := some "Requires a path and expr string"
    }

def main (args : List String) : IO UInt32  := do
  let res ← parseAndCheck args
  IO.println (toJson res)
  return 0
