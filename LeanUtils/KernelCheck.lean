import Lean
import LeanUtils.Utils
-- TODO - remove this once we have a real frontend
import LeanUtils.ExtractSorry

open Lean Meta Elab Term Expr Meta Tactic

-- TODO - decide on a format (something like lean4export)
-- that lets us roundtrip Exprs without running tactics/elab
structure SerializedExpr where
  expr: Expr

def serializeExpr (expr: Expr): SerializedExpr := { expr := expr }
def deserializeExpr (expr: SerializedExpr): Expr := expr.expr

def elabStringAsExpr (code : String) (type : Expr) : TermElabM Expr := do
  -- parse the string as a syntax tree
  let stx := (Parser.runParserCategory (← getEnv) `term code).toOption.get!
  -- elaborate it into an expression
  withoutErrToSorry do
    let expr ← elabTerm stx (some type)
    return expr

partial def Lean.Expr.all (e : Expr) (p : Expr → Bool) : Bool :=
  if !p e then false else
  match e with
  | .app f a        => f.all p && a.all p
  | .lam _ ty bd _  => ty.all p && bd.all p
  | .forallE _ ty bd _ => ty.all p && bd.all p
  | .letE _ ty val bd _ => ty.all p && val.all p && bd.all p
  | .mdata _ b      => b.all p
  | .proj _ _ b     => b.all p
  | _               => true

def Lean.Expr.containsConstantNames (e : Expr) (names : List Name) : Bool :=
  e.all (fun x => match x with
    | .const x _ => x ∈ names
    | _ => true)

#check TheoremVal.mk

#check Expr.dbgToString

inductive KernelCheckResult where
| success
| error (e: String)


structure TargetEnvData where
  ctx: ContextInfo
  theoremVal: TheoremVal
  type: Expr



def findTargetEnv (tree: InfoTree) (targetSorry: ParsedSorry): IO (Option TargetEnvData) := do
  -- TODO - explain why an empty LocalContext is okay. Maybe - local context occurs within TermElabM - we're at top-level decl, so no local context
  let a ←  (do (tree.visitM (m := IO) (postNode := fun ctx i cs as => match i with
    -- TODO - deduplicate this
    | .ofTermInfo ti =>
      let head := (as.flatMap Option.toList).flatten
      if targetSorry.pos == ctx.fileMap.toPosition ti.stx.getPos?.get! then do
        if let some type := ti.expectedType? then
          return head ++ ([(ctx, some (type), none)])
        else
          return head ++ [(ctx, none, none)]
      else
        return head
    | .ofTacticInfo ti =>
      let head := (as.flatMap Option.toList).flatten
      if targetSorry.pos == ctx.fileMap.toPosition ti.stx.getPos?.get! then do
        let goal ← if let [goal] := ti.goalsBefore then pure goal else (throw (IO.userError "Found more than one goal"))
        return head ++ ([(ctx, none, some goal)])
      else
        return head
    | _ => pure []
  )))

  let matchedCtxs := a.get!
  let targetDatas ← (matchedCtxs.mapM (fun (ctx, type, goal) =>
    ctx.runMetaM {} do
      if let some oldDecl :=  ctx.env.find? targetSorry.parentDecl then
        match oldDecl with
        | .thmInfo info =>
          match (type, goal) with
          | (some type, none) => return [({ctx := ctx, theoremVal := info, type := type} : TargetEnvData)]
          | _ => throwError "Bad case"
        | _ =>
          throwError ("Unexpected constant type")
      else
        throwError ("Missing parentDecl in environment")
  ))
  let allTargets := targetDatas.flatten--.filter (fun data => data.ctx.parentDecl? == (some targetSorry.parentDecl))
  let [singleTarget] := allTargets | throw (IO.userError s!"Expected exactly one target, found {allTargets.map (fun d => d.type)}")
  return (some singleTarget)

  -- match matchedCtxs with
  -- | [(ctx, none, none)] => throwError ("Missing expected type for sorry")
  -- | [(ctx, type, goal)] =>
  --     ctx.runMetaM {} do

  -- | [] => none
  -- | _ => throwError ("Expected exactly one ctx")

/-
check that `expr` has type `type`
-/
-- TODO - change the error type to make it harder to accidentally return success
-- remove the 'panics'
def kernelCheck (sorryFilePath: System.FilePath) (targetData: TargetEnvData) (expr : SerializedExpr) (type: Expr) (fileMap: FileMap) (bannedNames : List Name) : IO (KernelCheckResult) := do
  let expr := deserializeExpr expr
  let _ ← Core.CoreM.toIO (ctx := {fileName := sorryFilePath.fileName.get!, fileMap := fileMap}) (s := { env := targetData.ctx.env }) do
    if expr.containsConstantNames bannedNames then
      return (KernelCheckResult.error "contains banned constant name.")
    else
      try
        addDecl (Declaration.thmDecl {targetData.theoremVal with value := expr, type := type, name := ← mkFreshId})
        return (KernelCheckResult.success)
      catch e =>
        return (KernelCheckResult.error (← e.toMessageData.toString))

  return KernelCheckResult.success

def main (args : List String) : IO UInt32  := do
  if let [path, rawExpr] := args then
    IO.println "Running new sorry extraction."
    unsafe enableInitializersExecution
    let path : System.FilePath := { toString := path }
    let path ← IO.FS.realPath path
    let projectSearchPath ← getProjectSearchPath path
    searchPathRef.set projectSearchPath
    let out := (← parseFile path)
    let [firstSorry] := out | throw (IO.userError "Expected exactly one sorry")
    IO.println s!"Found sorry: {firstSorry}"

    let (fileMap, trees) ← extractInfoTrees path

    let targetEnvs ← trees.mapM (fun t => findTargetEnv t firstSorry)

    IO.println s!"Initial tree count: {trees.length}"

    let targetEnv := targetEnvs.flatMap (Option.toList)
    let [singleData] := targetEnv | throw (IO.userError "Bad")

    -- let prettyTrees := trees.filterMap (fun t => match t with
    --   | .context ctx t => match ctx with
    --     | .commandCtx parent => some s!"Command"
    --     | .parentDeclCtx _ => some "Parent"
    --   | _ => none
    -- )

    -- IO.println s!"Got trees {prettyTrees}"

    -- let matchingTrees := trees.filterMap (fun t => match t with
    --   | .context ctx t => if (((ctx.mergeIntoOuter? none).map (fun p => p.parentDecl? == some (firstSorry.parentDecl))).getD false) then (ctx.mergeIntoOuter? none).map (fun ctx => (t, ctx)) else none
    --   | _ => none
    -- )

    --let [(tree, ctxInfo)] := matchingTrees | (throw (IO.userError s!"Expected exactly one one matching tree, found count: {matchingTrees.length}"))
    singleData.ctx.runMetaM {} do
      let (elabedExpr, _) ← TermElabM.run (elabStringAsExpr rawExpr singleData.type)
      IO.println s!"Got elabed expr: {elabedExpr}"
      -- TODO - fix bannedNames
      kernelCheck path singleData (serializeExpr elabedExpr) singleData.type fileMap [`sorry]
  else
    throw (IO.userError "Requires a path and expr string")
  return 0
