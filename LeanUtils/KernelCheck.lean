import Lean
import LeanUtils.Utils
-- TODO - remove this once we have a real frontend
import LeanUtils.ExtractSorry

open Lean Meta Elab Term Expr Meta Tactic

-- TODO - decide on a format (something like lean4export)
-- that lets us roundtrip Exprs without running tactics/elab
structure SerializedExpr where
  expr: Expr

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
  env: Environment
  theoremVal: TheoremVal
  type: Expr

def findTargetEnv (trees: List (InfoTree)) (targetSorry: ParsedSorry) : IO TargetEnvData := do
  let matchingTrees := trees.filterMap (fun t => match t with
    | .context ctx t => if (((ctx.mergeIntoOuter? none).map (fun p => p.parentDecl? == some (targetSorry.parentDecl))).getD false) then (ctx.mergeIntoOuter? none).map (fun ctx => (t, ctx)) else none
    | _ => none
  )

  let [(tree, ctxInfo)] := matchingTrees | (throw (IO.userError "Expected exactly one one matching tree, found {matchingTrees}"))
  -- TODO - explain why an empty LocalContext is okay. Maybe - local context occurs within TermElabM - we're at top-level decl, so no local context
  let a ← ctxInfo.runMetaM {} (do (tree.visitM (m := MetaM) (postNode := fun ctx i cs as => match i with
    -- TODO - deduplicate this
    | .ofTermInfo ti => do pure ((as.flatMap Option.toList).flatten ++ (if targetSorry.pos == ctx.fileMap.toPosition ti.stx.getPos?.get! then ([(ctx, ti.expectedType?)]) else []))
    | .ofTacticInfo ti =>
      let head := (as.flatMap Option.toList).flatten
      if targetSorry.pos == ctx.fileMap.toPosition ti.stx.getPos?.get! then do
        let type ← if let [goal] := ti.goalsBefore then goal.getType else (throwError ("Found more than one goal"))
        return head ++ ([(ctx, some type)])
      else
        return head
    | _ => pure []
  )))

  let matchedCtxs := a.get!
  match matchedCtxs with
  | [(ctx, some type)] =>
      if let some oldDecl :=  ctx.env.find? targetSorry.parentDecl then
        match oldDecl with
        | .thmInfo info =>
          pure {env := ctx.env, theoremVal := info, type := type}
        | _ =>
          throw (IO.userError "Unexpected constant type")
      else
        throw (IO.userError "Misisng parentDecl in environment")
  | [(ctx, none)] => throw (IO.userError "Missing expected type for sorry")
  | _ => throw (IO.userError "Expected exactly one ctx")

/-
check that `expr` has type `type`
-/
-- TODO - change the error type to make it harder to accidentally return success
-- remove the 'panics'
def kernelCheck (sorryFilePath: System.FilePath) (expr : SerializedExpr) (type: Expr) (targetSorry: ParsedSorry) (bannedNames : List Name) : IO (KernelCheckResult) := do
  let expr := deserializeExpr expr
  let (fileMap, trees) ← extractInfoTrees sorryFilePath
  let targetData ← findTargetEnv trees targetSorry
  let _ ← Core.CoreM.toIO (ctx := {fileName := sorryFilePath.fileName.get!, fileMap := fileMap}) (s := { env := targetData.env }) do
    if expr.containsConstantNames bannedNames then
      return (KernelCheckResult.error "contains banned constant name.")
    else
      try
        addDecl (Declaration.thmDecl {sdjfsdf.theoremVal with value := expr, type := type, name := ← mkFreshId})
        return (KernelCheckResult.success)
      catch e =>
        return (KernelCheckResult.error (← e.toMessageData.toString))

  return KernelCheckResult.success

def fakeMain (args : List String) : IO UInt32  := do
  if let [path, rawExpr] := args then
    IO.println "Running sorry extraction."
    unsafe enableInitializersExecution
    let path : System.FilePath := { toString := path }
    let path ← IO.FS.realPath path
    let projectSearchPath ← getProjectSearchPath path
    searchPathRef.set projectSearchPath
    let out := (← parseFile path)
    let firstSorry := out[0]?

    -- do term elab
    let expr: Expr := elabStringAsExpr rawExpr

    IO.println s!"Got sorries: {out}"
    kernelCheck path expr
  else
    IO.println "A path is needed."

  return 0
