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


def findTargetEnv (trees: List (InfoTree)) (targetSorry: ParsedSorry) : IO (Environment × TheoremVal) := do
  let matchingTrees := trees.filter (fun t => match t with
    | .context ctx t => ((ctx.mergeIntoOuter? none).map (fun p => p.parentDecl? == some (targetSorry.parentDecl))).getD false
    | _ => false
  )

  let tree := if matchingTrees.length == 1 then matchingTrees[0]! else (panic "Expected exactly one one matching tree, found {matchingTrees}")
  let a ← tree.visitM (m := Id) (postNode := fun ctx i cs as => do match i with
    -- TODO - deduplicate this
    | .ofTermInfo ti => pure ((as.flatMap Option.toList).flatten ++ (if targetSorry.pos == ctx.fileMap.toPosition ti.stx.getPos?.get! then ([ctx]) else []))
    | .ofTacticInfo ti =>  pure ((as.flatMap Option.toList).flatten ++ (if targetSorry.pos == ctx.fileMap.toPosition ti.stx.getPos?.get! then ([ctx]) else []))
    | _ => pure []
  )


  let matchedCtxs := a.get!
  match matchedCtxs with
  | [ctx] =>
      if let some oldDecl :=  ctx.env.find? targetSorry.parentDecl then
        match oldDecl with
        | .thmInfo info =>
          pure (ctx.env, info)
        | _ =>
          throw (IO.userError "Unexpected constant type")
      else
        throw (IO.userError "Misisng parentDecl in environment")
  | _ => throw (IO.userError "Expected exactly one ctx")

/-
check that `expr` has type `type`
-/
-- TODO - change the error type to make it harder to accidentally return success
-- remove the 'panics'
def kernelCheck (sorryFilePath: System.FilePath) (expr type : SerializedExpr) (targetSorry: ParsedSorry) (bannedNames : List Name) : IO (KernelCheckResult) := do
  let expr := deserializeExpr expr
  let type := deserializeExpr type
  let (fileMap, trees) ← extractInfoTrees sorryFilePath
  let (newEnv, val) ← findTargetEnv trees targetSorry
  let _ ← Core.CoreM.toIO (ctx := {fileName := sorryFilePath.fileName.get!, fileMap := fileMap}) (s := { env := newEnv }) do
    if expr.containsConstantNames bannedNames then
      return (KernelCheckResult.error "contains banned constant name.")
    else
      try
        addDecl (Declaration.thmDecl {val with value := expr, type := type, name := ← mkFreshId})
        return (KernelCheckResult.success)
      catch e =>
        return (KernelCheckResult.error (← e.toMessageData.toString))

  return KernelCheckResult.success

def main (args : List String) : IO UInt32  := do
  if let some path := args[0]? then
    IO.println "Running sorry extraction."
    unsafe enableInitializersExecution
    let path : System.FilePath := { toString := path }
    let path ← IO.FS.realPath path
    let projectSearchPath ← getProjectSearchPath path
    searchPathRef.set projectSearchPath
    let out := (← parseFile path).map ToJson.toJson

    IO.println s!"Got sorries: {out}"

    IO.eprintln s!"File extraction yielded"
    IO.eprintln (toJson out)
  else
    IO.println "A path is needed."

  return 0
