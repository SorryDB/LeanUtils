import LeanUtils.ExtractSorry
import Lean.Meta.Basic
import LeanUtils.TargetEnv

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
    let (fileMap, singleData) ← match ← findSorryTargetFromFile path rawSorry with
    | .ok x => pure x
    | .error e => throw (IO.userError e)

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
      error := some "Requires a path, sorry, and expr string"
    }

def main (args : List String) : IO UInt32  := do
  let res ← parseAndCheck args
  IO.println (toJson res)
  return 0
