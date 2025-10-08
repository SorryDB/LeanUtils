import Lean
import LeanUtils.Utils

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

/--
  From https://github.com/leanprover-community/repl/blob/593cb8808ece84ce45368eb45eed845732ab04d0/REPL/Lean/InfoTree.lean#L16
  Extract the range of a `Syntax` expressed as lines and columns. -/
-- Extracted from the private declaration `Lean.Elab.formatStxRange`,
-- in `Lean.Elab.InfoTree.Main`.
def stxRange (fileMap : FileMap) (stx : Syntax) : Position × Position :=
  let pos    := stx.getPos?.getD 0
  let endPos := stx.getTailPos?.getD pos
  (fileMap.toPosition pos, fileMap.toPosition endPos)



/-
check that `expr` has type `type`
-/
-- TODO - change the error type to make it harder to accidentally return success
-- remove the 'panics'
def kernelCheck (sorryFilePath: System.FilePath) (expr type : SerializedExpr) (targetSorry: ParsedSorry) (targetSorryFile: System.FilePath) (bannedNames : List Name) : CoreM (Option String) := do
  let expr := deserializeExpr expr
  let type := deserializeExpr type

  if expr.containsConstantNames bannedNames then
      return some "contains banned constant name."

  let (_, trees) ← extractInfoTrees sorryFilePath
  let matchingTrees := trees.filter (fun t => match t with
    | .context ctx t => ((ctx.mergeIntoOuter? none).map (fun p => p.parentDecl? == some (targetSorry.parentDecl))).getD false
    | _ => false
  )

  let tree := if matchingTrees.length == 1 then matchingTrees[0]! else (panic "Expected exactly one one matching tree, found {matchingTrees}")
  let a ← tree.visitM (m := Id) (postNode := fun ctx i cs as => do match i with
    | .ofTermInfo ti => pure ((as.flatMap Option.toList).flatten ++ (if targetSorry.pos == ctx.fileMap.toPosition ti.stx.getPos?.get! then ([ctx]) else []))
    | .ofTacticInfo ti => pure []
    | _ => pure []
  )
  let matchedCtxs := a.get!
  match matchedCtxs with
  | [ctx] =>
      if let some oldDecl :=  ctx.env.find? targetSorry.parentDecl then
        match oldDecl with
        | .thmInfo info =>
          try
            addDecl (Declaration.thmDecl {info with value := expr, type := type, name := ← mkFreshId})
            return none
          catch e =>
            return some (← e.toMessageData.toString)
        | _ =>
          return some "Unexpected constant type"
      else
        panic ("Missing parentDecl in environment")
  | _ => pure (some "Expected exactly one ctx")
