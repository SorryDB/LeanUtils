import Lean

open Lean Meta Elab Term Expr Meta Tactic

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
/-
check that `expr` has type `type`
-/
def kernelCheck (expr type : Expr) (oldDecl : TheoremVal) (bannedNames : List Name) : CoreM (Option String) := do
  if expr.containsConstantNames bannedNames then
    return some "contains banned constant name."
  try
    addDecl (Declaration.thmDecl {oldDecl with value := expr, type := type, name := ← mkFreshId})
    return none
  catch e =>
    return some (← e.toMessageData.toString)
