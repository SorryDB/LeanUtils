import Lean
import Lake

open Lean Elab Term Meta Syntax Command

structure SorryData (Out : Type) where
  out : Out
  stx : Syntax
  parentDecl : Name
deriving BEq

/-- Visit a node in the info tree and apply function `x` if the node
is a tactic info or term info. -/
def visitSorryNode {Out} (ctx : ContextInfo) (node : Info)
    (x : MVarId → MetaM (Option Out)) : IO (Option <| SorryData Out) := do
  match node with
  | .ofTacticInfo i =>
    match i.stx with
    | `(tactic| sorry)
    | `(tactic| admit) =>
      let some mvar := i.goalsBefore[0]? | return none
      let some mctx := (i.mctxBefore.decls.find? mvar) | return none
      match ← ctx.runMetaM mctx.lctx <| x mvar, ctx.parentDecl? with
      | some out, some name => return some ⟨out, i.stx, name⟩
      | _, _ => return none
    | _ => return none
  | .ofTermInfo i =>
    match i.stx with
    | `(term| sorry) => TermInfo.runMetaM i ctx do
      let some type := i.expectedType? | return none
      match ← x (← mkFreshExprMVar type).mvarId!, ctx.parentDecl? with
      | some out, some name => return some ⟨out, i.stx, name⟩
      | _, _ => return none
    | _ => return none
  | _ => return none
