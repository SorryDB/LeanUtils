import Lean
import Lake

open Lean Elab Term Meta Syntax Command

structure SorryData (Out : Type) where
  out : Out
  stx : Syntax
  parentDecl : Name
deriving BEq

-- #check ContextInfo

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

structure ParsedSorry where
  statement : String
  pos : Position
  parentDecl : Name
  hash : UInt64
deriving ToJson, DecidableEq

def SorryData.toParsedSorry {Out} [ToString Out] (fileMap : FileMap) : SorryData Out → ParsedSorry :=
  fun ⟨out, stx, parentDecl⟩ =>
    ⟨ToString.toString out, fileMap.toPosition stx.getPos?.get!, parentDecl, Hashable.hash <| ToString.toString out⟩

instance : ToString ParsedSorry where
  toString a := ToString.toString <| ToJson.toJson a


/-- `extractInfoTree myLeanFile` takes as input the path to a Lean file and outputs
the infotrees of the file, together with the `FileMap`. -/
def extractInfoTrees (fileName : System.FilePath) : IO ( FileMap × List InfoTree) := do
  let input ← IO.FS.readFile fileName
  let inputCtx := Parser.mkInputContext input fileName.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  -- TODO: do we need to specify the main module here?
  let (env, messages) ← processHeader header {} messages inputCtx
  let commandState := Command.mkState env messages
  let s ← IO.processCommands inputCtx parserState commandState
  let fileMap := FileMap.ofString input
  return (fileMap, s.commandState.infoState.trees.toList)
