import Lean
import Lake

open Lean Elab Term Meta Syntax Command

structure SorryData (Out : Type) where
  out : Out
  stx : Syntax
  parentDecl : Name
deriving BEq

def printNode (node: Info): String := match node with
  | Info.ofTacticInfo (i : TacticInfo) => "Tactic"
  | Info.ofTermInfo (i : TermInfo) => "Term"
  | Info.ofPartialTermInfo (i : PartialTermInfo) => "PartialTerm"
  | Info.ofCommandInfo (i : CommandInfo) => "Command"
  | Info.ofMacroExpansionInfo (i : MacroExpansionInfo) => "MacroExpansion"
  | Info.ofOptionInfo (i : OptionInfo) => "OptionInfo"
  | Info.ofFieldInfo (i : FieldInfo)=> "FieldInfo"
  | Info.ofCompletionInfo (i : CompletionInfo) => "CompletionInfo"
  | Info.ofUserWidgetInfo (i : UserWidgetInfo) => "UserWidget"
  | Info.ofCustomInfo (i : CustomInfo) => "CustomInfo"
  | Info.ofFVarAliasInfo (i : FVarAliasInfo) => "FVarAlias"
  | Info.ofFieldRedeclInfo (i : FieldRedeclInfo) => "FiledReDecl"
  | Info.ofDelabTermInfo (i : DelabTermInfo) => "DelabTerm"
  | Info.ofChoiceInfo (i : ChoiceInfo) => "ChoiceInfo"

-- #check ContextInfo

def isSorryTactic (stx: Syntax): Bool := match stx with
| `(tactic| sorry)
| `(tactic| admit)  => true
| _ => false

/-- Visit a node in the info tree and apply function `x` if the node
is a tactic info or term info. -/
def visitSorryNode {Out} (ctx : ContextInfo) (node : Info)
    (x : MVarId → MetaM (Option Out)) : IO (Option <| SorryData Out) := do


  IO.println s!"Inspecting {printNode node} with syntax: {node.stx}"

  match node with
  | .ofTacticInfo i =>
    if isSorryTactic i.stx then
      IO.println s!"Got tactic info: {i.stx.prettyPrint}"
      let some mvar := i.goalsBefore[0]? | return none
      let some mctx := (i.mctxBefore.decls.find? mvar) | return none
      match ← ctx.runMetaM mctx.lctx <| x mvar, ctx.parentDecl? with
      | some out, some name => return some ⟨out, i.stx, name⟩
      | _, _ => return none
    else return none
  | .ofTermInfo i =>
    IO.println s!"Got term info: {i.stx.prettyPrint}"
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


/-
Note: we may want to implememt the following functions in Python in order to
only have to run them once per project, rather than once per Lean file.
-/

/-- Get the root directory of a Lean project, given the path to a file in the project. -/
partial def getProjectRootDirPath (path : System.FilePath) : IO (System.FilePath) :=
  go path
where
  go (path : System.FilePath) : IO System.FilePath := do
    if ← path.isDir then
      let contents := (← path.readDir).map IO.FS.DirEntry.fileName
      if contents.contains "lean-toolchain" then
        return path
      else
        let some path := path.parent | throw <| .userError s!"The Lean file {path} does not lie in a Lean project containing a toolchain file."
        go path
    else
      let some path := path.parent | throw <| .userError "The file path provided does not lie in any directory."
      go path

/-- Get the path to all the oleans needed for a given Lean project. -/
partial def getAllLakePaths (path : System.FilePath) : IO (Array System.FilePath) := do
  unless ← path.pathExists do return #[]
  let dirEntries := (← path.readDir).map IO.FS.DirEntry.path
  if dirEntries.contains (path / ".lake") then
    return (← getAllLakePaths <| path / ".lake/packages").push (path / ".lake/build/lib/lean")
  else
    let dirEntries ← dirEntries.filterM fun path ↦ path.isDir
    return (← dirEntries.mapM getAllLakePaths).flatten

/-- Construct the search path for a project.

Note: we could avoid using this if we were using `lake env`. Currently we're not doing so as this would require
running the command in the root directory of the Lean project we're extracting sorries from. -/
def getProjectSearchPath (path : System.FilePath) : IO (System.SearchPath) := do
  let rootDir ← getProjectRootDirPath path
  let paths ← getAllLakePaths rootDir
  let originalSearchPath ← getBuiltinSearchPath (← findSysroot)
  return originalSearchPath.append paths.toList
