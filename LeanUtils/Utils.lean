import Lean
import Lake

open Lean Elab Term Meta Syntax Command

structure SorryData (Out : Type) where
  out : Out
  stx : Syntax
  parentDecl : Name
deriving BEq

def isSorryTactic (stx: Syntax) : Bool :=
  match stx with
  | `(tactic| sorry)
  | `(tactic| admit) => true
  | _ => false

def isSorryTerm (stx: Syntax) : Bool :=
  match stx with
  | `(term| sorry) => true
  | _ => false

/-- Visit a node in the info tree and apply function `x` if the node
is a tactic info or term info. -/
def visitSorryNode {Out} (ctx : ContextInfo) (node : Info)
    (x : MVarId → MetaM (Option Out)) : IO (Option <| SorryData Out) := do
  match node with
  | .ofTacticInfo i =>
    if isSorryTactic i.stx then
      let some mvar := i.goalsBefore[0]? | return none
      let some mctx := (i.mctxBefore.decls.find? mvar) | return none
      match ← ctx.runMetaM mctx.lctx <| x mvar, ctx.parentDecl? with
      | some out, some name => return some ⟨out, i.stx, name⟩
      | _, _ => return none
    else return none
  | .ofTermInfo i =>
    if isSorryTerm i.stx then TermInfo.runMetaM i ctx do
      let some type := i.expectedType? | return none
      match ← x (← mkFreshExprMVar type).mvarId!, ctx.parentDecl? with
      | some out, some name => return some ⟨out, i.stx, name⟩
      | _, _ => return none
    else return none
  | _ => return none

/-- One `sorry` found in a file.

`startByte`/`endByte` and `kind` are emitted by `ExtractSorry` and consumed by
tools that rewrite the source (a byte range is what a splice needs; `kind`
says whether the token is the `sorry` *tactic* or the `sorry` *term*, which
decides whether a replacement needs a leading `by`).  They are optional on
input so that a record with only line/column positions -- the shape stored in
the SorryDB database -- still deserializes. -/
structure ParsedSorry where
  goal : String
  startPos : Position
  endPos : Position
  parentDecl : Name
  hash : UInt64
  startByte : Option Nat := none
  endByte : Option Nat := none
  /-- `"tactic"` or `"term"`; `none` accepts either. -/
  kind : Option String := none
deriving DecidableEq, FromJson

/-- `true` unless `kind` is set and differs from `k`. -/
def ParsedSorry.acceptsKind (ps : ParsedSorry) (k : String) : Bool :=
  ps.kind.all (· == k)

instance : ToJson ParsedSorry where
  toJson ps :=
    let location := [
        ("start_line", Json.num ps.startPos.line),
        ("start_column", Json.num ps.startPos.column),
        ("end_line", Json.num ps.endPos.line),
        ("end_column", Json.num ps.endPos.column)
      ] ++ (ps.startByte.map fun b => ("start_byte", Json.num b)).toList
        ++ (ps.endByte.map fun b => ("end_byte", Json.num b)).toList
    Json.mkObj <| [
      ("goal", Json.str ps.goal),
      ("location", Json.mkObj location),
      ("parentDecl", Json.str ps.parentDecl.toString),
      ("hash", Json.num ps.hash.toNat)
    ] ++ (ps.kind.map fun k => ("kind", Json.str k)).toList

def SorryData.toParsedSorry {Out} [ToString Out] (fileMap : FileMap) :
    SorryData Out → ParsedSorry :=
  fun ⟨out, stx, parentDecl⟩ =>
    {
      goal := ToString.toString out
      startPos := fileMap.toPosition stx.getPos?.get!
      endPos := fileMap.toPosition stx.getTailPos?.get!
      parentDecl
      hash := Hashable.hash <| ToString.toString out
      startByte := some stx.getPos?.get!.byteIdx
      endByte := some stx.getTailPos?.get!.byteIdx
      kind := some (if isSorryTactic stx then "tactic" else "term")
    }

instance : ToString ParsedSorry where
  toString a := ToString.toString <| ToJson.toJson a

def Lean.Message.printIfError (m : Message) : IO Unit := do
  if m.severity == .error then IO.eprintln <| ← m.toString

def Lean.MessageLog.printErrors (m : MessageLog) : IO Unit := do
  for message in m.reported ++ m.unreported do message.printIfError

/-- `extractInfoTree myLeanFile` takes as input the path to a Lean file and outputs
the infotrees of the file, together with the `FileMap`. -/
def extractInfoTrees (fileName : System.FilePath) : IO (FileMap × List InfoTree) := do
  let input ← IO.FS.readFile fileName
  let inputCtx := Parser.mkInputContext input fileName.toString
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  if Lean.MessageLog.hasErrors messages then
    IO.eprintln s!"Ran into errors while parsing the header of {fileName}"
    MessageLog.printErrors messages
  -- TODO: do we need to specify the main module here?
  let (env, messages) ← processHeader header {} messages inputCtx
  if Lean.MessageLog.hasErrors messages then
    IO.eprintln s!"Ran into errors whist processing the header of {fileName}"
    MessageLog.printErrors messages
  let commandState := Command.mkState env messages
  let frontendState ← IO.processCommands inputCtx parserState commandState
  if Lean.MessageLog.hasErrors frontendState.commandState.messages then
    IO.eprintln s!"Ran into errors whist processing the commands in {fileName}"
    MessageLog.printErrors frontendState.commandState.messages
  let fileMap := FileMap.ofString input
  return (fileMap, frontendState.commandState.infoState.trees.toList)

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
    -- A built package.  Recurse into its own dependencies, and ALSO into any
    -- sub-packages sitting directly inside it: one git dependency can ship
    -- several packages side by side (e.g. `packages/Hammer/HammerCore`), which
    -- lake puts on LEAN_PATH but which this short-circuit would otherwise skip.
    let nested ← getAllLakePaths <| path / ".lake/packages"
    let subPkgs ← dirEntries.filterM fun entry => do
      if entry == path / ".lake" then return false
      if !(← entry.isDir) then return false
      (entry / ".lake").pathExists
    let fromSubPkgs ← subPkgs.mapM getAllLakePaths
    return (nested ++ fromSubPkgs.flatten).push (path / ".lake/build/lib/lean")
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
  -- Honour LEAN_PATH when it is set: `lake env` derives it from the manifest,
  -- which is authoritative for layouts a directory walk cannot infer.
  let envPaths : List System.FilePath ← do
    match ← IO.getEnv "LEAN_PATH" with
    | some raw => pure (System.SearchPath.parse raw)
    | none => pure []
  return originalSearchPath.append (paths.toList ++ envPaths)

def System.FilePath.checkOLeans (path : System.FilePath) : IO Unit := do
  discard <| Lean.findOLean (← moduleNameOfFileName path none)
