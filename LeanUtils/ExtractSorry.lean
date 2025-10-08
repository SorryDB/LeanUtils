import Lean
import LeanUtils.Utils
import LeanUtils.Backports
-- import Lake

open Lean Elab Term Meta Syntax Command

/-- Pretty print a goal if it doesn't contain any metavariables. -/
def ppGoalIfNoMVar (mvar : MVarId) : MetaM (Option Format) := do
  let e ← instantiateMVars <| ← mvar.getType
  unless !e.hasExprMVar do return none
  try
    return some <| ← ppGoal mvar
  catch _ =>
    return none


/-- Traverses an info tree and applies `x` on the type of each sorry,
while iteratively reconstructing the MetaM context.

Later, we apply this with `T = Option String`, where the output of `x`
is `none` if we cannot infer the type/pretty print the `Expr` corresponding
to a goal, or if the `Expr` contains some metavariables. -/
partial def traverseInfoTree {Out : Type}
    (x : MVarId → MetaM (Option Out)) (T : InfoTree) :
   IO (List <| SorryData Out) :=
  T.collectNodesBottomUpM' go
where
  go (ctx : ContextInfo) (info : Info) (_ : PersistentArray InfoTree) (outs : List <| SorryData Out) :
    IO (List <| SorryData Out) := do
    let currentOuts := outs
    match ← visitSorryNode ctx info x with
    | some out => return currentOuts ++ [out]
    | none => return currentOuts

/-- Extract the sorries in an info tree that don't contain any metavariables. -/
def extractSorries (T : InfoTree) : IO (List <| SorryData Format) :=
  traverseInfoTree ppGoalIfNoMVar T

-- A hack: the sorry extraction method currently seems to return duplicates
-- for some reason.
def List.Dedup {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | cons a l =>  if a ∈ l then l.Dedup else a :: l.Dedup


/-- `parseFile myLeanFile` extracts the sorries contained in the Lean file `myLeanFile`. -/
def parseFile (path : System.FilePath) : IO (List ParsedSorry) := do
  let (fileMap, trees) ← extractInfoTrees path
  -- TODO(Paul-Lez): here ideally we should filter `trees` so we only run
  -- `extractSorries` on infotrees that arise from theorems/lemmas/definitions/...
  let sorryLists  ← trees.mapM extractSorries
  let sorryLists : List ParsedSorry := sorryLists.flatten'.map (SorryData.toParsedSorry fileMap)
  let sorryLists := sorryLists.Dedup
  return sorryLists

-- def main (args : List String) : IO Unit := do
--   if let some path := args[0]? then
--     IO.println "Running sorry extraction."
--     unsafe enableInitializersExecution
--     let path : System.FilePath := { toString := path }
--     let path ← IO.FS.realPath path
--     let projectSearchPath ← getProjectSearchPath path
--     searchPathRef.set projectSearchPath
--     let out := (← parseFile path).map ToJson.toJson
--     IO.eprintln s!"File extraction yielded"
--     IO.eprintln (toJson out)
--   else
--     IO.println "A path is needed."
