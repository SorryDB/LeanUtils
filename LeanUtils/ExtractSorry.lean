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

/-- One record per source token.

A `sorry` *tactic* elaborates to a `sorry` *term*, so the info trees carry two
nodes for the same token with the same goal.  They differ only in `kind`, which
would otherwise defeat the plain deduplication; merge them and keep the
`"tactic"` record, since that is the position the token occupies in the source
(a replacement there needs no leading `by`). -/
def dedupByToken (sorries : List ParsedSorry) : List ParsedSorry :=
  sorries.foldl (init := []) fun acc ps =>
    let sameToken (q : ParsedSorry) :=
      q.startPos == ps.startPos && q.endPos == ps.endPos &&
        q.parentDecl == ps.parentDecl && q.goal == ps.goal
    match acc.find? sameToken with
    | none => acc ++ [ps]
    | some q =>
      if q.kind != some "tactic" && ps.kind == some "tactic" then
        acc.map fun r => if sameToken r then ps else r
      else acc

/-- `parseFile myLeanFile` extracts the sorries contained in the Lean file `myLeanFile`. -/
def parseFile (path : System.FilePath) : IO (List ParsedSorry) := do
  unsafe enableInitializersExecution
  let projectSearchPath ← getProjectSearchPath path
  searchPathRef.set projectSearchPath
  -- Throw an error if the oleans of the file can't be found...
  path.checkOLeans
  let (fileMap, trees) ← extractInfoTrees path
  -- TODO(Paul-Lez): here ideally we should filter `trees` so we only run
  -- `extractSorries` on infotrees that arise from theorems/lemmas/definitions/...
  let sorryLists  ← trees.mapM extractSorries
  let sorryLists : List ParsedSorry := sorryLists.flatten'.map (SorryData.toParsedSorry fileMap)
  return dedupByToken sorryLists
