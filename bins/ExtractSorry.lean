import Lean
import LeanUtils.Utils
import LeanUtils.Backports
import LeanUtils.ExtractSorry
-- import Lake

open Lean Elab Term Meta Syntax Command

/-
Note: we may want to implememt the following functions in Python in order to
only have to run them once per project, rather than once per Lean file.
-/

def main (args : List String) : IO Unit := do
  if let some path := args[0]? then
    IO.println "Running sorry extraction."
    unsafe enableInitializersExecution
    let path : System.FilePath := { toString := path }
    let path ← IO.FS.realPath path
    searchPathRef.set compile_time_search_path%
    let out := (← parseFile path).map ToJson.toJson
    IO.eprintln s!"File extraction yielded"
    IO.eprintln (toJson out)
  else
    IO.println "A path is needed."
