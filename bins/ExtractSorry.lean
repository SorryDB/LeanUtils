import Lean
import LeanUtils.Logging
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
  Lean.initSearchPath (← Lean.findSysroot)
  -- TODO(Pau-Lez): This is a hack because I'm lazy: reimplement using the CLI package
  let verbose : Bool ← show IO Bool from do
    match args[1]? with
    | some "--verbose" => do
      return true
    | some _ =>
      IO.eprintln "The second argument should be either the flag --verbose, or nothing."
      return false
    | none =>
      return false
  if let some path := args[0]? then
    if verbose then
      IO.println s!"Running sorry extraction on file {path}."
      IO.println s!"Absolute path to this file is {← IO.FS.realPath ⟨path⟩}"
    unsafe enableInitializersExecution
    let path : System.FilePath := { toString := path }
    let path ← IO.FS.realPath path
    let out := (← parseFile path).map ToJson.toJson
    if verbose then IO.eprintln s!"File extraction yielded"
    IO.eprintln (toJson out)
  else
    IO.println "A path is needed."
