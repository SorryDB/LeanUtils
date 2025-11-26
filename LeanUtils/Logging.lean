import Lean

def logRun : IO Unit := do
  IO.println s!"Running {Lean.versionString}."
  IO.println s!"Current directory is {← IO.currentDir}."
  IO.println s!"Current search path is {← Lean.searchPathRef.get}."
