import bins.ExtractGoal

/--
info: {"ok": "\ntheorem mytheorem : True := sorry"}
-/
#guard_msgs in
#eval do
  let _ ← main [
    "LeanUtilsTest/LeanFileWithSorries.lean",
    "{\"startPos\":{\"line\":5,\"column\":4},\"parentDecl\":\"test\",\"hash\":\"1590982770643673912\",\"goal\":\"⊢ True\",\"endPos\":{\"line\":5,\"column\":9}}"
  ]
