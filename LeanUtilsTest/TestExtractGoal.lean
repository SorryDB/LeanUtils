import bins.ExtractGoal

/-! `ExtractGoal <file> <ParsedSorry json> [flags]` restates the goal at one `sorry`
as a standalone theorem, and prints the term that closes the original goal with
it. Only positions, parent declaration, goal and hash are required in the record
(hash as a decimal string). The payload has three parts, separated by markers:
the source prefix up to the enclosing command, the helper theorem, and the
application. -/

-- A tactic `sorry` with one hypothesis in scope.
/--
info: {"ok":
 "import Lean\n\n\n-- sorrydb-helper-start\ntheorem mytheorem (someLemma : True) : 1 + 1 = 2 := sorry\n-- sorrydb-application: mytheorem someLemma"}
---
info: 0
-/
#guard_msgs in
#eval main ["LeanUtilsTest/LeanFileWithSorries.lean",
  "{\"goal\": \"someLemma : True\\n⊢ 1 + 1 = 2\", \"startPos\": {\"line\": 6, \"column\": 2}, \"endPos\": {\"line\": 6, \"column\": 7}, \"parentDecl\": \"test\", \"hash\": \"3234805056349482567\"}"]

-- A term-mode `sorry`: the prefix now contains the whole preceding declaration.
/--
info: {"ok":
 "import Lean\n\ntheorem test : 1 + 1 = 2 := by\n  have someLemma : True := by\n    sorry\n  sorry\n\n\n\n-- sorrydb-helper-start\ntheorem mytheorem : 1 + 1 = 2 := sorry\n-- sorrydb-application: mytheorem"}
---
info: 0
-/
#guard_msgs in
#eval main ["LeanUtilsTest/LeanFileWithSorries.lean",
  "{\"goal\": \"⊢ 1 + 1 = 2\", \"startPos\": {\"line\": 10, \"column\": 2}, \"endPos\": {\"line\": 10, \"column\": 7}, \"parentDecl\": \"test'\", \"hash\": \"11128604812966687648\"}"]

-- One token, two goals: the recorded goal text selects which one is meant.
/--
info: {"ok":
 "import Lean\n\n-- One `sorry` token closes two goals; SorryDB records one entry per goal.\n\n-- sorrydb-helper-start\ntheorem mytheorem : 2 = 2 := sorry\n-- sorrydb-application: mytheorem"}
---
info: 0
-/
#guard_msgs in
#eval main ["LeanUtilsTest/LeanFileWithMultiGoalSorry.lean",
  "{\"goal\": \"⊢ 2 = 2\", \"startPos\": {\"line\": 5, \"column\": 18}, \"endPos\": {\"line\": 5, \"column\": 23}, \"parentDecl\": \"both\", \"hash\": \"0\", \"kind\": \"tactic\"}"]

-- ... and a goal text matching neither is refused, listing the candidates.
/--
info: {"error":
 "Found different types for infotrees corresponding to same sorry; target=3 = 3; candidates=[1 = 1, 2 = 2]"}
---
info: 0
-/
#guard_msgs in
#eval main ["LeanUtilsTest/LeanFileWithMultiGoalSorry.lean",
  "{\"goal\": \"⊢ 3 = 3\", \"startPos\": {\"line\": 5, \"column\": 18}, \"endPos\": {\"line\": 5, \"column\": 23}, \"parentDecl\": \"both\", \"hash\": \"0\", \"kind\": \"tactic\"}"]
