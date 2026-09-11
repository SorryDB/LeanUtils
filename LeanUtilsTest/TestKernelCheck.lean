import bins.KernelCheck

/-! `KernelCheck <file> <ParsedSorry json> <proof term>` checks a candidate term
against the goal of one `sorry`. The record only needs positions, parent
declaration, goal and hash (a decimal string: JSON numbers cannot carry a full
`UInt64`); `kind`/byte offsets are optional (see `ParsedSorry`). -/

def trueSorry : String :=
  "{\"goal\": \"⊢ True\", \"startPos\": {\"line\": 5, \"column\": 4}, \"endPos\": {\"line\": 5, \"column\": 9}, \"parentDecl\": \"test\", \"hash\": \"1590982770643673912\"}"

/--
info: {"success": true, "error": null}
---
info: 0
-/
#guard_msgs in
#eval main ["LeanUtilsTest/LeanFileWithSorries.lean", trueSorry, "trivial"]

-- A term that still relies on `sorryAx` is rejected by name, before the kernel.
/--
info: {"success": false, "error": "Contains banned constant names: [sorryAx]"}
---
info: 0
-/
#guard_msgs in
#eval main ["LeanUtilsTest/LeanFileWithSorries.lean", trueSorry, "sorry"]

-- A term of the wrong type is rejected by the kernel.
/--
info: {"success": false,
 "error":
 "(kernel) declaration type mismatch, '_uniq.1' has type\n  Nat\nbut it is expected to have type\n  True"}
---
info: 0
-/
#guard_msgs in
#eval main ["LeanUtilsTest/LeanFileWithSorries.lean", trueSorry, "(0 : Nat)"]
