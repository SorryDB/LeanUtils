import LeanUtils.ExtractSorry

/--
info: Running sorry extraction.
File extraction yielded
[{"statement": "⊢ True",
  "pos": {"line": 5, "column": 4},
  "parentDecl": "test",
  "hash": "1590982770643673912"},
 {"statement": "someLemma : True\n⊢ 1 + 1 = 2",
  "pos": {"line": 6, "column": 2},
  "parentDecl": "test",
  "hash": "3234805056349482567"},
 {"statement": "⊢ 1 + 1 = 2",
  "pos": {"line": 10, "column": 2},
  "parentDecl": "test'",
  "hash": "11128604812966687648"},
 {"statement": "⊢ 1 + 2 = 3",
  "pos": {"line": 26, "column": 4},
  "parentDecl": "test'''",
  "hash": "13350658948405900884"}]
-/
#guard_msgs in
#eval main ["LeanUtilsTest/LeanFileWithSorries.lean"]
