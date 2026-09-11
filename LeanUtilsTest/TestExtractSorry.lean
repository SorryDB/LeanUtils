import bins.ExtractSorry

/--
info: [{"parentDecl": "test",
  "location":
  {"start_line": 5,
   "start_column": 4,
   "start_byte": 78,
   "end_line": 5,
   "end_column": 9,
   "end_byte": 83},
  "kind": "tactic",
  "hash": 1590982770643673912,
  "goal": "⊢ True"},
 {"parentDecl": "test",
  "location":
  {"start_line": 6,
   "start_column": 2,
   "start_byte": 86,
   "end_line": 6,
   "end_column": 7,
   "end_byte": 91},
  "kind": "tactic",
  "hash": 3234805056349482567,
  "goal": "someLemma : True\n⊢ 1 + 1 = 2"},
 {"parentDecl": "test'",
  "location":
  {"start_line": 10,
   "start_column": 2,
   "start_byte": 125,
   "end_line": 10,
   "end_column": 7,
   "end_byte": 130},
  "kind": "term",
  "hash": 11128604812966687648,
  "goal": "⊢ 1 + 1 = 2"},
 {"parentDecl": "test'''",
  "location":
  {"start_line": 26,
   "start_column": 4,
   "start_byte": 446,
   "end_line": 26,
   "end_column": 9,
   "end_byte": 451},
  "kind": "tactic",
  "hash": 13350658948405900884,
  "goal": "⊢ 1 + 2 = 3"}]
-/
#guard_msgs in
#eval main ["LeanUtilsTest/LeanFileWithSorries.lean"]
