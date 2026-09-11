import Lean

-- One `sorry` token closes two goals; SorryDB records one entry per goal.
theorem both : (1 : Nat) = 1 ∧ (2 : Nat) = 2 := by
  constructor <;> sorry
