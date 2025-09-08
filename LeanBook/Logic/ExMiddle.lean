
example (P : Prop) : ¬¬ P → P := by
  intro hn2p
  by_cases h : P
  . exact h
  . contradiction

example (P Q : Prop) : ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q := by
  constructor
  . intro h
    by_cases hP : P
    . right
      intro hq
      apply h
      constructor <;> assumption
    . left
      assumption
  . intro h
    cases h with
    | inl h =>
      intro hpq
      apply h
      exact hpq.left
    | inr h =>
      intro hpq
      apply h
      exact hpq.right

example (P Q : Prop) : (P → Q) ↔ (¬ Q → ¬ P) := by
  constructor
  . intro hpq hnq hp
    apply hnq
    apply hpq hp
  . intro h hp
    by_cases hq : Q
    . assumption
    . have hnp := h hq
      contradiction
