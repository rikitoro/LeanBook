
example (P : Prop) : ¬¬¬ P → ¬ P := by
  intro hn3p hp
  have hn2p : ¬¬ P := by
    intro hnp
    contradiction
  contradiction

example (P : Prop) : ¬¬¬ P → ¬ P := by
  intro hn3p hp
  have : ¬¬ P := by
    intro hnp
    contradiction
  contradiction

example (P : Prop) : ¬¬ (P ∨ ¬ P) := by
  intro h
  suffices hyp : ¬ P from by
    have : P ∨ ¬ P := by
      right
      exact hyp
    contradiction

  intro hp
  have : P ∨ ¬ P := by
    left
    exact hp
  contradiction

example (P : Prop) : (P → True) ↔ True := by
  exact imp_true_iff P

example (P : Prop) : (True → P) ↔ P := by
  exact true_imp_iff


example (P Q : Prop) (h : ¬ P ↔ Q) : (P → False) ↔ Q := by
  rw [show (P → False) ↔ ¬ P from by rfl]
  rw [h]

example (P : Prop) : ¬ (P ↔ ¬ P) := by
  intro h
  have hnp : ¬ P := by
    intro hp
    have : ¬ P := by
      rw [h] at hp
      assumption
    contradiction
  have hp : P := by
    rw [← h] at hnp
    exact hnp
  contradiction
