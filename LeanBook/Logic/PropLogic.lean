#check Prop

#check (1 + 1 = 3 : Prop)

#check (fun n => n + 3 = 39 : Nat → Prop)
#check True
#check False

example : True := by trivial

example (P : Prop) (h : P) : P := by
  exact h

example (P : Prop) (h : P) : P := by
  assumption

example (h : False) : ∀ x y z n : Nat,
  n ≥ 3 → x ^ n + y ^ n = z ^ n → x * y * z = 0 := by
  trivial

example (P Q R : Prop) : (P → Q → R) = (P → (Q → R)) := by
  rfl

#eval True → True
#eval True → False
#eval False → True
#eval False → False


example (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  apply h
  exact hp

example (P Q : Prop) (h1 : P → Q) (h2 : Q → P) : P ↔ Q := by
  constructor
  · apply h1
  · apply h2

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor
  case mp =>
    intro h
    exact h hq
  case mpr =>
    intro hp hq
    exact hp

example (P Q : Prop) (hq : Q) : (Q → P) ↔ P := by
  constructor <;> intro h
  · apply h hq
  . intro hq
    exact h

example (P Q : Prop) (h : P ↔ Q) (hq : Q) : P := by
  rw [h]
  exact hq

example (P Q : Prop) (h : P ↔ Q) (hp : P) : Q := by
  rw [←h]
  exact hp

example (P Q : Prop) (h : P ↔ Q) : P = Q := by
  rw [h]


example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  constructor
  · exact hp
  · exact hq

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q := by
  exact ⟨hp, hq⟩

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
  And.intro hp hq

example (P Q : Prop) (h : P ∧ Q) : P := by
  exact h.left

example (P Q : Prop) (h : P ∧ Q) : Q := by
  apply h.right

example (P Q : Prop) (hp : P) : P ∨ Q := by
  left
  exact hp

example (P Q : Prop) (h : P ∨ Q) : Q ∨ P := by
  cases h
  case inl hP =>
    right
    exact hP
  case inr hQ =>
    left
    exact hQ


example (P Q : Prop) : (¬ P ∨ Q) → (P → Q) := by
  intro h hP
  cases h with
  | inl _ => contradiction
  | inr _ => assumption

example (P Q : Prop) : ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q := by
  constructor
  . intro h
    constructor
    . intro hP
      apply h
      left
      assumption
    . intro hQ
      apply h
      right
      assumption
  . intro h hpq
    rcases hpq with hp | hq
    . apply h.left hp
    . apply h.right hq
