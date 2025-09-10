import LeanBook.IntMathlib.PreOrder

@[simp↓]
theorem MyInt.add_right_eq_self {a b : MyInt} : a + b = a ↔ b = 0 := by
  constructor <;> intro h
  case mp =>
    rw [show b = a + b - a from by ring]
    rw [h]
    ring
  case mpr =>
    simp [h]

theorem MyInt.le_antisymm (a b : MyInt) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  notation_simp at *
  obtain ⟨m, hm⟩ := h1
  obtain ⟨n, hn⟩ := h2
  rw [← hn, add_assoc] at hm
  replace hm : ↑(n + m) = (0 : MyInt) := by
    push_cast
    simp_all
  have ⟨hnz, hmz⟩ : n = 0 ∧ m = 0 := by
    simp_all
  simp_all

instance : PartialOrder MyInt where
  le_antisymm := by apply MyInt.le_antisymm

example (a b : MyInt) (h1 : a ≤ b) (h2 : b ≤ a) : a = b := by
  order


example {a b : MyInt} (h : a = b ∨ a < b) : a ≤ b := by
  cases h with order
