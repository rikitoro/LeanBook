import LeanBook.NatOrder.OrdMonoid

variable {n m k : MyNat}

theorem MyNat.lt_trans (h₁ : n < m) (h₂ : m < k) : n < k := by
  notation_simp at *
  calc
    _ ≤ m := by apply h₁
    _ ≤ m + 1 := by simp
    _ ≤ k := by apply h₂

theorem MyNat.lt_of_le_of_lt (h₁ : n ≤ m) (h₂ : m < k) : n < k := by
  notation_simp at *
  have : n + 1 ≤ k := calc
    _ ≤ m + 1 := by compatible
    _ ≤ k := h₂
  assumption

theorem MyNat.lt_of_lt_of_le (h₁ : n < m) (h₂ : m ≤ k) : n < k := by
  notation_simp at *
  have : n + 1 ≤ k := by calc
    _ ≤ m := by exact h₁
    _ ≤ k := by exact h₂
  assumption

instance : Trans (· < · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_trans

instance : Trans (· ≤ · : MyNat → MyNat → Prop) (· < ·) (· < ·) where
  trans := MyNat.lt_of_le_of_lt

instance : Trans (· < · : MyNat → MyNat → Prop) (· ≤ ·) (· < ·) where
  trans := MyNat.lt_of_lt_of_le


@[simp]
theorem MyNat.lt_irrefl (n : MyNat) : ¬ n < n := by
  intro h
  notation_simp at h
  rw [le_iff_add] at h
  obtain ⟨k, hk⟩ := h
  rw [add_assoc] at hk
  simp_all

theorem MyNat.le_antisymm (h₁ : n ≤ m) (h₂ : m ≤ n) : n = m := by
  induction h₁ with
  | refl =>
    rfl
  | @step m h ih =>
    have : n < n := by calc
      _ ≤ m := by exact h
      _ < m + 1 := by notation_simp; rfl
      _ ≤ n := by exact h₂
    simp_all

example (a b : MyNat) : a < b ∨ a = b → a ≤ b := by
  intro h
  cases h with
  | inl h =>
    notation_simp at h
    calc
      _ ≤ a + 1 := by simp_all
      _ ≤ b := by assumption
  | inr h =>
    rw [h]
