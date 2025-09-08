import LeanBook.NatOrder.OrderDef

def MyNat.lt (m n : MyNat) : Prop := (m + 1) ≤ n

instance : LT MyNat where
  lt := MyNat.lt

example (m n : MyNat) : m < n ↔ (m + 1) ≤ n := by
  dsimp [(· < ·), MyNat.lt]
  rfl

@[simp]
theorem MyNat.one_neq_zero : 1 ≠ 0 := by
  intro h
  injection h

@[simp]
theorem MyNat.zero_neq_one : 0 ≠ 1 := by
  intro h
  injection h


@[simp]
theorem MyNat.zero_le (n : MyNat) : 0 ≤ n := by
  rw [MyNat.le_iff_add]
  exists n
  simp

theorem MyNat.zero_of_le_zero {n : MyNat} (h : n ≤ 0) : n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exfalso
    rw [le_iff_add] at h
    obtain ⟨k, hk⟩ := h
    simp_all

@[simp]
theorem MyNat.le_zero {n : MyNat} : n ≤ 0 ↔ n = 0 := by
  constructor <;> intro h
  . apply zero_of_le_zero h
  . simp [h]

theorem MyNat.eq_zero_or_pos (n : MyNat) : n = 0 ∨ 0 < n := by
  induction n with
  | zero => simp
  | succ n ih =>
    dsimp [(· < ·), lt] at *
    cases ih with
    | inl ih =>
      simp_all
    | inr ih =>
      simp_all [le_step]

theorem MyNat.eq_or_lt_of_le {m n : MyNat} : n ≤ m → n = m ∨ n < m := by
  intro h
  dsimp [(· < ·), lt]
  rw [MyNat.le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  induction k with
  | zero =>
    simp_all
  | succ k ih =>
    have : ∃ k, n + 1 + k = m := by
      exists k
      rw [← hk]
      ac_rfl
    simp_all

theorem MyNat.le_of_lt {a b : MyNat} (h : a < b) : a ≤ b := by
  dsimp [(· < · ), lt] at h
  calc
    _ ≤ a + 1 := by simp
    _ ≤ b := by exact h

theorem MyNat.le_of_eq_or_lt {m n : MyNat} : n = m ∨ n < m → n ≤ m := by
  intro h
  cases h with
  | inl h =>
    rw [h]
  | inr h =>
    apply le_of_lt h

theorem MyNat.le_iff_eq_or_lt {m n : MyNat} : n ≤ m ↔ n = m ∨ n < m := by
  constructor
  . apply eq_or_lt_of_le
  . apply le_of_eq_or_lt
