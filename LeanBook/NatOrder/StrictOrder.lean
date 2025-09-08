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

theorem MyNat.lt_or_ge (a b : MyNat) : a < b ∨ b ≤ a := by
  dsimp [(· < ·), lt]
  induction a with
  | zero =>
    simp
    have : b = 0 ∨ 0 < b := by apply MyNat.eq_zero_or_pos
    dsimp [(· < ·), lt] at this
    simp_all
    cases this with
    | inl h =>
      right
      assumption
    | inr h =>
      left
      assumption
  | succ a ih =>
    cases ih with
    | inl h =>
      simp [le_iff_eq_or_lt] at h
      cases h with
      | inl h =>
        right
        simp_all
      | inr h =>
        dsimp [(· < ·), lt] at h
        left
        assumption
    | inr h =>
      right
      apply le_step h

#check MyNat.eq_zero_or_pos


theorem MyNat.lt_of_not_le {a b : MyNat} (h : ¬ a ≤ b) : b < a := by
  cases lt_or_ge b a with
  | inl h => assumption
  | inr h => contradiction

theorem MyNat.not_le_of_lt {a b : MyNat} (h : a < b) : ¬ b ≤ a := by
  intro hle
  dsimp [(· < ·), lt] at h
  rw [le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  obtain ⟨l, hl⟩ := hle
  have : a + (k + l + 1) = a := by calc
    _ = a + 1 + k + l := by ac_rfl
    _ = b + l := by rw [hk]
    _ = a := by rw [hl]
  simp at this

theorem MyNat.lt_iff_le_not_le (a b : MyNat) : a < b ↔ a ≤ b ∧ ¬ b ≤ a := by
  constructor <;> intro h
  . simp_all [not_le_of_lt, le_of_lt]
  . simp_all [lt_of_not_le]

theorem MyNat.le_total (a b : MyNat) : a ≤ b ∨ b ≤ a := by
  cases lt_or_ge a b <;> simp_all [le_of_lt]


example (a : MyNat) : a ≠ a + 1 := by
  simp_all only [ne_eq, MyNat.self_eq_add_right, MyNat.one_neq_zero, not_false_eq_true]

example (n : MyNat) : ¬ n + 1 ≤ n := by
  intro h
  rw [MyNat.le_iff_add] at h
  obtain ⟨k, hk⟩ := h
  rw [MyNat.add_assoc] at hk
  simp_all only [MyNat.add_right_eq_self, MyNat.add_eq_zero_iff_eq_zero, MyNat.one_neq_zero,
    false_and]
