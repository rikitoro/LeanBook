import LeanBook.IntMathlib.DecidableOrd

theorem MyInt.nonneg_or_nonneg_neg {a : MyInt} : 0 ≤ a ∨ 0 ≤ -a := by
  induction a using Quotient.inductionOn with
  | h a =>
    obtain ⟨m, n⟩ := a
    have : n ≤ m ∨ m ≤ n := by
      apply MyNat.le_total
    cases this with
    | inl h =>
      left
      simp [mk_def]
      norm_cast
    | inr h =>
      right
      simp [mk_def]
      norm_cast

theorem MyInt.le_total (a b : MyInt) : a ≤ b ∨ b ≤ a := by
  suffices goal : 0 ≤ b - a ∨ 0 ≤ - (b - a) from by
    cases goal with
    | inl h =>
      left
      simp_all
    | inr h =>
      right
      simp_all
  apply nonneg_or_nonneg_neg

instance : LinearOrder MyInt where
  toDecidableLE := by infer_instance
  le_total := MyInt.le_total

theorem MyInt.eq_or_lt_of_le {a b : MyInt} (h : a ≤ b) : a = b ∨ a < b := by
  by_cases hor : a = b
  case pos =>
    left
    assumption
  case neg =>
    right
    order

theorem MyInt.le_of_eq_or_lt {a b : MyInt} (h : a = b ∨ a < b) : a ≤ b := by
  cases h with
  | inl h =>
    rw [h]
  | inr h =>
    order

theorem MyInt.le_iff_eq_or_lt (m n : MyInt) : n ≤ m ↔ n = m ∨ n < m := by
  constructor
  case mp => apply eq_or_lt_of_le
  case mpr => apply le_of_eq_or_lt

example {a b : MyInt} (h : b < a) : ¬ a ≤ b := by
  order

example {a : MyInt} (neg : a ≤ 0) : - a ≥ 0 := by
  notation_simp at *
  obtain ⟨k, hk⟩ := neg
  use k
  simp
  have : ↑k = -a := by calc
    _ = (a + ↑k) - a := by abel
    _ = 0 - a := by rw [hk]
    _ = -a := by simp
  assumption
