import LeanBook.IntMathlib.LinearOrder

variable {a b c : MyInt}

theorem MyInt.le.dest (h : a < b) : ∃ k : MyNat, a + (↑k + 1) = b := by
  notation_simp at *
  obtain ⟨⟨k, hk⟩, h⟩ := h
  induction k with
  | zero =>
    exfalso
    apply h
    use 0
    simp_all
  | succ k ih =>
    push_cast at hk
    use k
    assumption


theorem MyInt.le.intro (a : MyInt) (b : MyNat) : a ≤ a + ↑b := by
  use b

theorem MyInt.lt.intro (h : ∃ k : MyNat, a + (k + 1) = b) : a < b := by
  obtain ⟨k, hk⟩ := h
  simp only [lt_def]
  constructor
  case left =>
    notation_simp
    use k + 1
    assumption
  case right =>
    notation_simp
    intro ⟨s, hs⟩
    rw [← hs] at hk
    have : ↑(s + k) + (1 : MyInt) = 0 := by calc
      _ = (↑s + ↑k) + (1 : MyInt) := by push_cast; rfl
      _ = b + ↑s + (↑k + 1) - b := by abel
      _ = b - b := by rw [hk]
      _ = 0 := by abel
    replace : (0 : MyInt) > 0 := by calc
      _ = ↑(s + k) + (1 : MyInt) := by rw [this]
      _ = (1 : MyInt) + ↑(s + k) := by ac_rfl
      _ ≥ (1 : MyInt)  := by apply le.intro
      _ > (0 : MyInt) := by decide
    order


theorem MyInt.lt_iff_add : a < b ↔ ∃ k : MyNat, a + (k + 1) = b := by
  constructor
  case mp => apply le.dest
  case mpr => apply lt.intro


@[push_cast]
theorem MyInt.ofMyNat_mul (m n : MyNat) :
  ↑(m * n) = (m : MyInt) * ↑n := by
  dsimp [MyInt.ofMyNat]
  apply Quotient.sound
  notation_simp
  ring

theorem MyInt.mul_pos (ha : 0 < a) (hb : 0 < b) : 0 < a * b := by
  rw [MyInt.lt_iff_add] at *
  obtain ⟨c, hc⟩ := ha
  obtain ⟨d, hd⟩ := hb
  simp at *
  rw [← hc, ← hd]
  use c *d + c + d
  push_cast
  ring


theorem MyInt.sub_pos : 0 < a - b ↔ b < a := by
  constructor <;> intro h
  case mp =>
    rw [lt_iff_add] at *
    simp at *
    obtain ⟨k, hk⟩ := h
    use k
    rw [hk]
    abel
  case mpr =>
    rw [lt_iff_add] at *
    simp at *
    obtain ⟨k, hk⟩ := h
    use k
    rw [← hk]
    abel

theorem MyInt.mul_lt_mul_of_pos_left (h : a < b) (pos : 0 < c) :
  c * a < c * b := by
  suffices 0 < c * (b - a) from by
    rw [lt_iff_add] at this ⊢
    obtain ⟨k, hk⟩ := this
    simp at *
    use k
    rw [hk]
    simp [left_distrib]
  replace h : 0 < b - a := by
    rw [sub_pos]
    assumption
  apply mul_pos
  . assumption
  . assumption

theorem MyInt.mul_lt_mul_of_pos_right (h : a < b) (pos : 0 < c) :
  a * c < b * c := by
  rw [mul_comm a, mul_comm b]
  apply mul_lt_mul_of_pos_left
  . assumption
  . assumption

instance : IsStrictOrderedRing MyInt where
  zero_le_one := by decide
  exists_pair_ne := by exists 0, 1
  mul_lt_mul_of_pos_left := by apply MyInt.mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := by apply MyInt.mul_lt_mul_of_pos_right


example (a b c : MyInt) (h : a < b) : a + c < b + c := by
  linarith

example (a b : MyInt) (h1 : 2 * a - b = 1) (h2 : a + b = 5) : a = 2 := by
  linarith


theorem MyInt.mul_le_mul_of_nonneg_left (h : a ≤ b) (nneg : 0 ≤ c) :
  c * a ≤ c * b := by
  nlinarith

theorem MyInt.mul_le_mul_of_nonneg_right (h : a ≤ b) (nneg : 0 ≤ c) :
  a * c ≤ b * c := by
  nlinarith


instance : IsOrderedRing MyInt where
  zero_le_one := by decide
  mul_le_mul_of_nonneg_left := by apply MyInt.mul_le_mul_of_nonneg_left
  mul_le_mul_of_nonneg_right := by apply MyInt.mul_le_mul_of_nonneg_right


example (a b : MyInt) (h1 : 3 * a - 2 * b = 5) (h2 : 6 * a - 5 * b = 11) : b = -1 := by
  linarith
