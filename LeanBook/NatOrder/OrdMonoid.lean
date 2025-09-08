import LeanBook.NatOrder.NotationSimp

variable {a b m n : MyNat}

theorem MyNat.add_le_add_left (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  rw [le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  exists k
  rw [← hk]
  ac_rfl

theorem MyNat.add_le_add_right (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by calc
  _ = l + m := by ac_rfl
  _ ≤ l + n := by apply add_le_add_left h
  _ = n + l := by ac_rfl

theorem MyNat.add_le_add (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by calc
  _ ≤ n + a := by apply add_le_add_right h1
  _ ≤ n + b := by apply add_le_add_left h2
