import LeanBook.IntMathlib.PartialOrder

theorem MyInt.add_le_add_left (a b : MyInt) (h : a ≤ b) (c : MyInt) :
  c + a ≤ c + b := by
  notation_simp at *
  obtain ⟨k, hk⟩  := h
  exists k
  rw [← hk]
  ac_rfl

instance : IsOrderedAddMonoid MyInt where
  add_le_add_left := MyInt.add_le_add_left

example {a : MyInt} (nneg : 0 ≤ a) : ∃ k : MyNat, a = ↑k := by
  notation_simp at *
  obtain ⟨k, hk⟩ := nneg
  exists k
  simp_all
