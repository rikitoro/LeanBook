import LeanBook.IntMathlib.Mul

private def MyInt.const (z : MyInt) : MyInt → MyInt := fun _ => z

#check_failure MyInt.const (0 : MyNat)

def MyInt.ofMyNat (n : MyNat) : MyInt := ⟦(n, 0)⟧

#check MyInt.const (.ofMyNat 0)

instance : Coe MyNat MyInt where
  coe := MyInt.ofMyNat

#check MyInt.const (0 : MyNat)

example : ((0 : MyNat) : MyInt) = (0 : MyInt) := by
  guard_target =ₛ MyInt.ofMyNat 0 = 0
  sorry


attribute [coe] MyInt.ofMyNat

@[simp]
theorem MyInt.ofNat_zero_eq_zero : MyInt.ofMyNat 0 = (0 : MyInt) := by
  dsimp [ofMyNat]
  rfl

example : ((0 : MyNat) : MyInt) = (0 : MyInt) := by
  guard_target =ₛ ↑(0 : MyNat) = (0 : MyInt)
  simp

@[norm_cast]
theorem MyInt.ofMyNat_inj {m n : MyNat} :
  (m : MyInt) = (n : MyInt) ↔ m = n := by
  constructor <;> intro h
  case mp =>
    have : (m, 0) ≈ (n, 0) := by
      apply Quotient.exact h
    notation_simp at this
    simp_all
  case mpr =>
    rw [h]

@[simp]
theorem MyInt.ofMyNat_eq_zero {n : MyNat} : (n : MyInt) = 0 ↔ n = 0 := by
  constructor <;> intro h
  . rw [show (0 : MyInt) = ↑(0 : MyNat) from rfl] at h
    norm_cast at h
  . simp_all

@[push_cast]
theorem MyInt.ofNat_add (m n : MyNat) :
  ↑(m + n) = (m : MyInt) + (n : MyInt) := by
  rfl
