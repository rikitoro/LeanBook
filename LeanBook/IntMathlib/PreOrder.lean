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
