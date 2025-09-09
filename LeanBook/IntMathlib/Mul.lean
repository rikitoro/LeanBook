import LeanBook.IntMathlib.Add

instance : Zero MyNat where
  zero := 0

instance : AddCommMonoid MyNat where
  zero_add := MyNat.zero_add
  add_zero := MyNat.add_zero
  add_assoc := MyNat.add_assoc
  add_comm := MyNat.add_comm
  nsmul := nsmulRec

instance : One MyNat where
  one := 1

instance : CommSemiring MyNat where
  left_distrib := MyNat.mul_add
  right_distrib := MyNat.add_mul
  zero_mul := MyNat.zero_mul
  mul_zero := MyNat.mul_zero
  mul_one := MyNat.mul_one
  one_mul := MyNat.one_mul
  mul_assoc := MyNat.mul_assoc
  mul_comm := MyNat.mul_comm

example (a b c : MyNat) : (a + b) * (a + c) = a * a + (b + c) * a + b * c := by
  ring
