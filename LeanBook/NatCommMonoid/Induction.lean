import LeanBook.NatCommMonoid.TypeClass


#reduce fun (n : MyNat) => n + 0
#reduce fun (n : MyNat) => 0 + n

set_option pp.fieldNotation.generalized false in

example (n : MyNat) : 0 + n = n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    sorry

theorem MyNat.add_zero (n : MyNat) : n + 0 = n := by rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [MyNat.add_zero]

theorem MyNat.add_zero_rev (n : MyNat) : n = n + 0 := by rfl

example (m n : MyNat) : (n + 0) + m = n + m := by
  rw [← MyNat.add_zero_rev]

theorem MyNat.add_succ (m n : MyNat) : m + .succ n = .succ (m + n) := by
  rfl

theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [MyNat.add_succ]
    rw [ih]

example (n : MyNat) : 1 + n = .succ n := by
  induction n with
  | zero =>
    rfl
  | succ n ih =>
    rw [MyNat.add_succ, ih]
