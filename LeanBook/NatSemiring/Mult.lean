import LeanBook.NatCommMonoid.BetterInduction

def MyNat.mul (m n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => mul m n + m

instance : Mul MyNat where
  mul := MyNat.mul

#eval 2 * 3
#eval 3 * 5

theorem MyNat.mul_add_one (m n : MyNat) : m * (n + 1) = m * n + m := by
  rfl

theorem MyNat.add_one_mul (m n : MyNat) : (m + 1) * n = m * n + n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [MyNat.mul_add_one, ih]
    ac_rfl

@[simp]
theorem MyNat.mul_zero (m : MyNat) : m * 0 = 0 := by
  rfl

@[simp]
theorem MyNat.zero_mul (n : MyNat) : 0 * n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [MyNat.mul_add_one, ih]


@[simp]
theorem MyNat.mul_one (n : MyNat) : n * 1 = n := by calc
  _ = n * (0 + 1) := by rfl
  _ = n * 0 + n := by rfl
  _ = 0 + n := by rfl
  _ = n := by simp

@[simp]
theorem MyNat.one_mul (n : MyNat) : 1 * n = n := by calc
  _ = (0 + 1) * n := by rfl
  _ = 0 * n + n := by rw [MyNat.add_one_mul]
  _ = 0 + n := by simp
  _ = n := by simp

theorem MyNat.mul_comm (m n : MyNat) : m * n = n * m := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp [MyNat.add_one_mul, MyNat.mul_add_one, ih]

theorem MyNat.add_mul (l m n : MyNat) : (l + m) * n = l * n + m * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [MyNat.mul_add_one, ih]
    ac_rfl

theorem MyNat.mul_add (l m n : MyNat) : l * (m + n) = l * m + l * n := by
  rw [MyNat.mul_comm]
  rw [MyNat.add_mul]
  simp [MyNat.mul_comm]

theorem MyNat.mul_assoc (l m n : MyNat) : l * m * n = l * (m * n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [MyNat.mul_add, ih]

instance : Std.Associative (α := MyNat) (· * ·) where
  assoc := MyNat.mul_assoc

instance : Std.Commutative (α := MyNat) (· * ·) where
  comm := MyNat.mul_comm


example (m n : MyNat) : m * n * n * m = m * m * n * n := by
  ac_rfl

example (m n : MyNat) : (m + n) * (m + n) = m * m + 2 * m * n + n * n := by
  rw [show 2 = 1 + 1 from by rfl]
  simp [MyNat.add_mul, MyNat.mul_add]
  ac_rfl
