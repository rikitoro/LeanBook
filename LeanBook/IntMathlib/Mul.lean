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

def PreInt.mul (m n : PreInt) : MyInt :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => ⟦(m₁ * n₁ + m₂ * n₂, m₁ * n₂ + m₂ * n₁)⟧

def MyInt.mul : MyInt → MyInt → MyInt := Quotient.lift₂ PreInt.mul <| by
  intro (a, b) (c, d) (p, q) (r, s) h₁ h₂
  dsimp [PreInt.mul]
  apply Quotient.sound
  notation_simp at *

  generalize hl : a * c + b * d + (p * s + q * r) = lhs
  generalize hr : a * d + b * c + (p * r + q * s) = rhs

  have leml : lhs + q * c = c * b + b * d + d * p + p * r + r * q := by calc
    _ = a * c + b * d + (p * s + q * r) + q * c := by rw [hl]
    _ = (a + q) * c + b * d + p * s + q * r := by ring
    _ = (b + p) * c + b * d + p * s + q * r := by rw [h₁]
    _ = b * c + b * d + q * r + p * (c + s) := by ring
    _ = b * c + b * d + q * r + p * (d + r) := by rw [h₂]
    _ = c * b + b * d + d * p + p * r + r * q := by ring

  have lemr : rhs + q * c = c * b + b * d + d * p + p * r + r * q := by calc
    _ = a * d + b * c + (p * r + q * s) + q * c := by rw [hr]
    _ = a * d + b * c + p * r + q * (c + s) := by ring
    _ = a * d + b * c + p * r + q * (d + r) := by rw [h₂]
    _ = (a + q) * d + b * c + p * r + q * r := by ring
    _ = (b + p) * d + b * c + p * r + q * r := by rw [h₁]
    _ = c * b + b * d + d * p + p * r + r * q := by ring

  have lem : lhs + q * c = rhs + q * c := by rw [leml, lemr]

  simp_all

instance : Mul MyInt where
  mul := MyInt.mul

@[notation_simp]
theorem MyNat.toMyNat_one : MyNat.ofNat 1 = 1 := rfl

@[simp]
theorem MyInt.mul_one (m : MyInt) : m * 1 = m := by
  revert m
  unfold_int₁
  ring

@[simp]
theorem MyInt.one_mul (m : MyInt) : 1 * m = m := by
  revert m
  unfold_int₁
  ring

@[simp]
theorem MyInt.mul_zero (m : MyInt) : m * 0 = 0 := by
  revert m
  unfold_int₁

@[simp]
theorem MyInt.zero_mul (m : MyInt) : 0 * m = 0 := by
  revert m
  unfold_int₁
  ring

theorem MyInt.mul_comm (m n : MyInt) : m * n = n * m := by
  revert m n
  unfold_int₂
  ring

theorem MyInt.mul_assoc (m n k : MyInt) : m * n * k = m * (n * k) := by
  revert m n k
  unfold_int₃
  ring

theorem MyInt.left_distrib (m n k : MyInt) : m * (n + k) = m * n + m * k := by
  revert m n k
  unfold_int₃
  ring

theorem MyInt.right_distrib (m n k : MyInt) : (m + n) * k = m * k + n * k := by
  revert m n k
  unfold_int₃
  ring


instance : CommRing MyInt where
  left_distrib := MyInt.left_distrib
  right_distrib := MyInt.right_distrib
  zero_mul := MyInt.zero_mul
  mul_zero := MyInt.mul_zero
  mul_one := MyInt.mul_one
  one_mul := MyInt.one_mul
  mul_assoc := MyInt.mul_assoc
  mul_comm := MyInt.mul_comm
  zsmul := zsmulRec
  neg_add_cancel := MyInt.neg_add_cancel


example (m n : MyInt) : (m - n) * (m + n) = m * m - n * n := by
  ring

example (m : MyInt) : ∃ s t : MyInt, s * t = m * m * m - 1 := by
  exists m - 1, m * m + m + 1
  ring
