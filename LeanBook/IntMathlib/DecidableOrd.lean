import LeanBook.IntMathlib.OrderdAddCommGroup

theorem MyInt.mk_def (x y : MyNat) : ⟦(x, y)⟧ = (x : MyInt) - (y : MyInt) := by
  simp [ofMyNat]

def PreInt.bpos (n : PreInt) : Bool :=
  match n with
  | (n₁, n₂) => decide (n₂ ≤ n₁)

def MyInt.bpos : MyInt → Bool := Quotient.lift PreInt.bpos <| by
  intro (a, b) (c, d) hr
  notation_simp at hr
  dsimp [PreInt.bpos]
  simp_all
  constructor <;> intro h
  case mp =>
    have : a + d ≤ a + c := by calc
      _ = b + c := by rw [hr]
      _ ≤ a + c := by compatible
    simp at this
    assumption
  case mpr =>
    have : b + c ≤ a + c := by calc
      _ = a + d := by rw [← hr]
      _ ≤ a + c := by compatible
    simp at this
    assumption

@[simp]
theorem MyInt.bpos_def (m n : MyNat) : MyInt.bpos ⟦(m, n)⟧ ↔ n ≤ m := by
  dsimp [MyInt.bpos, PreInt.bpos]
  simp

@[norm_cast]
theorem MyInt.ofMyNat_le (m n : MyNat) : (m : MyInt) ≤ (n : MyInt) ↔ m ≤ n := by
  rw [MyNat.le_iff_add]
  notation_simp
  constructor <;> intro ⟨k, hk⟩
  case mp =>
    exists k
    have : ↑(m + k) = (n : MyInt) := by
      norm_cast at hk
    norm_cast at *
  case mpr =>
    exists k
    rw [← hk]
    norm_cast
