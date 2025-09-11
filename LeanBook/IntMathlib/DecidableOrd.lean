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

theorem MyInt.le_sub_iff (x y z : MyInt) : z ≤ x - y ↔ z + y ≤ x := by
  simp

theorem MyInt.sub_nonneg (m n : MyInt) : 0 ≤ m - n ↔ n ≤ m := by
  simp

theorem MyInt.bpos_iff (z : MyInt) : bpos z ↔ 0 ≤ z := by
  induction z using Quotient.inductionOn with
  | h a =>
    obtain ⟨x, y⟩ := a
    rw [bpos_def, mk_def]
    rw [sub_nonneg]
    norm_cast

instance : DecidablePred (0 ≤ · : MyInt → Prop) := by
  intro n
  apply decidable_of_iff (MyInt.bpos n)
  apply MyInt.bpos_iff

example : 0 ≤ (3 : MyInt) := by
  decide


instance : DecidableLE MyInt := by
  intro n m
  apply decidable_of_iff (0 ≤ m - n)
  apply MyInt.sub_nonneg

#eval (3 : MyInt) ≤ 4

example : (3 : MyInt) ≤ 4 := by
  decide

instance : DecidableLT MyInt := by
  intro n m
  dsimp [(· < ·), MyInt.lt]
  infer_instance

#eval (3 : MyInt) < 4

example : (3 : MyInt) < 4 := by
  decide

instance : DecidableEq MyInt := decidableEqOfDecidableLE

#eval (3 : MyNat) = 4

example : ¬ (3 : MyInt) = 4 := by
  decide

example (a : MyInt) (h : ∃ k : MyNat, a = ↑k) :  0 ≤ a := by
  obtain ⟨k, hk⟩ := h
  notation_simp
  use k
  simp [hk]
