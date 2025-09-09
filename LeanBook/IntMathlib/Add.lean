import LeanBook.Int.Basic
import Mathlib.Tactic

def PreInt.add (m n : PreInt) : MyInt :=
  match m, n with
  | (m₁, m₂), (n₁, n₂) => ⟦(m₁ + n₁, m₂ + n₂)⟧

def MyInt.add : MyInt → MyInt → MyInt := Quotient.lift₂ PreInt.add <| by
  intro (m₁, m₂) (n₁, n₂) (m'₁, m'₂) (n'₁, n'₂) rm rn
  dsimp [PreInt.add]
  apply Quotient.sound
  notation_simp at *
  have : m₁ + n₁ + (m'₂ + n'₂) = m₂ + n₂ + (m'₁ + n'₁) := by calc
    _ = m₁ + m'₂ + (n₁ + n'₂) := by ac_rfl
    _ = m₂ + m'₁ + (n₂ + n'₁) := by rw [rm, rn]
    _ = m₂ + n₂ + (m'₁ + n'₁) := by ac_rfl
  assumption

instance instAddMyInt : Add MyInt where
  add := MyInt.add

#check (3 + 4 : MyInt)

@[simp]
theorem MyInt.add_def (x₁ x₂ y₁ y₂ : MyNat)
  : ⟦(x₁, x₂)⟧ + ⟦(y₁, y₂)⟧ = (⟦(x₁ + y₁, x₂ + y₂)⟧: MyInt) := by
  dsimp [(· + ·), Add.add, MyInt.add, PreInt.add]

attribute [notation_simp] PreInt.sr PreInt.r

@[notation_simp, simp]
theorem MyNat.ofNat_zero : MyNat.ofNat 0 = 0 := rfl

@[simp]
theorem MyInt.add_zero (m : MyInt) : m + 0 = m := by
  refine Quotient.inductionOn m ?_

  intro (a₁, a₂)
  apply Quotient.sound
  notation_simp
  ac_rfl

@[simp]
theorem MyInt.zero_add (m : MyInt) : 0 + m = m := by
  refine Quotient.inductionOn m ?_
  intro (a₁, a₂)
  apply Quotient.sound
  notation_simp
  ac_rfl

section
local macro "unfold_int₁" : tactic => `(tactic| focus
  refine Quotient.inductionOn m ?_
  intro (a₁, a₂)
  apply Quotient.sound
  notation_simp
)

example (m : MyInt) : m + 0 = m := by
  fail_if_success unfold_int₁
  sorry
end

section
set_option hygiene false

local macro "unfold_int₁" : tactic => `(tactic| focus
  refine Quotient.inductionOn m ?_
  intro (a₁, a₂)
  apply Quotient.sound
  notation_simp
)

example (m : MyInt) : m + 0 = m := by
  unfold_int₁
  ac_rfl
end


macro "unfold_int₁" : tactic => `(tactic| focus
  intro m
  refine Quotient.inductionOn m ?_
  intro (a₁, a₂)
  apply Quotient.sound
  notation_simp
)

example (m : MyInt) : m + 0 = m := by
  revert m
  unfold_int₁
  ac_rfl

macro "unfold_int₂" : tactic => `(tactic| focus
  intro m n
  refine Quotient.inductionOn₂ m n ?_
  intro (a₁, a₂) (b₁, b₂)
  apply Quot.sound
  notation_simp
)

macro "unfold_int₃" : tactic => `(tactic| focus
  intro m n k
  refine Quotient.inductionOn₃ m n k ?_
  intro (a₁, a₂) (b₁, b₂) (c₁, c₂)
  apply Quot.sound
  notation_simp
)

theorem MyInt.add_assoc (m n k : MyInt) : m + n + k = m + (n + k) := by
  revert m n k
  unfold_int₃
  ac_rfl

theorem MyInt.add_comm (m n : MyInt) : m + n = n + m := by
  revert m n
  unfold_int₂
  ac_rfl

instance : Std.Associative (α := MyInt) (· + ·) where
  assoc := MyInt.add_assoc

instance : Std.Commutative (α := MyInt) (· + ·) where
  comm := MyInt.add_comm

def MyInt.sub (m n : MyInt) : MyInt := m + -n

instance : Sub MyInt where
  sub := MyInt.sub

@[simp, notation_simp]
theorem MyInt.sub_def (x y : MyInt) : x - y = x + -y := rfl

theorem MyInt.neg_add_cancel (m : MyInt) : -m + m = 0 := by
  revert m
  unfold_int₁
  ac_rfl

instance : AddCommGroup MyInt where
  add_assoc := MyInt.add_assoc
  add_comm := MyInt.add_comm
  zero_add := MyInt.zero_add
  add_zero := MyInt.add_zero
  neg_add_cancel := MyInt.neg_add_cancel
  nsmul := nsmulRec
  zsmul := zsmulRec


example (a b : MyInt) : (a + b) - b = a := by
  abel

example (a b c : MyInt) : (a - b) - c + b + c = a := by
  abel
