import LeanBook.NatOrder.StrictOrder
import LeanBook.NatOrder.NotationSimpTag

theorem MyNat.lt_def (m n : MyNat) : m < n ↔ m + 1 ≤ n := by rfl

section

attribute [local simp] MyNat.lt_def

example (m n : MyNat) : m < n := by
  simp
  sorry

end

section

open Lean Parser Tactic

syntax "notation_simp" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp only [notation_simp, $args,*] $[at $location]?)

end

attribute [notation_simp] MyNat.lt_def

example (m n : MyNat) : m < n := by
  notation_simp
  sorry

example (m n : MyNat) (h : m < n) : m + 1 ≤ n := by
  notation_simp at *
  assumption

example (m n : MyNat) : m < n := by
  -- simp
  sorry


section

open Lean Parser Tactic

syntax "notation_simp?" (simpArgs)? (location)? : tactic

macro_rules
| `(tactic| notation_simp? $[[$simpArgs,*]]? $[at $location]?) =>
  let args := simpArgs.map (·.getElems) |>.getD #[]
  `(tactic| simp? only [notation_simp, $args,*] $[at $location]?)

end

example (m n : MyNat) : m < n := by
  notation_simp?
  sorry


example (a b : MyNat) (h1 : a < b) (h2 : b < a) : False := by
  notation_simp at *
  have : a + 1 ≤ a := by calc
    _ ≤ b := by apply h1
    _ ≤ b + 1 := by simp
    _ ≤ a := by apply h2
  rw [MyNat.le_iff_add] at this

  obtain ⟨k, hk⟩ := this
  rw [MyNat.add_assoc] at hk
  simp_all?
