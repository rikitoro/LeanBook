import LeanBook.NatOrder.NotationSimp
import LeanBook.NatOrder.CompatibleTag

variable {a b m n : MyNat}

theorem MyNat.add_le_add_left (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  rw [le_iff_add] at *
  obtain ⟨k, hk⟩ := h
  exists k
  rw [← hk]
  ac_rfl

theorem MyNat.add_le_add_right (h : m ≤ n) (l : MyNat) : m + l ≤ n + l := by calc
  _ = l + m := by ac_rfl
  _ ≤ l + n := by apply add_le_add_left h
  _ = n + l := by ac_rfl

theorem MyNat.add_le_add (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by calc
  _ ≤ n + a := by apply add_le_add_right h1
  _ ≤ n + b := by apply add_le_add_left h2


example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  apply MyNat.add_le_add_left h

example (hle : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
  apply MyNat.add_le_add_right hle


example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  apply MyNat.add_le_add_left <;> assumption

example (hle : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
  apply MyNat.add_le_add_right <;> assumption

example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
  apply MyNat.add_le_add <;> assumption


syntax "compatible" : tactic

section

local macro_rules
| `(tactic| compatible) =>
  `(tactic| apply MyNat.add_le_add_left <;> assumption)

local macro_rules
| `(tactic| compatible) =>
  `(tactic| apply MyNat.add_le_add_right <;> assumption)

local macro_rules
| `(tactic| compatible) =>
  `(tactic| apply MyNat.add_le_add <;> assumption)

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  compatible

example (hle : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
  compatible

example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
  compatible

end



open Lean Elab Tactic in

elab "compatible" : tactic => do
  let taggedDecls ← labelled `compatible
  if taggedDecls.isEmpty then
    throwError "`[compatible]`が付与された定理はありません。"
  for decl in taggedDecls do
    let declStx := mkIdent decl
    try
      evalTactic <| ← `(tactic| apply $declStx <;> assumption)

      return ()
    catch _ =>
      pure ()
  throwError "ゴールを閉じることができませんでした。"


attribute [compatible] MyNat.add_le_add_left MyNat.add_le_add_right MyNat.add_le_add

example (h : n ≤ m) (l : MyNat) : l + n ≤ l + m := by
  compatible

example (hle : m ≤ n) (l : MyNat) : m + l ≤ n + l := by
  compatible

example (h1 : m ≤ n) (h2 : a ≤ b) : m + a ≤ n + b := by
  compatible

@[compatible]
theorem MyNat.add_lt_add_left {m n : MyNat} (h : m < n) (k : MyNat) : k + m < k + n := by
  notation_simp at *
  calc
    _ = k + (m + 1) := by ac_rfl
    _ ≤ k + n := by compatible

@[compatible]
theorem MyNat.add_lt_add_right {m n : MyNat} (h : m < n) (k : MyNat) : m + k < n + k := by
  calc
    _ = k + m := by ac_rfl
    _ < k + n := by compatible
    _ = n + k := by ac_rfl

section

variable (m n k : MyNat)

theorem MyNat.le_of_add_le_add_left : k + m ≤ k + n → m ≤ n := by
  intro h
  rw [le_iff_add] at *
  obtain ⟨d, hd⟩ := h
  exists d
  have : m + d + k = n + k := by calc
    _ = k + m + d := by ac_rfl
    _ = k + n := by rw [hd]
    _ = n + k := by ac_rfl
  simp_all

theorem MyNat.le_of_add_le_add_right : m + k ≤ n + k → m ≤ n := by
  rw [add_comm m k, add_comm n k]
  apply le_of_add_le_add_left


@[simp]
theorem MyNat.add_le_add_iff_left : k + m ≤ k + n ↔ m ≤ n := by
  constructor
  . apply le_of_add_le_add_left
  . intro h
    compatible

@[simp]
theorem MyNat.add_le_add_iff_right : m + k ≤ n + k ↔ m ≤ n := by
  constructor
  . apply le_of_add_le_add_right
  . intro h
    compatible



end


section
variable (m₁ m₂ n₁ n₂ l₁ l₂ : MyNat)

example (h1 : m₁ ≤ m₂) (h2 : n₁ ≤ n₂) (h3 : l₁ ≤ l₂) :
  l₁ + m₁ + n₁ ≤ l₂ + m₂ + n₂ := by calc
  _ ≤ l₁ + m₁ + n₂ := by compatible
  _ = n₂ + l₁ + m₁ := by ac_rfl
  _ ≤ n₂ + l₁ + m₂ := by compatible
  _ = m₂ + n₂ + l₁ := by ac_rfl
  _ ≤ m₂ + n₂ + l₂ := by compatible
  _ = l₂ + m₂ + n₂ := by ac_rfl

end
