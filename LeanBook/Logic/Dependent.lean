#check Nat.add_zero

#check Nat.add_zero 0
#check Nat.add_zero 42

#check (Nat.add_zero : (n : Nat) → n + 0 = n)

example : (∀ n : Nat, n + 0 = n) = ((n : Nat) → n + 0 = n) := by rfl

#check (∀ n : Nat, n + 0 = n)

set_option pp.foralls false in
#check (∀ n : Nat, n + 0 = n)

example : List Nat := [0, 1, 2, 3]

inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons {n : Nat} (a : α) (v : Vect α n) : Vect α (n + 1)

example : Vect Nat 0 := .nil
example : Vect Nat 1 := .cons 42 .nil
#check Vect.cons 42 .nil


example : (α : Type) × α := ⟨Nat, 1⟩

example : (α : Type) × α := ⟨Bool, true⟩

example : (α : Type) × α := ⟨Prop, True⟩

example : List ((α : Type) × α) := [⟨Nat, 1⟩, ⟨Bool, true⟩, ⟨Prop, True⟩]


example : List ((α : Type) × α) := [⟨Nat, 42⟩, ⟨Bool, false⟩]

example : {α : Type} → {n : Nat} → (a : α) → (v : Vect α n) → Vect α (n + 1) :=
  .cons
