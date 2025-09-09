section
variable {α β : Type} (sr : Setoid α)
variable (f : β → α)

#check (Quotient.mk sr)


example (a : Quotient sr) : True := by
  induction a using Quotient.inductionOn with
  | h x =>
    guard_hyp x : α
    trivial

#check Quotient.mk sr ∘ f
end

section
variable {α β : Type} (sr : Setoid α)
variable (f : α → β) (h : ∀ x y, x ≈ y → f x = f y)

#check Quotient.lift f h

example : ∀ x, (Quotient.lift f h) (Quotient.mk sr x) = f x := by
  intro x
  rfl
end


section

variable {α : Type} (sr : Setoid α)
variable (x y : α) (h : x ≈ y)

example : Quotient.mk sr x = Quotient.mk sr y := by
  apply Quotient.sound h

#check Quotient.sound

end

section
variable {α : Type} (sr : Setoid α)
variable (x y : α)

example (h : Quotient.mk sr x = Quotient.mk sr y) : x ≈ y := by
  apply Quotient.exact
  apply h

end


private def Rel.comap {α β : Type} (f : α → β) (r : β → β → Prop) :
  α → α → Prop :=
  fun x y => r (f x) (f y)

private def Setoid.comap {α β : Type} (f : α → β) (sr : Setoid β) :
  Setoid α where
  r := Rel.comap f (· ≈ ·)
  iseqv := by
    constructor
    case refl =>
      intro x
      dsimp [Rel.comap]
      apply sr.refl

    case symm =>
      intro x y h
      dsimp [Rel.comap] at *
      apply sr.symm
      exact h

    case trans =>
      intro x y z hxy hyz
      dsimp [Rel.comap] at *
      apply sr.trans hxy
      exact hyz
