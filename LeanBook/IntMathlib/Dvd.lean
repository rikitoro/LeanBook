import LeanBook.IntMathlib.OrderedRing

example : (2 : MyInt) ∣ 4 := by
  dsimp [(· ∣ ·)]
  exists 2

@[notation_simp]
theorem MyInt.dvd_iff_exists {m n : MyInt} : m ∣n ↔ ∃ k, n = m * k := by
  rfl

def MyInt.IsPrime (n : MyInt) : Prop :=
  n > 1 ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n

example {p a b : MyInt} (hprime : p.IsPrime) : p ∣ a * b → p ∣ a ∨ p ∣ b := by
  dsimp [MyInt.IsPrime] at hprime
  have ⟨h1, h2⟩ := hprime
  sorry
