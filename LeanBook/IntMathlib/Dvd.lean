import LeanBook.IntMathlib.OrderedRing

example : (2 : MyInt) ∣ 4 := by
  dsimp [(· ∣ ·)]
  exists 2

@[notation_simp]
theorem MyInt.dvd_iff_exists {m n : MyInt} : m ∣n ↔ ∃ k, n = m * k := by
  rfl

def MyInt.IsPrime (n : MyInt) : Prop :=
  n > 1 ∧ ∀ k, 1 < k → k < n → ¬ k ∣ n

theorem MyInt.mul_prev_dvd {m n : MyInt} (a : MyInt) (h : m ∣ n) : a * m∣ a * n := by
  obtain ⟨k, hk⟩ := h
  use k
  rw [hk]
  ring


  example {p a b : MyInt} (hprime : p.IsPrime) : p ∣ a * b → p ∣ a ∨ p ∣ b := by
  dsimp [MyInt.IsPrime] at hprime
  have ⟨h1, h2⟩ := hprime
  intro h
  by_cases hpa : p ∣ a
  . left
    assumption
  . right
    obtain ⟨k, hk⟩ := h
    sorry
