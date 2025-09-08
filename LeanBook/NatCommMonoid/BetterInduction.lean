import LeanBook.NatCommMonoid.AcRfl


example (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    simp [MyNat.ctor_eq_zero]
  | succ n ih =>
    simp [ih]

#check MyNat.rec

def MyNat.recAux.{u} {motive : MyNat → Sort u}
  (zero : motive 0)
  (succ : (n : MyNat) → motive n → motive (n + 1))
  (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n =>
    succ n (recAux zero succ n)

attribute [induction_eliminator] MyNat.recAux

example (m n : MyNat) : m + n = n + m := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    ac_rfl

private def MyNat.pred (n : MyNat) : MyNat :=
  match n with
  | 0 => 0
  | n + 1 => n

example (n : MyNat) : MyNat.pred (MyNat.pred n + 1) = MyNat.pred n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rfl
