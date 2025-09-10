inductive MyNat where
  | zero
  | succ (n : MyNat)

def MyNat.add (m n : MyNat) : MyNat :=
  match n with
  | .zero => m
  | .succ n => .succ (add m n)

instance : Add MyNat where
  add := MyNat.add

def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
  | 0 => .zero
  | n + 1 => .succ (ofNat n)

@[default_instance]
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

@[simp, grind =]
theorem MyNat.zero_eq_zero_lit : MyNat.zero = 0 := by
  rfl

@[simp, grind =]
theorem MyNat.succ_eq_add_one (n : MyNat): .succ n = n + 1 := by
  rfl

@[induction_eliminator]
def MyNat.recAux.{u} {motive : MyNat → Sort u}
  (zero : motive 0)
  (succ : (n : MyNat) → motive n → motive (n + 1))
  (t : MyNat) : motive t :=
  match t with
  | .zero => zero
  | .succ n => succ n (MyNat.recAux zero succ n)

@[simp, grind =]
theorem MyNat.add_zero (n : MyNat) : n + 0 = n := rfl

@[simp, grind =]
theorem MyNat.add_succ (m n : MyNat) : m + .succ n = .succ (m + n) := by rfl

@[simp, grind =]
theorem MyNat.add_add_one (m n : MyNat) : m + (n + 1) = (m + n) + 1 := by rfl

@[simp, grind =]
theorem MyNat.zero_add (n : MyNat) : 0 + n = n := by
  induction n with grind

@[simp, grind =]
theorem MyNat.succ_add (m n : MyNat) : .succ m + n = .succ (m + n) := by
  induction n with grind

@[simp, grind =]
theorem MyNat.add_one_add (m n : MyNat) : (m + 1) + n = (m + n) + 1 := by
  induction n with grind

@[grind _=_]
theorem MyNat.add_comm (m n : MyNat) : m + n = n + m := by
  induction n with grind

@[grind _=_]
theorem MyNat.add_assoc (l m n : MyNat) : l + m + n = l + (m + n) := by
  induction n with grind

instance : Std.Associative (α := MyNat) (· + ·) where
  assoc := MyNat.add_assoc

instance : Std.Commutative (α := MyNat) (· + ·) where
  comm := MyNat.add_comm
