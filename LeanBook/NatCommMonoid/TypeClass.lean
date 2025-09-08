import LeanBook.FirstProof.NaturalNumber


def MyNat.ofNat (n : Nat) : MyNat :=
  match n with
  | 0 => .zero
  | n + 1 => .succ (ofNat n)

@[default_instance]
instance (n : Nat) : OfNat MyNat n where
  ofNat := MyNat.ofNat n

#check 0
#check 1


instance : Add MyNat where
  add := MyNat.add

#check 1 + 1
#check MyNat.zero + .one

#eval 0 + 0
#eval 1 + 2

def MyNat.toNat (n : MyNat) : Nat :=
  match n with
  | 0 => 0
  | n + 1 => n.toNat + 1

instance : Repr MyNat where
  reprPrec n _ := repr n.toNat

#check 0 + 0
#eval 0 + 0
#eval 1 + 1


example (n : MyNat) : n + 0 = n := by
  rfl
