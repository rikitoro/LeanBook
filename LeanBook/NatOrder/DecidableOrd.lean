import LeanBook.NatOrder.PartialOrder

example : 0 ≤ 1 := by
  apply MyNat.le.step
  apply MyNat.le.refl

example : 0 ≤ 3 := by
  apply MyNat.le.step
  apply MyNat.le.step
  apply MyNat.le.step
  apply MyNat.le.refl

deriving instance DecidableEq for MyNat

example : 32 + 13 ≠ 46 := by
  decide

#eval 1 ≠ 2

def MyNat.ble (a b : MyNat) : Bool :=
  match a, b with
  | 0, _ => true
  | _ + 1, 0 => false
  | a + 1, b + 1 => ble a b

#eval MyNat.ble 0 1
#eval MyNat.ble 4 3
#eval MyNat.ble 3 12


@[simp]
theorem MyNat.ble_zero_left (n : MyNat) : ble 0 n = true := by
  rfl

@[simp]
theorem MyNat.ble_zero_right (n : MyNat) : ble (n + 1) 0 = false := by
  rfl

@[simp]
theorem MyNat.ble_succ (m n : MyNat) : ble (m + 1) (n + 1) = ble m n := by
  rfl




instance (a b : MyNat) : Decidable (a ≤ b) := by
  apply decidable_of_iff (MyNat.ble a b = true)
  guard_target =ₛ MyNat.ble a b = true ↔ a ≤ b
  sorry


#check MyNat.ble.induct
/-
MyNat.ble.induct (motive : MyNat → MyNat → Prop)
  (case1 : ∀ (b : MyNat), motive MyNat.zero b)
  (case2 : ∀ (n : MyNat), motive n.succ MyNat.zero)
  (case3 : ∀ (a b : MyNat), motive a b → motive a.succ b.succ)
  (a b : MyNat) : motive a b
-/

def MyNat.ble.inductAux (motive : MyNat → MyNat → Prop)
  (case1 : ∀ (n : MyNat), motive 0 n)
  (case2 : ∀ (n : MyNat), motive (n + 1) 0)
  (case3 : ∀ (m n : MyNat), motive m n → motive (m + 1) (n + 1))
  (m n : MyNat) : motive m n := by
  induction m, n using MyNat.ble.induct with
  | case1 n => apply case1
  | case2 n => apply case2
  | case3 m n h => apply case3; assumption

theorem MyNat.le_impl (m n : MyNat) : MyNat.ble m n ↔ m ≤ n := by
  induction m, n using ble.inductAux with
  | case1 n =>
    simp
  | case2 n =>
    simp_all
  | case3 m n ih =>
    simp [ih]

instance : DecidableLE MyNat := fun n m =>
  decidable_of_iff (MyNat.ble n m) (MyNat.le_impl n m)

#eval 1 ≤ 3
#eval 12 ≤ 13

example : 1 ≤ 9 := by
  decide

example : 32 ≤ 47 := by
  decide

theorem MyNat.lt_impl (m n : MyNat) : ble (m + 1) n ↔ m < n := by
  rw [le_impl]
  rfl

instance : DecidableLT MyNat := fun n m =>
  decidable_of_iff (MyNat.ble (n + 1) m) (MyNat.lt_impl n m)

example : 1 < 4 := by decide

example : 23 < 32 ∧ 12 ≤ 24 := by
  decide
