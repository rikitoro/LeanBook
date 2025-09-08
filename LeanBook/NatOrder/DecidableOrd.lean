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
