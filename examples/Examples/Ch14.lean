/-!
# Chapter 14 — Software verification basics
-/

namespace Examples.Ch14

def myAdd : Nat → Nat → Nat
  | m, 0 => m
  | m, n + 1 => (myAdd m n) + 1

theorem myAdd_eq_add (m n : Nat) : myAdd m n = m + n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      calc myAdd m (k + 1)
          = myAdd m k + 1 := rfl
        _ = m + k + 1 := by rw [ih]
        _ = m + (k + 1) := by omega

structure Account where
  balance : Int
deriving Repr

def transfer (src dst : Account) (amount : Int) : Option (Account × Account) :=
  if amount ≤ 0 ∨ src.balance < amount then none
  else
    some
      ({ src with balance := src.balance - amount },
       { dst with balance := dst.balance + amount })

theorem transfer_preserves_total
    (src dst : Account) (amount : Int)
    (src' dst' : Account)
    (h : transfer src dst amount = some (src', dst')) :
    src'.balance + dst'.balance = src.balance + dst.balance := by
  simp [transfer] at h
  -- Success branch: preconditions ∧ accounts equal to updated structs
  rcases h with ⟨_, rfl, rfl⟩
  change (src.balance - amount) + (dst.balance + amount) = src.balance + dst.balance
  omega

theorem transfer_fail_if_nonpos
    (src dst : Account) (amount : Int) (h : amount ≤ 0) :
    transfer src dst amount = none := by
  simp [transfer, h]

inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : α → Vec α n → Vec α (n + 1)

def Vec.map (f : α → β) : Vec α n → Vec β n
  | .nil => .nil
  | .cons x xs => .cons (f x) (xs.map f)

theorem Vec.map_map (f : β → γ) (g : α → β) (v : Vec α n) :
    Vec.map f (Vec.map g v) = Vec.map (f ∘ g) v := by
  induction v with
  | nil => rfl
  | cons x xs ih => simp [Vec.map, ih]

end Examples.Ch14
