/-!
# Chapter 9 — Longer tactic proofs without sorry

`zero_add` and `add_comm` by induction (stdlib also has these; we re-prove for practice).
-/

namespace Examples.Ch09Add

theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Nat.add_succ, ih]

theorem add_succ (m n : Nat) : m + Nat.succ n = Nat.succ (m + n) := by
  rfl

theorem succ_add (m n : Nat) : Nat.succ m + n = Nat.succ (m + n) := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Nat.add_succ, ih, Nat.add_succ]

theorem add_comm (m n : Nat) : m + n = n + m := by
  induction n with
  | zero =>
      -- m + 0 = 0 + m
      rw [Nat.add_zero, zero_add]
  | succ k ih =>
      -- m + succ k = succ k + m
      rw [Nat.add_succ, succ_add, ih]

theorem add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  induction c with
  | zero => rfl
  | succ k ih =>
      calc (a + b) + k.succ
          = ((a + b) + k).succ := Nat.add_succ _ _
        _ = (a + (b + k)).succ := by rw [ih]
        _ = a + (b + k).succ := (Nat.add_succ _ _).symm

#print axioms add_comm
#print axioms add_assoc

end Examples.Ch09Add
