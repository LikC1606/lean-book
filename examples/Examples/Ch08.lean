/-!
# Chapter 8 — Propositions as types
-/

namespace Examples.Ch08

variable {A B : Prop}

theorem and_swap : A ∧ B → B ∧ A :=
  fun h => ⟨h.right, h.left⟩

theorem and_swap_tac : A ∧ B → B ∧ A := by
  intro h
  exact ⟨h.right, h.left⟩

theorem or_swap (h : A ∨ B) : B ∨ A :=
  match h with
  | .inl ha => .inr ha
  | .inr hb => .inl hb

theorem not_false : ¬False := fun h => h

theorem exists_square : ∃ n : Nat, n * n = 16 :=
  ⟨4, rfl⟩

theorem two_eq_two : 2 = 2 := rfl

#print axioms and_swap
#print axioms exists_square

end Examples.Ch08
