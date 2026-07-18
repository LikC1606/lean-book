/-!
# Chapter 14 — Insertion sort, fully verified (no sorry)

`Sorted` := `List.Pairwise (· ≤ ·)`.
-/

namespace Examples.Ch14Sort

def insert (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insert x ys

def insertionSort : List Nat → List Nat
  | [] => []
  | x :: xs => insert x (insertionSort xs)

def Sorted (xs : List Nat) : Prop :=
  List.Pairwise (· ≤ ·) xs

theorem mem_insert (x : Nat) (xs : List Nat) (z : Nat) :
    z ∈ insert x xs ↔ z = x ∨ z ∈ xs := by
  induction xs with
  | nil =>
      simp [insert]
  | cons y ys ih =>
      constructor
      · intro h
        by_cases hxy : x ≤ y
        · have heq : insert x (y :: ys) = x :: y :: ys := by
            simp [insert, hxy]
          rw [heq] at h
          rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inl rfl
          · rcases List.mem_cons.mp h' with rfl | hz
            · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
            · exact Or.inr (List.mem_cons.mpr (Or.inr hz))
        · have heq : insert x (y :: ys) = y :: insert x ys := by
            simp [insert, hxy]
          rw [heq] at h
          rcases List.mem_cons.mp h with rfl | hz
          · exact Or.inr (List.mem_cons.mpr (Or.inl rfl))
          · rcases ih.mp hz with rfl | hys
            · exact Or.inl rfl
            · exact Or.inr (List.mem_cons.mpr (Or.inr hys))
      · intro h
        by_cases hxy : x ≤ y
        · have heq : insert x (y :: ys) = x :: y :: ys := by
            simp [insert, hxy]
          rw [heq]
          rcases h with rfl | h'
          · exact List.mem_cons.mpr (Or.inl rfl)
          · rcases List.mem_cons.mp h' with rfl | hz
            · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
            · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr hz)))
        · have heq : insert x (y :: ys) = y :: insert x ys := by
            simp [insert, hxy]
          rw [heq]
          rcases h with rfl | h'
          · exact List.mem_cons.mpr (Or.inr (ih.mpr (Or.inl rfl)))
          · rcases List.mem_cons.mp h' with rfl | hz
            · exact List.mem_cons.mpr (Or.inl rfl)
            · exact List.mem_cons.mpr (Or.inr (ih.mpr (Or.inr hz)))

theorem sorted_insert (x : Nat) (xs : List Nat) (hs : Sorted xs) :
    Sorted (insert x xs) := by
  induction xs with
  | nil =>
      exact List.pairwise_singleton (· ≤ ·) x
  | cons y ys ih =>
      by_cases hxy : x ≤ y
      · have heq : insert x (y :: ys) = x :: y :: ys := by simp [insert, hxy]
        rw [heq]
        refine List.Pairwise.cons ?_ hs
        intro z hz
        rcases List.mem_cons.mp hz with rfl | hzys
        · exact hxy
        · exact Nat.le_trans hxy (List.rel_of_pairwise_cons hs hzys)
      · have hyx : y ≤ x := Nat.le_of_not_le hxy
        have hs_ys : Sorted ys := (List.pairwise_cons.mp hs).2
        have h_ins : Sorted (insert x ys) := ih hs_ys
        have heq : insert x (y :: ys) = y :: insert x ys := by simp [insert, hxy]
        rw [heq]
        refine List.Pairwise.cons ?_ h_ins
        intro z hz
        rcases (mem_insert x ys z).mp hz with rfl | hzys
        · exact hyx
        · exact List.rel_of_pairwise_cons hs hzys

theorem sorted_insertionSort (xs : List Nat) : Sorted (insertionSort xs) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons x xs ih => exact sorted_insert x (insertionSort xs) ih

def count (a : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => (if a = y then 1 else 0) + count a ys

theorem count_insert (x z : Nat) (xs : List Nat) :
    count z (insert x xs) = (if z = x then 1 else 0) + count z xs := by
  induction xs with
  | nil =>
      simp [insert, count]
  | cons y ys ih =>
      by_cases hxy : x ≤ y
      · simp [insert, hxy, count]
      · simp [insert, hxy, count, ih]; omega

theorem count_insertionSort (z : Nat) (xs : List Nat) :
    count z (insertionSort xs) = count z xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp [insertionSort, count, count_insert, ih]


#eval insertionSort [3, 1, 4, 1, 5, 9, 2, 6]
#print axioms sorted_insertionSort
#print axioms count_insertionSort

end Examples.Ch14Sort
