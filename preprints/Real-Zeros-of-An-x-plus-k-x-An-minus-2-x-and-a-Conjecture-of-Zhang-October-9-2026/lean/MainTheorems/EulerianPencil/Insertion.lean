import MainTheorems.EulerianPencil.Basic

namespace ResearchMain.EulerianPencil

open Polynomial

noncomputable def afterInsertion (a n : ℕ) (l : List ℕ) : ℤ[X] :=
  ((List.permutations'Aux n l).map (fun v => X ^ descentCount (a :: v))).sum

theorem afterInsertion_step {a b n : ℕ} (ha : a < n) (hb : b < n) (l : List ℕ) :
    afterInsertion a n (b :: l) = X ^ (descentCount (b :: l) + 1) +
      X ^ (if b < a then 1 else 0) * afterInsertion b n l := by
  simp only [afterInsertion, List.permutations'Aux, List.map_cons, List.sum_cons,
    List.map_map, Function.comp_def, descentCount_cons_cons]
  rw [ite_eq_right (Nat.not_lt_of_ge ha.le), ite_eq_left hb]
  simp only [zero_add]
  simp_rw [pow_add]
  rw [List.sum_map_mul_left]
  ring

theorem afterInsertion_formula {n : ℕ} (l : List ℕ)
    (hmax : ∀ b ∈ l, b < n) {a : ℕ} (ha : a < n) :
    afterInsertion a n l = ((descentCount (a :: l) + 1 : ℕ) : ℤ[X]) *
        X ^ descentCount (a :: l) +
      ((l.length - descentCount (a :: l) : ℕ) : ℤ[X]) * X ^ (descentCount (a :: l) + 1) := by
  induction l generalizing a with
  | nil => simp [afterInsertion, descentCount, Nat.not_lt_of_ge ha.le]
  | cons b l ih =>
    have hb : b < n := hmax b List.mem_cons_self
    have ht : ∀ c ∈ l, c < n := fun c hc => hmax c (List.mem_cons_of_mem _ hc)
    have hd := descentCount_prefix_le b l
    rw [afterInsertion_step ha hb, ih ht hb, descentCount_cons_cons]
    by_cases hab : b < a
    · rw [ite_eq_left hab, List.length_cons]
      have hs : l.length + 1 - (1 + descentCount (b :: l)) =
          l.length - descentCount (b :: l) := by omega
      rw [hs]
      push_cast
      simp_rw [pow_add]
      ring
    · rw [ite_eq_right hab]
      simp only [zero_add, List.length_cons, pow_zero, one_mul]
      have hs : l.length + 1 - descentCount (b :: l) =
          (l.length - descentCount (b :: l)) + 1 := by omega
      rw [hs]
      push_cast
      ring

theorem insertion_generating_function (n : ℕ) (l : List ℕ) (hmax : ∀ a ∈ l, a < n) :
    ((List.permutations'Aux n l).map (fun v => (X : ℤ[X]) ^ descentCount v)).sum =
      ((descentCount l + 1 : ℕ) : ℤ[X]) * X ^ descentCount l +
        ((l.length - descentCount l : ℕ) : ℤ[X]) * X ^ (descentCount l + 1) := by
  cases l with
  | nil => simp [descentCount]
  | cons a l =>
    have ha : a < n := hmax a List.mem_cons_self
    have ht : ∀ b ∈ l, b < n := fun b hb => hmax b (List.mem_cons_of_mem _ hb)
    have hd := descentCount_prefix_le a l
    simp only [List.permutations'Aux, List.map_cons, List.sum_cons, List.map_map, Function.comp_def]
    change X ^ descentCount (n :: a :: l) + afterInsertion a n l = _
    rw [descentCount_cons_cons, ite_eq_left ha, afterInsertion_formula l ht ha,
      List.length_cons]
    have hs : l.length + 1 - descentCount (a :: l) =
        (l.length - descentCount (a :: l)) + 1 := by omega
    rw [hs]
    push_cast
    simp_rw [pow_add]
    ring

end ResearchMain.EulerianPencil
