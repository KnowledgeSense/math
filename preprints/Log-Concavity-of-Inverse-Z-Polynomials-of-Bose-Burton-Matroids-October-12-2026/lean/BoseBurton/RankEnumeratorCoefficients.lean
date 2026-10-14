import BoseBurton.ProjectiveDuality

noncomputable section
namespace BoseBurton
open Finset Submodule Module Polynomial MatroidInverseZ
open scoped Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [Module.Finite K V] [Finite V]

omit [Module.Finite K V] in
theorem projectiveRankEnumerator_coeff (k : ℕ) :
    (projectiveRankEnumerator K V).coeff k =
      (Nat.card {U : Submodule K V // finrank K U = k} : ℤ) := by
  simp [projectiveRankEnumerator, coeff_X_pow,
    Nat.card_eq_fintype_card, Fintype.card_subtype, eq_comm]

theorem projectiveRankEnumerator_coeff_symm (k : ℕ) (hk : k ≤ finrank K V) :
    (projectiveRankEnumerator K V).coeff k =
      (projectiveRankEnumerator K V).coeff (finrank K V-k) := by
  have h := congrArg (fun p : Polynomial ℤ => p.coeff k) (projectiveRankEnumerator_reflect K V)
  rw [coeff_reflect, revAt_le hk] at h
  exact h.symm

theorem projectiveRankEnumerator_coeff_above (k : ℕ) (hk : finrank K V < k) :
    (projectiveRankEnumerator K V).coeff k = 0 := by
  rw [projectiveRankEnumerator, finsetSum_coeff]
  apply sum_eq_zero
  intro U _
  rw [coeff_X_pow]
  exact ite_eq_right (by have := Submodule.finrank_le U; omega)

end BoseBurton
