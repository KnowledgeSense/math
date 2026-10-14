import BoseBurton.SubspaceCounting
import BoseBurton.GaussianIdentities

noncomputable section
namespace BoseBurton
open Submodule Module Finset
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Fintype K] [Module.Finite K V] [Finite V]

theorem subspace_count_gaussian_all (k : ℕ) :
    (Nat.card {U : Submodule K V // finrank K U=k} : ℝ)=
      gaussian (Fintype.card K : ℝ) (finrank K V) k := by
  by_cases hk : k≤finrank K V
  · exact subspace_count_gaussian K V k hk
  · have : IsEmpty {U : Submodule K V // finrank K U=k} := ⟨fun U=>by
      have h := Submodule.finrank_le U.val
      rw [U.property] at h
      exact hk h⟩
    rw [gaussian_outside (Fintype.card K : ℝ) (finrank K V) k (by omega)]
    simp

theorem subspace_sum_by_dimension (f : ℕ→ℝ) :
    (∑ U : Submodule K V,f (finrank K U))=
      ∑ k∈range (finrank K V+1),gaussian (Fintype.card K : ℝ) (finrank K V) k*f k := by
  classical
  have he (k : ℕ) : (∑ U : Submodule K V,if finrank K U=k then (1:ℝ) else 0)=
      gaussian (Fintype.card K : ℝ) (finrank K V) k := by
    rw [← subspace_count_gaussian_all K V k,Nat.card_eq_fintype_card,Fintype.card_subtype]
    simp
  calc
    _ = ∑ U : Submodule K V,∑ k∈range (finrank K V+1),if finrank K U=k then f k else 0 := by
      apply sum_congr rfl
      intro U _
      simp [show finrank K U<finrank K V+1 by have := Submodule.finrank_le U; omega]
    _ = ∑ k∈range (finrank K V+1),∑ U : Submodule K V,if finrank K U=k then f k else 0 := by rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro k _
      rw [← he,sum_mul]
      apply sum_congr rfl
      intro U _
      split_ifs <;> simp

end BoseBurton
