import BoseBurton.ProjectiveYExpansion

noncomputable section
namespace BoseBurton
open Submodule Module Finset Polynomial
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
    [Fintype K] [Module.Finite K V] [Finite V]

theorem projectiveY_coeff_real (k : ℕ) :
    ((projectiveY K V).coeff k:ℝ)=
      (Fintype.card K:ℝ)^((finrank K V).choose 2)*gaussian (Fintype.card K:ℝ)⁻¹ (finrank K V) k := by
  classical
  have he := congrArg (fun p : Polynomial ℝ=>p.coeff k) (projectiveY_real_expansion K V)
  simp only [coeff_map,finsetSum_coeff,coeff_C_mul,coeff_X_pow,
    mul_ite,mul_one,mul_zero] at he
  change ((projectiveY K V).coeff k:ℝ)=_ at he
  simp only [eq_comm (a:=k)] at he
  rw [subspace_sum_by_dimension K V (fun i=>if finrank K V-i=k then
    (Fintype.card K:ℝ)^(i.choose 2+(finrank K V-i).choose 2) else 0)] at he
  by_cases hk : k≤finrank K V
  · have hs : (∑ i∈range (finrank K V+1),gaussian (Fintype.card K:ℝ) (finrank K V) i*
        (if finrank K V-i=k then (Fintype.card K:ℝ)^(i.choose 2+(finrank K V-i).choose 2) else 0))=
        gaussian (Fintype.card K:ℝ) (finrank K V) (finrank K V-k)*
          (Fintype.card K:ℝ)^((finrank K V-k).choose 2+k.choose 2) := by
      have hsum : (∑ i∈range (finrank K V+1),gaussian (Fintype.card K:ℝ) (finrank K V) i*
        (if finrank K V-i=k then (Fintype.card K:ℝ)^(i.choose 2+(finrank K V-i).choose 2) else 0))=
        ∑ i∈range (finrank K V+1),if i=finrank K V-k then
          gaussian (Fintype.card K:ℝ) (finrank K V) i*(Fintype.card K:ℝ)^(i.choose 2+k.choose 2) else 0 := by
        apply sum_congr rfl
        intro i hi
        have hi' : i≤finrank K V := by simp only [mem_range] at hi; omega
        by_cases hik : i=finrank K V-k
        · have heq : finrank K V-i=k := by omega
          simp [hik,Nat.sub_sub_self hk]
        · have heq : finrank K V-i≠k := by omega
          simp [hik,heq]
      rw [hsum]
      simp [show finrank K V-k<finrank K V+1 by omega]
    rw [hs,gaussian_symm (Fintype.card K:ℝ) (finrank K V) k hk] at he
    rw [he]
    have hq : (1:ℝ)<Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α:=K)
    rw [gaussian_dual (Fintype.card K:ℝ) hq (finrank K V) k hk]
    have hexp : k*(finrank K V-k)+((finrank K V-k).choose 2+k.choose 2)=(finrank K V).choose 2 := by
      have h := choose_two_add k (finrank K V-k)
      rw [Nat.add_sub_of_le hk] at h
      omega
    calc
      _ = (Fintype.card K:ℝ)^(k*(finrank K V-k)+((finrank K V-k).choose 2+k.choose 2))*
          gaussian (Fintype.card K:ℝ)⁻¹ (finrank K V) k := by rw [pow_add]; ring
      _ = _ := by rw [hexp]
  · rw [gaussian_outside (Fintype.card K:ℝ)⁻¹ (finrank K V) k (by omega),mul_zero,he]
    apply sum_eq_zero
    intro i _
    have h : finrank K V-i≠k := by omega
    simp [h]

theorem projectiveY_eq_projectiveRow :
    (projectiveY K V).map (Int.castRingHom ℝ)=projectiveRow (Fintype.card K:ℝ) (finrank K V) := by
  ext k
  rw [coeff_map,projectiveRow,coeff_C_mul,gaussianRow_coeff]
  exact projectiveY_coeff_real K V k

end BoseBurton
