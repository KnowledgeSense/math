import BoseBurton.SubspaceCountingSums
import BoseBurton.GaussianEuler
import BoseBurton.ProjectiveIntervals

noncomputable section
open scoped Classical
namespace BoseBurton
open Submodule Module Finset MatroidInverseZ IncidenceAlgebra
universe u v

theorem projective_lower_mu {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Module.Finite K V] [Finite V] (U : Submodule K V) :
    IncidenceAlgebra.mu ℤ (⊥ : Submodule K V) U=
      IncidenceAlgebra.mu ℤ (⊥ : Submodule K U) ⊤ := by
  classical
  have h := mu_interval_transport (MapSubtype.orderEmbedding U) (subspaceSpace_fills U) ⊥ ⊤
  change IncidenceAlgebra.mu ℤ ((⊥ : Submodule K U).map U.subtype)
    ((⊤ : Submodule K U).map U.subtype)=_ at h
  simpa only [Submodule.map_bot,Submodule.map_top,range_subtype] using h

theorem projective_mu_formula (K : Type u) (V : Type v) [Field K] [AddCommGroup V]
    [Module K V] [Fintype K] [Module.Finite K V] [Finite V] :
    (IncidenceAlgebra.mu ℤ (⊥ : Submodule K V) ⊤ : ℝ)=
      (-1:ℝ)^(finrank K V)*(Fintype.card K : ℝ)^((finrank K V).choose 2) := by
  classical
  generalize hd : finrank K V=n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hn : n=0
    · have ht : (⊤ : Submodule K V)=⊥ := Submodule.finrank_eq_zero.mp (by simp [hd,hn])
      simp [ht,hn]
    · have hnpos : 1≤n := by omega
      have hne : (⊥ : Submodule K V)≠⊤ := by
        intro he
        have h := congrArg (fun U : Submodule K V=>finrank K U) he
        simp only [finrank_bot,finrank_top,hd] at h
        omega
      have hproper (U : Submodule K V) (hU : U≠⊤) :
          (IncidenceAlgebra.mu ℤ (⊥ : Submodule K V) U : ℝ)=
            (-1:ℝ)^(finrank K U)*(Fintype.card K : ℝ)^((finrank K U).choose 2) := by
        rw [projective_lower_mu]
        have hlt := Submodule.finrank_lt_finrank_of_lt (show U<(⊤ : Submodule K V) from lt_top_iff_ne_top.mpr hU)
        rw [finrank_top,hd] at hlt
        exact ih (finrank K U) hlt U rfl
      have hm : (∑ U : Submodule K V,(IncidenceAlgebra.mu ℤ (⊥ : Submodule K V) U:ℝ))=0 := by
        have h := IncidenceAlgebra.sum_Icc_mu_right (𝕜:=ℤ) (⊥ : Submodule K V) ⊤
        simp only [Icc_bot_top,hne,ite_false] at h
        exact_mod_cast h
      have hc : (∑ U : Submodule K V,(-1:ℝ)^(finrank K U)*
          (Fintype.card K : ℝ)^((finrank K U).choose 2))=0 := by
        rw [subspace_sum_by_dimension K V (fun i=>(-1:ℝ)^i*(Fintype.card K:ℝ)^(i.choose 2)),hd]
        have hq : (1:ℝ)<Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α:=K)
        have h := gaussian_euler_sum (Fintype.card K : ℝ) hq n hnpos
        convert h using 1
        apply sum_congr rfl
        intro i _
        ring
      have he : (∑ U∈univ.erase (⊤ : Submodule K V),(IncidenceAlgebra.mu ℤ (⊥ : Submodule K V) U:ℝ))=
          ∑ U∈univ.erase (⊤ : Submodule K V),(-1:ℝ)^(finrank K U)*(Fintype.card K : ℝ)^((finrank K U).choose 2) := by
        apply sum_congr rfl
        intro U hU
        exact hproper U (mem_erase.mp hU).1
      have hm' := sum_erase_add univ (fun U : Submodule K V=>(IncidenceAlgebra.mu ℤ (⊥ : Submodule K V) U:ℝ)) (mem_univ ⊤)
      have hc' := sum_erase_add univ (fun U : Submodule K V=>(-1:ℝ)^(finrank K U)*(Fintype.card K : ℝ)^((finrank K U).choose 2)) (mem_univ ⊤)
      rw [he,hm] at hm'
      rw [hc,finrank_top,hd] at hc'
      linarith

end BoseBurton
