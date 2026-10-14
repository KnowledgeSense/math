import BoseBurton.ProjectiveDuality
import BoseBurton.ProjectiveIntervals
import BoseBurton.ProjectiveEvaluationAlgebra

noncomputable section
namespace BoseBurton
open Submodule Module Finset Polynomial MatroidInverseZ
universe u v

/-- The actual projective KL polynomial is one in every finite dimension. -/
theorem projectiveP_eq_one (K : Type u) (V : Type v) [Field K] [AddCommGroup V]
    [Module K V] [Module.Finite K V] [Finite V] : projectiveP K V=1 := by
  classical
  generalize hd : finrank K V=n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases hn : n=0
    · have ht : (⊤ : Submodule K V)=⊥ :=
        Submodule.finrank_eq_zero.mp (by simp [hd,hn])
      unfold projectiveP
      rw [ht,kl_self]
    · have hnpos : 0<n := by omega
      have hne : (⊥ : Submodule K V)≠⊤ := by
        intro he
        have h := congrArg (fun U : Submodule K V=>finrank K U) he
        simp only [finrank_bot,finrank_top,hd] at h
        omega
      have hup (U : Submodule K V) (hU : U≠⊥) :
          kl (fun S : Submodule K V=>finrank K S) ⊤ U=1 := by
        rw [projective_upper_kl]
        have hpos : 0<finrank K U := by
          have h := Submodule.finrank_lt_finrank_of_lt (show (⊥ : Submodule K V)<U from bot_lt_iff_ne_bot.mpr hU)
          simpa only [finrank_bot] using h
        have hdim := Submodule.finrank_quotient_add_finrank U
        have hlt : finrank K (V ⧸ U)<n := by omega
        exact ih (finrank K (V ⧸ U)) hlt (V ⧸ U) rfl
      let rank : Submodule K V→ℕ := fun U=>finrank K U
      have hmono : Monotone rank := fun _ _ h=>Submodule.finrank_mono h
      have hZ : zKernel rank ⊥ ⊤=projectiveRankEnumerator K V+(projectiveP K V-1) := by
        rw [zKernel_apply]
        simp only [rank,finrank_bot,Nat.sub_zero,Icc_bot_top]
        have hz := sum_erase_add univ (fun U : Submodule K V=>X^(finrank K U)*kl rank ⊤ U) (mem_univ ⊥)
        have hg := sum_erase_add univ (fun U : Submodule K V=>(X:Polynomial ℤ)^(finrank K U)) (mem_univ ⊥)
        have he : (∑ U∈univ.erase (⊥ : Submodule K V),X^(finrank K U)*kl rank ⊤ U)=
            ∑ U∈univ.erase (⊥ : Submodule K V),(X:Polynomial ℤ)^(finrank K U) := by
          apply sum_congr rfl
          intro U hU
          rw [hup U (mem_erase.mp hU).1,mul_one]
        rw [he] at hz
        simp only [finrank_bot,pow_zero,one_mul] at hz hg
        change _=projectiveRankEnumerator K V+(projectiveP K V-1)
        unfold projectiveRankEnumerator
        change _+projectiveP K V=_ at hz
        linear_combination -hz+hg
      apply strict_half_palindromic_difference n hnpos
      · intro i hi
        unfold projectiveP
        apply kl_high_coeff _ ⊥ ⊤ hne i
        simpa only [finrank_top,finrank_bot,Nat.sub_zero,hd] using hi
      · have h := zKernel_reflect rank hmono ⊥ ⊤
        rw [hZ,reflect_add] at h
        simp only [rank,finrank_top,finrank_bot,Nat.sub_zero] at h
        rw [projectiveRankEnumerator_reflect] at h
        have he := add_left_cancel h
        simpa only [hd] using he

end BoseBurton
