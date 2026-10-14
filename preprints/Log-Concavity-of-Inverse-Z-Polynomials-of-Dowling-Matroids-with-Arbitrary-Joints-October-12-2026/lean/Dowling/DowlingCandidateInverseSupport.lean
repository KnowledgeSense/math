import Dowling.DowlingCandidateSupport

noncomputable section
namespace Dowling
open PowerSeries Finset

 theorem candidateWeight_monomial {w n : ℕ} {p : Polynomial ℝ}
    (hp : ∀ k, n < 2*k+w → p.coeff k = 0) :
    CandidateWeight w (C p * X^n) := by
  intro i k hi
  rw [coeff_C_mul, coeff_X_pow]
  split_ifs with h
  · subst i
    simpa only [mul_one] using hp k hi
  · simp

theorem candidateWeight_sum {ι : Type*} (s : Finset ι) {w : ℕ}
    {f : ι → PowerSeries (Polynomial ℝ)} (h : ∀ i ∈ s, CandidateWeight w (f i)) :
    CandidateWeight w (∑ i ∈ s, f i) := by
  intro n k hn
  simp only [map_sum, Polynomial.finsetSum_coeff]
  exact sum_eq_zero fun i hi => h i hi n k hn

/-- Compositional inversion preserves the strict half-degree cone. -/
theorem CandidateWeight.substInv {f : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight 1 f) [Invertible (coeff 1 f)] (h1 : coeff 1 f = 1) :
    CandidateWeight 1 f.substInv := by
  have hinv : ⅟(coeff 1 f) = 1 := by
    have h := invOf_mul_self (coeff 1 f)
    simpa only [h1,mul_one] using h
  have hcoeff (n : ℕ) : ∀ k, n < 2*k+1 → (substInvFun f n).coeff k = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro k hk
      match n with
      | 0 => simp [substInvFun]
      | 1 =>
        have hk0 : k≠0 := by omega
        simp only [substInvFun,hinv,Polynomial.coeff_one]
        simp [hk0]
      | n+2 =>
        have ht : CandidateWeight 1
            (∑ i : Fin (n+2), C (substInvFun f i.val) * X^i.val) := by
          apply candidateWeight_sum
          intro i _
          apply candidateWeight_monomial
          exact ih i.val (by omega)
        have hs := hf.subst ht
        have hz := hs (n+2) k hk
        simpa only [substInvFun,hinv,neg_one_mul,Polynomial.coeff_neg,neg_eq_zero]
          using hz
  intro n k hn
  simpa only [PowerSeries.substInv, coeff_mk] using hcoeff n k hn

theorem CandidateWeight.substInvOfIsUnit {f : PowerSeries (Polynomial ℝ)}
    (hf : CandidateWeight 1 f) (h1 : coeff 1 f = 1) (hu : IsUnit (coeff 1 f)) :
    CandidateWeight 1 (f.substInvOfIsUnit hu) := by
  let := hu.invertible
  rw [substInvOfIsUnit_eq_substInv]
  exact hf.substInv h1

end Dowling
