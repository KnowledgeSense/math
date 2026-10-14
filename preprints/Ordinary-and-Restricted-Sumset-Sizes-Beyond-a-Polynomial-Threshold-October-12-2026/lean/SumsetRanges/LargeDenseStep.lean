import SumsetRanges.LargeValueSteps

open Finset Polynomial
namespace SumsetRanges
open scoped BigOperators Classical

theorem largeValue_dense_step (h c b x : ℕ) (r u : ℕ → ℕ)
    (hh : 2≤h) (hc : 4*h≤c) (hb : 2≤b) (hx : b-1≤x)
    (hn : nonfreeSize h r u≤c) :
    0≤largeValue h c b r u (x+1)-largeValue h c b r u x ∧
    largeValue h c b r u (x+1)-largeValue h c b r u x≤2*(c.choose (h-2) : ℤ) := by
  let P := sparsePolynomial h c r u
  let Y := restrictedPolynomial (denseSet (b-1) (x+1))-restrictedPolynomial (denseSet (b-1) x)
  have he : largeValue h c b r u (x+1)-largeValue h c b r u x=(P*Y).coeff h := by
    simp only [largeValue,P,Y,mul_sub,coeff_sub]
  rw [he,coeff_mul_range_reversed,sum_range_split_two _ h (by omega)]
  have hy0 : Y.coeff 0=0 := by
    simp [Y,restrictedPolynomial_constant]
  have hy1 : Y.coeff 1=0 := by
    simp only [Y,coeff_sub,coeff_restrictedPolynomial]
    rw [dense_restricted_one _ _ (by omega),dense_restricted_one _ _ hx]
    omega
  simp only [hy0,hy1,zero_mul,zero_add]
  have hy : ∀ e,0≤Y.coeff e ∧ Y.coeff e≤1 := by
    intro e
    have hs := dense_restricted_step (b-1) x e (by omega) hx
    simp only [Y,coeff_sub,coeff_restrictedPolynomial]
    have h0 : ((restrictedSums (denseSet (b-1) x) e).card : ℤ)≤
        ((restrictedSums (denseSet (b-1) (x+1)) e).card : ℤ) := by exact_mod_cast hs.1
    have h1 : ((restrictedSums (denseSet (b-1) (x+1)) e).card : ℤ)≤
        ((restrictedSums (denseSet (b-1) x) e).card : ℤ)+1 := by exact_mod_cast hs.2
    omega
  have hpn := sparsePolynomial_nonneg h c r u
  have hpu := sparsePolynomial_le_binomial h c r u hn
  constructor
  · apply Finset.sum_nonneg
    intro e _
    exact mul_nonneg (hy e).1 (hpn (h-e))
  · have hbnd : (∑ e∈Icc 2 h,Y.coeff e*P.coeff (h-e))≤
        ∑ e∈Icc 2 h,(c.choose (h-e) : ℤ) := by
      apply Finset.sum_le_sum
      intro e _
      have hp := hpu (h-e)
      rw [coeff_one_add_X_pow] at hp
      have hm := mul_le_mul_of_nonneg_right (hy e).2 (hpn (h-e))
      simpa only [one_mul] using hm.trans (by simpa [P] using hp)
    have ht := choose_tail_le_twice_top h c hh hc
    exact hbnd.trans (by exact_mod_cast ht)

end SumsetRanges
