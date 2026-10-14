import TerminalLogConcavity.EnvelopeWeightBound
import TerminalLogConcavity.ReleasePhase
import TerminalLogConcavity.ReleaseCoefficientBounds
import TerminalLogConcavity.EnvelopeSmallness
import TerminalLogConcavity.EnvelopeSummation
import TerminalLogConcavity.ModelAdjacent

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

theorem upperChain_product_model_bound {q H : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H)
    (hmodel : ∀ j ≤ q, ((releaseModelPolynomial q H).coeff j : ℝ) ≤ 3*releaseModel q H j)
    {j : ℕ} (hj : j ≤ q) :
    ((∏ i ∈ Finset.range q,upperChain q (thresholdIndex (target q H)) (i+1)).coeff j : ℝ) ≤
      12*releaseModel q H j := by
  have ha := selectedAmplifier_ge_128 (show 1 ≤ q by omega) hH
  have h1 := upperChain_product_coeff_le hq (thresholdIndex (target q H)) j ha hj
  have h2 := lowerChain_product_bound hq (thresholdIndex (target q H)) ha j
  simp only [realPolynomial_coeff,coeff_C_mul] at h2
  have h3 := hmodel j hj
  change ((∏ i ∈ Finset.range q,lowerChain q (thresholdIndex (target q H)) (i+1)).coeff j : ℝ) ≤
      2*((releaseModelPolynomial q H).coeff j : ℝ) at h2
  nlinarith only [h1,h2,h3]

theorem release_coefficient_upper_of_model {q H j : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H) (hj : j ≤ q)
    (hmodel : ∀ k ≤ q, ((releaseModelPolynomial q H).coeff k : ℝ) ≤ 3*releaseModel q H k) :
    ((releaseReversedPolynomial q H).coeff j : ℝ) ≤ (2:ℝ)^(q+3)*releaseModel q H j := by
  let t := thresholdIndex (target q H)
  let ws := releaseEnvelopeWeights q t
  let U := ∏ i ∈ Finset.range q,upperChain q t (i+1)
  let W := ws.sum
  have hpoly := release_common_envelope q t
  rw [pathStateSum_graph] at hpoly
  have hcoeff := hpoly j
  change (releaseReversedPolynomial q H).coeff j ≤ (C (2^(q-1))*linearProduct ws*U).coeff j at hcoeff
  rw [mul_assoc,coeff_C_mul,coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => (linearProduct ws).coeff a * U.coeff b) j] at hcoeff
  have hreal : ((releaseReversedPolynomial q H).coeff j : ℝ) ≤
      (2:ℝ)^(q-1)*∑ k ∈ Finset.range (j+1),
        ((linearProduct ws).coeff k : ℝ)*(U.coeff (j-k) : ℝ) := by exact_mod_cast hcoeff
  have hsum : (∑ k ∈ Finset.range (j+1),((linearProduct ws).coeff k : ℝ)*(U.coeff (j-k) : ℝ)) ≤
      12*(∑ k ∈ Finset.range (j+1),(W:ℝ)^k*releaseModel q H (j-k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hk' : k ≤ j := by have := Finset.mem_range.mp hk; omega
    have hE : ((linearProduct ws).coeff k : ℝ) ≤ (W:ℝ)^k := by exact_mod_cast linearProduct_coeff_le ws k
    have hU := upperChain_product_model_bound hq hH hmodel (show j-k ≤ q by omega)
    have hmul := mul_le_mul hE hU (by positivity : (0:ℝ) ≤ U.coeff (j-k)) (by positivity : (0:ℝ) ≤ (W:ℝ)^k)
    convert hmul using 1 ; ring
  have ha : 1 ≤ (selectedAmplifier q H : ℝ) := by exact_mod_cast amplifier_pos t
  have hback (k : ℕ) (hk : k < j+1) :
      releaseModel q H (j-k) ≤ ((q:ℝ)/(selectedAmplifier q H : ℝ)^(2*massParameter q))^k*releaseModel q H j := by
    exact modelCoefficient_backwards ha hj (by omega)
  have hsmall := release_envelope_small hq hH (releaseEnvelope_sum_bound hq hH)
  have hfinite := finite_envelope_bound (le_of_lt (releaseModel_pos hj))
    (show (0:ℝ) ≤ W by positivity) (by positivity : (0:ℝ) ≤ (q:ℝ)/(selectedAmplifier q H : ℝ)^(2*massParameter q))
    hsmall hback
  have h1 := mul_le_mul_of_nonneg_left hsum (show (0:ℝ) ≤ 2^(q-1) by positivity)
  have h2 := mul_le_mul_of_nonneg_left hfinite (show (0:ℝ) ≤ 12*2^(q-1) by positivity)
  have hp : (2:ℝ)^(q+3) = 16*2^(q-1) := by
    have he : q+3=(q-1)+4 := by omega
    rw [he,pow_add]
    norm_num
    ring
  rw [hp]
  nlinarith only [hreal,h1,h2]

/-- The full upper coefficient estimate for the actual release tree. -/
theorem release_coefficient_upper {q H j : ℕ} (hq : 2 ≤ q) (hH : 1 ≤ H) (hj : j ≤ q) :
    ((releaseReversedPolynomial q H).coeff j : ℝ) ≤ (2:ℝ)^(q+3)*releaseModel q H j :=
  release_coefficient_upper_of_model hq hH hj (fun _ hk => releaseModelPolynomial_upper hq hH hk)

end TerminalLogConcavity
