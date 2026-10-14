import TerminalLogConcavity.GaussianActive
import TerminalLogConcavity.GaussianModel
import TerminalLogConcavity.ElementaryBound

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

theorem normalized_factor_identity (q i : ℕ) {a lam : ℝ} (ha : 0 < a) :
    C (a ^ (i + 1) ^ 2) + (1 + C (lam * a ^ (2 * (i + 1))) * X) ^ q =
      C (a ^ (i + 1) ^ 2) *
        (C (1 + (1 / a) ^ ((i + 1) ^ 2)) + normalizedActive q a lam i) := by
  have hinv : a ^ ((i + 1) ^ 2) * (1 / a) ^ ((i + 1) ^ 2) = 1 := by
    rw [← mul_pow]
    simp [ne_of_gt ha]
  ext n
  by_cases hn : n = 0
  · subst n
    simp only [coeff_add, coeff_C_zero, coeff_C_mul, normalizedActive_zero,
      add_zero, weighted_binomial_coeff_semiring, Nat.choose_zero_right, Nat.cast_one, pow_zero, mul_one]
    nlinarith
  · simp only [coeff_add, coeff_C, hn, ite_false, zero_add, coeff_C_mul,
      normalizedActive, coeff_erase]
    calc
      _ = (a ^ ((i + 1) ^ 2) * (1 / a) ^ ((i + 1) ^ 2)) *
          ((1 + C (lam * a ^ (2 * (i + 1))) * X : ℝ[X]) ^ q).coeff n := by rw [hinv]; ring
      _ = _ := by ring

theorem normalized_factor_bound {p : ℝ[X]} (hp : CoeffNonnegative p) {c : ℝ} (hc : 1 ≤ c) :
    RealCoeffLE (C c + p) (C c * (1 + p)) := by
  intro n
  have hn := hp n
  by_cases he : n = 0
  · subst n; simp only [coeff_add, coeff_C_zero, coeff_C_mul, coeff_one_zero]; nlinarith
  · simp only [coeff_add, coeff_C, coeff_one, he, ite_false, coeff_C_mul, zero_add]
    nlinarith

theorem gaussian_normalization (q a lam : ℕ) (ha : 0 < a) :
    realPolynomial (gaussianPolynomial q a lam) =
      C ((a : ℝ) ^ squareSum q) *
        ∏ i ∈ Finset.range q,
          (C (1 + (1 / (a : ℝ)) ^ ((i + 1) ^ 2)) + normalizedActive q a lam i) := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha
  have hf (i : ℕ) : realPolynomial (gaussianFactor q a lam i) =
      C ((a : ℝ) ^ ((i + 1) ^ 2)) *
        (C (1 + (1 / (a : ℝ)) ^ ((i + 1) ^ 2)) + normalizedActive q a lam i) := by
    simpa [realPolynomial, gaussianFactor, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_pow] using normalized_factor_identity q i (lam := (lam : ℝ)) ha0
  simp only [gaussianPolynomial, realPolynomial, Polynomial.map_prod] at ⊢
  change (∏ i ∈ Finset.range q, realPolynomial (gaussianFactor q a lam i)) = _
  simp only [hf, Finset.prod_mul_distrib]
  congr 1
  rw [← map_prod, Finset.prod_pow_eq_pow_sum]
  rfl

theorem active_product_le_geometric (q : ℕ) {a lam : ℝ} (ha : 0 < a) (hlam : 0 ≤ lam) :
    RealCoeffLE (∏ i ∈ Finset.range q, (1 + normalizedActive q a lam i))
      (∑ k ∈ Finset.range (q + 1), gaussianActiveSum q a lam ^ k) := by
  let ps := (List.range q).map (normalizedActive q a lam)
  have hp : ∀ p ∈ ps, CoeffNonnegative p := by
    intro p hp
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hp
    exact normalizedActive_nonnegative ha hlam
  have h := product_one_add_le_geometric hp
  have he : (List.range q).toFinset = Finset.range q := by ext i; simp
  have hsum : ps.sum = gaussianActiveSum q a lam := by
    dsimp [ps, gaussianActiveSum]
    rw [← List.sum_toFinset _ (show (List.range q).Nodup from List.nodup_range), he]
  have hprod : (ps.map (fun p => 1 + p)).prod =
      ∏ i ∈ Finset.range q, (1 + normalizedActive q a lam i) := by
    dsimp [ps]
    rw [List.map_map, ← List.prod_toFinset _ (show (List.range q).Nodup from List.nodup_range), he]
    rfl
  rw [hprod, hsum] at h
  simpa [ps] using h

theorem gaussian_polynomial_majorization {q a lam : ℕ} (ha : 256 ≤ a) :
    RealCoeffLE (realPolynomial (gaussianPolynomial q a lam))
      (C ((3 / 2 : ℝ) * (a : ℝ) ^ squareSum q) *
        (∑ k ∈ Finset.range (q + 1), gaussianActiveSum q a lam ^ k)) := by
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
  let pref : ℝ := ∏ i ∈ Finset.range q, (1 + (1 / (a : ℝ)) ^ ((i + 1) ^ 2))
  let geo : ℝ[X] := ∑ k ∈ Finset.range (q + 1), gaussianActiveSum q a lam ^ k
  have hpref0 : 0 ≤ pref := Finset.prod_nonneg (fun i _ => by positivity)
  have hpref : pref ≤ 3 / 2 := by
    apply gaussian_prefactor_bound (by positivity)
    apply (div_le_div_iff₀ ha0 (by norm_num : (0 : ℝ) < 256)).mpr
    simpa only [one_mul] using (show (256 : ℝ) ≤ a by exact_mod_cast ha)
  have hactive (i : ℕ) : CoeffNonnegative (normalizedActive q (a : ℝ) (lam : ℝ) i) :=
    normalizedActive_nonnegative ha0 (by positivity)
  have hprod := RealCoeffLE.prod (Finset.range q)
    (fun i _ => normalized_factor_bound (hactive i)
      (show 1 ≤ 1 + (1 / (a : ℝ)) ^ ((i + 1) ^ 2) by apply le_add_of_nonneg_right; positivity))
    (fun i _ => (CoeffNonnegative.C (by positivity)).add
      (hactive i))
  have he : (∏ i ∈ Finset.range q,
      C (1 + (1 / (a : ℝ)) ^ ((i + 1) ^ 2)) * (1 + normalizedActive q a lam i)) =
      C pref * ∏ i ∈ Finset.range q, (1 + normalizedActive q a lam i) := by
    rw [Finset.prod_mul_distrib, ← map_prod]
  rw [he] at hprod
  have hgeo := (active_product_le_geometric q ha0 (show 0 ≤ (lam : ℝ) by positivity)).scale hpref0
  have hfirst := (hprod.trans hgeo).scale (show 0 ≤ (a : ℝ) ^ squareSum q by positivity)
  have hnorm := gaussian_normalization q a lam (by omega)
  have hfirst' : RealCoeffLE (realPolynomial (gaussianPolynomial q a lam))
      (C ((a : ℝ) ^ squareSum q * pref) * geo) := by
    rw [hnorm]
    convert hfirst using 1 ; simp only [map_mul, geo] ; ring
  have hgeo0 : CoeffNonnegative geo := by
    intro n
    simp only [geo, finsetSum_coeff]
    exact Finset.sum_nonneg (fun k _ => (gaussianActiveSum_nonnegative ha0 (by positivity)).pow k n)
  have hscale : (a : ℝ) ^ squareSum q * pref ≤ (3 / 2 : ℝ) * (a : ℝ) ^ squareSum q := by
    have h := mul_le_mul_of_nonneg_left hpref (show 0 ≤ (a : ℝ) ^ squareSum q by positivity)
    simpa [mul_comm] using h
  exact hfirst'.trans (RealCoeffLE.scale_mono hgeo0 hscale)

end TerminalLogConcavity
