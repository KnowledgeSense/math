import MainTheorems.LocalPermutation.DegreeBounds

namespace ResearchMain.LocalPermutation

open Classical MvPolynomial

variable {K : Type} [Field K] [Fintype K]

noncomputable def topExponent (σ : Type) [Fintype σ] (b : ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun _ => b)

theorem topExponent_apply (σ : Type) [Fintype σ] (b : ℕ) (i : σ) : topExponent σ b i = b := rfl

theorem topExponent_sum (σ : Type) [Fintype σ] (b : ℕ) :
    (topExponent σ b).sum (fun _ e => e) = Fintype.card σ * b := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simp only [topExponent_apply, Finset.sum_const, Finset.card_univ, smul_eq_mul]

noncomputable def weightedMoment {σ : Type} [Fintype σ] [DecidableEq σ] (f : (σ → K) → K) : K :=
  ∑ x, f x * ∏ i, x i

theorem sum_power_weighted (hq : 2 < Fintype.card K) (k : ℕ) (hk : k ≤ Fintype.card K - 1) :
    (∑ x : K, x ^ (k + 1)) = if k = Fintype.card K - 2 then -1 else 0 := by
  by_cases hlast : k = Fintype.card K - 1
  · subst k
    rw [show Fintype.card K - 1 + 1 = Fintype.card K by omega]
    simp only [FiniteField.pow_card]
    rw [ite_eq_right (by omega)]
    simpa only [pow_one] using FiniteField.sum_pow_lt_card_sub_one K 1 (by omega)
  · by_cases htop : k = Fintype.card K - 2
    · rw [ite_eq_left htop, htop, show Fintype.card K - 2 + 1 = Fintype.card K - 1 by omega]
      exact sum_power_last
    · rw [ite_eq_right htop]
      exact FiniteField.sum_pow_lt_card_sub_one K (k + 1) (by omega)

theorem weightedMoment_polynomial (hq : 2 < Fintype.card K) {σ : Type} [Fintype σ] [DecidableEq σ]
    {P : MvPolynomial σ K} (hP : Reduced P) :
    weightedMoment (fun x => eval x P) = P.coeff (topExponent σ (Fintype.card K - 2)) * (-1) ^ Fintype.card σ := by
  have heval (x : σ → K) : eval x P = ∑ d ∈ P.support, P.coeff d * ∏ i, x i ^ d i := by
    change eval₂ (RingHom.id K) x P = _
    simpa only [RingHom.id_apply] using eval₂_eq' (RingHom.id K) x P
  have hsplit (d : σ →₀ ℕ) : (∑ x : σ → K, ∏ i, x i ^ (d i + 1)) =
      ∏ i, ∑ x : K, x ^ (d i + 1) := (Fintype.prod_sum (fun i (x : K) => x ^ (d i + 1))).symm
  unfold weightedMoment
  simp_rw [heval, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.prod_mul_distrib, ← pow_succ, ← Finset.mul_sum, hsplit]
  have hpow : ∀ d ∈ P.support, (∏ i, ∑ x : K, x ^ (d i + 1)) =
      if d = topExponent σ (Fintype.card K - 2) then (-1 : K) ^ Fintype.card σ else 0 := by
    intro d hd
    have hdBound (i : σ) : d i ≤ Fintype.card K - 1 :=
      (monomial_le_degreeOf i hd).trans (reduced_iff_degreeOf.mp hP i)
    simp_rw [sum_power_weighted hq _ (hdBound _)]
    by_cases he : d = topExponent σ (Fintype.card K - 2)
    · subst d
      simp only [topExponent_apply, ite_true, Finset.prod_const, Finset.card_univ]
    · rw [ite_eq_right he]
      obtain ⟨i, hi⟩ : ∃ i, d i ≠ Fintype.card K - 2 := by
        by_contra h
        apply he
        ext i
        simpa only [topExponent_apply] using not_not.mp (not_exists.mp h i)
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [ite_eq_right hi]
  have hsum : (∑ d ∈ P.support, P.coeff d * ∏ i, ∑ x : K, x ^ (d i + 1)) =
      ∑ d ∈ P.support, if d = topExponent σ (Fintype.card K - 2) then
        P.coeff d * (-1 : K) ^ Fintype.card σ else 0 := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [hpow d hd]
    split_ifs <;> simp
  rw [hsum, Finset.sum_eq_single (topExponent σ (Fintype.card K - 2))]
  · rw [ite_eq_left rfl]
  · intro d _ hd
    rw [ite_eq_right hd]
  · intro hd
    have hzero : P.coeff (topExponent σ (Fintype.card K - 2)) = 0 := by
      simpa only [mem_support_iff, not_not] using hd
    simp only [hzero, zero_mul, ite_true]

omit [Fintype K] in
theorem totalDegree_bound {σ : Type} [Fintype σ] {P : MvPolynomial σ K} {b : ℕ}
    (h : ∀ i, P.degreeOf i ≤ b) : P.totalDegree ≤ Fintype.card σ * b := by
  rw [totalDegree, Finset.sup_le_iff]
  intro d hd
  rw [Finsupp.sum_fintype _ _ (by simp)]
  calc
    ∑ i, d i ≤ ∑ _i : σ, b := Finset.sum_le_sum fun i _ => (monomial_le_degreeOf i hd).trans (h i)
    _ = Fintype.card σ * b := by simp

theorem totalDegree_of_moment (hq : 2 < Fintype.card K) {n : ℕ} {P : MvPolynomial (Fin n) K}
    (hP : Reduced P) (hf : IsLocalPermutation (fun x => eval x P))
    (hm : weightedMoment (fun x => eval x P) ≠ 0) : P.totalDegree = n * (Fintype.card K - 2) := by
  have htop : P.coeff (topExponent (Fin n) (Fintype.card K - 2)) ≠ 0 := by
    intro he
    apply hm
    rw [weightedMoment_polynomial hq hP, he, zero_mul]
  apply le_antisymm
  · simpa only [Fintype.card_fin] using totalDegree_bound (degree_bound hq hP hf)
  · have h := le_totalDegree (mem_support_iff.mpr htop)
    rw [topExponent_sum, Fintype.card_fin] at h
    exact h

def HasMaximumDegree (K : Type) [Field K] [Fintype K] (n : ℕ) : Prop :=
  ∃ P : MvPolynomial (Fin n) K, PrimeCoefficients P ∧ IsLocalPermutation (fun x => eval x P) ∧
    (∀ i, P.degreeOf i ≤ Fintype.card K - 2) ∧ P.totalDegree = n * (Fintype.card K - 2)

theorem exists_maximum_degree (p : ℕ) [Fact p.Prime] [CharP K p] (hq : 2 < Fintype.card K)
    {n : ℕ} {f : (Fin n → K) → K} (hf : IsLocalPermutation f) (hFrob : FrobeniusEquivariant p f)
    (hm : weightedMoment f ≠ 0) : ∃ P : MvPolynomial (Fin n) K,
      PrimeCoefficients P ∧ IsLocalPermutation (fun x => eval x P) ∧
      (∀ i, P.degreeOf i ≤ Fintype.card K - 2) ∧ P.totalDegree = n * (Fintype.card K - 2) := by
  have hlocal : IsLocalPermutation (fun x => eval x (interpolate f)) := by simpa only [eval_interpolate] using hf
  have hmoment : weightedMoment (fun x => eval x (interpolate f)) ≠ 0 := by simpa only [eval_interpolate] using hm
  exact ⟨interpolate f, interpolate_primeCoefficients p f hFrob, hlocal,
    degree_bound hq (interpolate_reduced f) hlocal,
    totalDegree_of_moment hq (interpolate_reduced f) hlocal hmoment⟩

end ResearchMain.LocalPermutation
