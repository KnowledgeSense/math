import EmbeddingDimensionStrata.PolynomialJets

/-! # Actual normal forms inside the embedded subalgebras -/
noncomputable section
namespace EmbeddingDimensionStrata
variable {K : Type*} [Field K]

/-- A monic order-`v` power series whose nonleading support consists exclusively
of gaps below the conductor. -/
def IsNormalForm (v : ℕ) (f : PowerSeries K) : Prop :=
  PowerSeries.coeff v f = 1 ∧
  (∀ n < v, PowerSeries.coeff n f = 0) ∧
  (∀ n, v < n → Gamma n ∨ 60 ≤ n → PowerSeries.coeff n f = 0)

theorem IsNormalForm.hasOrder {v : ℕ} {f : PowerSeries K}
    (h : IsNormalForm v f) : HasOrder f v :=
  ⟨h.2.1, by rw [h.1]; exact one_ne_zero⟩

theorem IsNormalForm.coeff_eq_zero_of_value_ne {v n : ℕ} {f : PowerSeries K}
    (h : IsNormalForm v f) (hv : Gamma n) (hne : n ≠ v) :
    PowerSeries.coeff n f = 0 := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact h.2.1 n hlt
  · exact h.2.2 n hgt (Or.inl hv)

/-- A normal form is unique in an actual subalgebra having the given order set. -/
theorem normalForm_unique
    (S : Subalgebra K (PowerSeries K))
    (hvalues : ∀ n, HasValue S n ↔ Gamma n)
    {v : ℕ} {f g : PowerSeries K}
    (hf : f ∈ S) (hg : g ∈ S)
    (hnf : IsNormalForm v f) (hng : IsNormalForm v g) : f = g := by
  by_contra hne
  have hnz : f - g ≠ 0 := sub_ne_zero.mpr hne
  let n := (f - g).order.toNat
  have hord : HasOrder (f - g) n :=
    ⟨fun i hi => PowerSeries.coeff_of_lt_order_toNat i hi, PowerSeries.coeff_order hnz⟩
  have hgam : Gamma n := (hvalues n).mp ⟨f - g, S.sub_mem hf hg, hord⟩
  have hz : PowerSeries.coeff n (f - g) = 0 := by
    by_cases hnv : n = v
    · rw [hnv, map_sub, hnf.1, hng.1, sub_self]
    · simp only [map_sub, hnf.coeff_eq_zero_of_value_ne hgam hnv,
        hng.coeff_eq_zero_of_value_ne hgam hnv, sub_self]
  exact hord.2 hz

theorem trunc_mem_of_tail (S : Subalgebra K (PowerSeries K)) (c : ℕ)
    (hS : (tailIdeal K c : Set (PowerSeries K)) ⊆ S)
    {f : PowerSeries K} (hf : f ∈ S) : (f.trunc c : PowerSeries K) ∈ S := by
  have ht : f - (f.trunc c : PowerSeries K) ∈ S := by
    apply hS
    apply (mem_tailIdeal_iff c _).mpr
    intro i hi
    simp only [map_sub, PowerSeries.coeff_coe_trunc_of_lt hi, sub_self]
  have hm := S.sub_mem hf ht
  simpa only [sub_sub_cancel] using hm

/-- A monic representative can be chosen polynomial of degree below the conductor. -/
theorem exists_monic_representative
    (S : Subalgebra K (PowerSeries K))
    (htail : (tailIdeal K 60 : Set (PowerSeries K)) ⊆ S)
    {v : ℕ} (hv : v < 60) (hvalue : HasValue S v) :
    ∃ f ∈ S, PowerSeries.coeff v f = 1 ∧
      (∀ i < v, PowerSeries.coeff i f = 0) ∧
      (∀ i, 60 ≤ i → PowerSeries.coeff i f = 0) := by
  obtain ⟨f, hf, hlow, hlead⟩ := hvalue
  let g : PowerSeries K := (PowerSeries.coeff v f)⁻¹ • f
  refine ⟨(g.trunc 60 : PowerSeries K),
    trunc_mem_of_tail S 60 htail (S.smul_mem hf _), ?_, ?_, ?_⟩
  · rw [PowerSeries.coeff_coe_trunc_of_lt hv]
    simp only [g, map_smul, smul_eq_mul, inv_mul_cancel₀ hlead]
  · intro i hi
    rw [PowerSeries.coeff_coe_trunc_of_lt (by omega : i < 60)]
    simp only [g, map_smul, hlow i hi, smul_zero]
  · intro i hi
    simp only [Polynomial.coeff_coe, PowerSeries.coeff_trunc, ite_eq_right (by omega : ¬ i < 60)]

/-- Elimination of the semigroup coefficients is performed in the subalgebra
itself; the result is not postulated as additional parameter data. -/
theorem exists_normalForm
    (S : Subalgebra K (PowerSeries K))
    (htail : (tailIdeal K 60 : Set (PowerSeries K)) ⊆ S)
    (hvalues : ∀ n, HasValue S n ↔ Gamma n)
    {v : ℕ} (hv : v < 60) (hgam : Gamma v) :
    ∃ f ∈ S, IsNormalForm v f := by
  have elim : ∀ N : ℕ, ∃ f ∈ S,
      PowerSeries.coeff v f = 1 ∧
      (∀ i < v, PowerSeries.coeff i f = 0) ∧
      (∀ i, 60 ≤ i → PowerSeries.coeff i f = 0) ∧
      (∀ i < N, v < i → Gamma i → PowerSeries.coeff i f = 0) := by
    intro N
    induction N with
    | zero =>
      obtain ⟨f, hf, hlead, hlow, hhigh⟩ :=
        exists_monic_representative S htail hv ((hvalues v).mpr hgam)
      exact ⟨f, hf, hlead, hlow, hhigh, fun i hi => by omega⟩
    | succ N ih =>
      obtain ⟨f, hf, hlead, hlow, hhigh, helim⟩ := ih
      by_cases hN : v < N ∧ Gamma N ∧ N < 60
      · obtain ⟨w, hw, hwlead, hwlow, hwhigh⟩ :=
          exists_monic_representative S htail hN.2.2 ((hvalues N).mpr hN.2.1)
        refine ⟨f - PowerSeries.coeff N f • w,
          S.sub_mem hf (S.smul_mem hw _), ?_, ?_, ?_, ?_⟩
        · simp only [map_sub, map_smul, hwlow v hN.1, smul_zero, sub_zero, hlead]
        · intro i hi
          simp only [map_sub, map_smul, hlow i hi, hwlow i (by omega : i < N),
            smul_zero, sub_self]
        · intro i hi
          simp only [map_sub, map_smul, hhigh i hi, hwhigh i hi, smul_zero, sub_self]
        · intro i hi hvi hgi
          by_cases hin : i < N
          · simp only [map_sub, map_smul, helim i hin hvi hgi, hwlow i hin,
              smul_zero, sub_self]
          · have heq : i = N := by omega
            subst i
            simp only [map_sub, map_smul, hwlead, smul_eq_mul, mul_one, sub_self]
      · refine ⟨f, hf, hlead, hlow, hhigh, ?_⟩
        intro i hi hvi hgi
        by_cases hin : i < N
        · exact helim i hin hvi hgi
        · have heq : i = N := by omega
          subst i
          exact hhigh N (by
            by_contra hh
            exact hN ⟨hvi, hgi, by omega⟩)
  obtain ⟨f, hf, hlead, hlow, hhigh, helim⟩ := elim 60
  refine ⟨f, hf, hlead, hlow, ?_⟩
  intro i hvi hgi
  rcases hgi with hg | hi
  · by_cases hi : i < 60
    · exact helim i hi hvi hg
    · exact hhigh i (by omega)
  · exact hhigh i hi

open scoped PowerSeries.WithPiTopology in
/-- Each value below the conductor has exactly one normal form in every
complete subalgebra in the parameter space. -/
theorem existsUnique_normalForm
    [TopologicalSpace K]
    (S : CompleteGammaSubalgebra (K := K)) {v : ℕ}
    (hv : v < 60) (hgam : Gamma v) :
    ∃! f : PowerSeries K, f ∈ S.val ∧ IsNormalForm v f := by
  obtain ⟨f, hf, hn⟩ := exists_normalForm S.val
    (tailIdeal_le_of_gamma S.val S.property.1 S.property.2) S.property.2 hv hgam
  refine ⟨f, ⟨hf, hn⟩, ?_⟩
  intro g hg
  exact normalForm_unique S.val S.property.2 hg.1 hf hg.2 hn

end EmbeddingDimensionStrata
