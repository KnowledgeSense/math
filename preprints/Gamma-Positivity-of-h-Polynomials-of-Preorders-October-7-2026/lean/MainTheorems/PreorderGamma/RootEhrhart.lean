import MainTheorems.PreorderGamma.RootMarginCounts
import MainTheorems.PreorderGamma.GammaExpansion

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical

theorem auxiliary_series_coeff {T : Type*} [Fintype T]
    (a : T → ℕ) (N t : ℕ) :
    PowerSeries.coeff t
      ((∏ b : T, multichooseSeries (a b)) *
        ∑ j ∈ Finset.range (N + 1), multichooseSeries j) =
      ∑ s : MarginVectors (Option T) t,
        (∏ b : T, (Nat.multichoose (s.val (some b)) (a b) : ℚ)) *
          ∑ j ∈ Finset.range (N + 1), (Nat.multichoose (s.val none) j : ℚ) := by
  classical
  rw [Finset.mul_sum, map_sum]
  have hcoeff : ∀ j,
      PowerSeries.coeff t ((∏ b : T, multichooseSeries (a b)) * multichooseSeries j) =
        ∑ s : MarginVectors (Option T) t,
          (∏ b : T, (Nat.multichoose (s.val (some b)) (a b) : ℚ)) *
            (Nat.multichoose (s.val none) j : ℚ) := by
    intro j
    let c : Option T → ℕ := Option.elim' j a
    have hprod : (∏ b : T, multichooseSeries (a b)) * multichooseSeries j =
        ∏ b : Option T, multichooseSeries (c b) := by
      rw [Fintype.prod_option, mul_comm]
      rfl
    rw [hprod, powerSeries_coeff_product]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Fintype.prod_option, mul_comm]
    simp only [multichooseSeries_coeff]
    rfl
  simp_rw [hcoeff]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.mul_sum]

theorem auxiliary_series_eq {T : Type*} [Fintype T] (a : T → ℕ)
    (n : ℕ) (ha : (∑ b, a b) ≤ n) :
    ((∏ b : T, multichooseSeries (a b)) *
      ∑ j ∈ Finset.range (n - (∑ b, a b) + 1), multichooseSeries j) =
      (PowerSeries.X : PowerSeries ℚ) ^ (demandSupport a).card *
        (PowerSeries.invOneSubPow ℚ (n + Fintype.card T + 1)).val := by
  have hsum : ((∑ b, a b) + Fintype.card T) + (n - (∑ b, a b) + 1) =
      n + Fintype.card T + 1 := by omega
  rw [product_multichooseSeries, sum_multichooseSeries, mul_assoc,
    ← Units.val_mul, ← PowerSeries.invOneSubPow_add, hsum]

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

noncomputable def rootEhrhartSeries : PowerSeries ℚ :=
  PowerSeries.mk fun t => (rootLatticeCount (E := E) t : ℚ)

omit [Fintype E] in
@[simp] theorem rootEhrhartSeries_coeff (t : ℕ) :
    PowerSeries.coeff t (rootEhrhartSeries (E := E)) =
      (rootLatticeCount (E := E) t : ℚ) := PowerSeries.coeff_mk _ _

theorem root_ehrhart_series_clone :
    rootEhrhartSeries (E := E) =
      ∑ d : demandVectors (fun b a : E => b ≤ a),
        ((∏ b : E, multichooseSeries (d.val b).val) *
          ∑ j ∈ Finset.range (Fintype.card E - (∑ b, (d.val b).val) + 1),
            multichooseSeries j) := by
  ext t
  rw [rootEhrhartSeries_coeff, rootLatticeCount_clone_formula]
  simp only [map_sum, auxiliary_series_coeff, Nat.cast_sum, Nat.cast_mul, Nat.cast_prod]
  rw [Finset.sum_comm]

theorem root_ehrhart_series_support :
    rootEhrhartSeries (E := E) =
      (supportEnumerator (fun b a : E => b ≤ a)).map (Nat.castRingHom ℚ) *
        (PowerSeries.invOneSubPow ℚ (2 * Fintype.card E + 1)).val := by
  rw [root_ehrhart_series_clone]
  have hterm : ∀ d : demandVectors (fun b a : E => b ≤ a),
      ((∏ b : E, multichooseSeries (d.val b).val) *
        ∑ j ∈ Finset.range (Fintype.card E - (∑ b, (d.val b).val) + 1),
          multichooseSeries j) =
        (PowerSeries.X : PowerSeries ℚ) ^ (demandSupport (fun b => (d.val b).val)).card *
          (PowerSeries.invOneSubPow ℚ (2 * Fintype.card E + 1)).val := by
    intro d
    have hd := demand_total_bound (Finset.mem_filter.mp d.property).2
    simpa only [two_mul] using auxiliary_series_eq
      (fun b => (d.val b).val) (Fintype.card E) hd
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  congr 1
  change _ = Polynomial.coeToPowerSeries.ringHom
    ((supportEnumerator (fun b a : E => b ≤ a)).map (Nat.castRingHom ℚ))
  rw [supportEnumerator]
  simp only [Polynomial.map_sum, Polynomial.map_pow, Polynomial.map_X, map_sum,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_pow, Polynomial.coe_X]
  exact Finset.sum_coe_sort (demandVectors (fun b a : E => b ≤ a))
    (fun d => (PowerSeries.X : PowerSeries ℚ) ^
      (demandSupport (fun b => (d b).val)).card)

theorem root_ehrhart_series :
    rootEhrhartSeries (E := E) =
      (supportPolynomial (E := E)).map (Nat.castRingHom ℚ) *
        (PowerSeries.invOneSubPow ℚ (2 * Fintype.card E + 1)).val := by
  rw [root_ehrhart_series_support, supportPolynomial_eq_preorderEnumerator,
    supportEnumerator_transpose (fun a b : E => b ≤ a)]

theorem root_ehrhart_numerator :
    rootEhrhartSeries (E := E) *
      (1 - PowerSeries.X : PowerSeries ℚ) ^ (2 * Fintype.card E + 1) =
        ((supportPolynomial (E := E)).map (Nat.castRingHom ℚ) : PowerSeries ℚ) := by
  rw [root_ehrhart_series, mul_assoc,
    ← PowerSeries.invOneSubPow_inv_eq_one_sub_pow,
    Units.val_inv, mul_one]

theorem root_ehrhart_gamma_expansion :
    rootEhrhartSeries (E := E) *
      (1 - PowerSeries.X : PowerSeries ℚ) ^ (2 * Fintype.card E + 1) =
        ((∑ k ∈ Finset.range (Fintype.card E / 2 + 1),
          Polynomial.C (gammaCoefficient (E := E) k) * Polynomial.X ^ k *
            (1 + Polynomial.X) ^ (Fintype.card E - 2 * k)).map
              (Nat.castRingHom ℚ) : PowerSeries ℚ) := by
  rw [root_ehrhart_numerator, preorder_gamma_expansion]

end ResearchMain.PreorderGamma
