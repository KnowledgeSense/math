import MainTheorems.WishartBlocks.BoxAssociation

namespace ResearchMain.WishartBlocks

open MeasureTheory
open scoped BigOperators Topology

def positiveOrthant (n : ℕ) : Set (Fin n → ℝ) := {x | ∀ i, 0 < x i}

def positiveBox (n N : ℕ) : Set (Fin n → ℝ) :=
  intervalLattice n (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1)

theorem positiveBox_monotone (n : ℕ) : Monotone (positiveBox n) := by
  intro N M hNM x hx
  have hNM' : (N : ℝ) + 1 ≤ (M : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hNM 1
  exact ⟨fun i => (one_div_le_one_div_of_le (by positivity) hNM').trans (hx.1 i),
    fun i => (hx.2 i).trans hNM'⟩

theorem positiveBox_union (n : ℕ) : (⋃ N, positiveBox n N) = positiveOrthant n := by
  ext x
  constructor
  · intro hx
    obtain ⟨N, hN⟩ := Set.mem_iUnion.mp hx
    intro i
    exact (by positivity : 0 < 1 / ((N : ℝ) + 1)).trans_le (hN.1 i)
  · intro hx
    have hall : ∀ i : Fin n, ∀ᶠ N : ℕ in Filter.atTop,
        1 / ((N : ℝ) + 1) ≤ x i ∧ x i ≤ (N : ℝ) + 1 := by
      intro i
      have hxi : 0 < x i := hx i
      obtain ⟨K, hK⟩ := exists_nat_ge (max (x i) (1 / x i))
      filter_upwards [Filter.eventually_ge_atTop K] with N hN
      have hKN : (K : ℝ) ≤ N := by exact_mod_cast hN
      have hl : 1 / x i ≤ (N : ℝ) + 1 :=
        (le_max_right _ _).trans (hK.trans (by linarith))
      have hu : x i ≤ (N : ℝ) + 1 :=
        (le_max_left _ _).trans (hK.trans (by linarith))
      have hd := one_div_le_one_div_of_le (by positivity : 0 < 1 / x i) hl
      exact ⟨by simpa using hd, hu⟩
    obtain ⟨N, hN⟩ := (Filter.eventually_all.mpr hall).exists
    exact Set.mem_iUnion.mpr ⟨N, ⟨fun i => (hN i).1, fun i => (hN i).2⟩⟩

theorem eigenvalueWeight_of_not_positive {n : ℕ} (α : ℝ) {x : Fin n → ℝ}
    (hx : x ∉ positiveOrthant n) : eigenvalueWeight α x = 0 := by
  unfold eigenvalueWeight chamberWeight
  rw [ite_eq_right (fun h => hx h.1)]

theorem positiveBox_integral_limit {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Integrable f)
    (hs : ∀ x, x ∉ positiveOrthant n → f x = 0) :
    Filter.Tendsto (fun N => ∫ x in positiveBox n N, f x) Filter.atTop (𝓝 (∫ x, f x)) := by
  have h := tendsto_setIntegral_of_monotone (s := positiveBox n)
    (fun N : ℕ => intervalLattice_measurable n (1 / ((N : ℝ) + 1)) ((N : ℝ) + 1))
    (positiveBox_monotone n) hf.integrableOn
  rw [positiveBox_union] at h
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hs] at h
  exact h

theorem eigenvalue_association {n : ℕ} (α : ℝ) {F G : (Fin n → ℝ) → ℝ}
    (hcF : Continuous F) (hcG : Continuous G)
    (hF : ∀ x, 0 ≤ F x) (hG : ∀ x, 0 ≤ G x)
    (hmF : Monotone F) (hmG : Monotone G)
    (hiμ : Integrable (eigenvalueWeight (n := n) α))
    (hiF : Integrable (fun x => eigenvalueWeight α x * F x))
    (hiG : Integrable (fun x => eigenvalueWeight α x * G x))
    (hiFG : Integrable (fun x => eigenvalueWeight α x * (F x * G x))) :
    (∫ x, eigenvalueWeight α x * F x) * (∫ x, eigenvalueWeight α x * G x) ≤
      (∫ x : Fin n → ℝ, eigenvalueWeight α x) *
        (∫ x, eigenvalueWeight α x * (F x * G x)) := by
  have hμ := positiveBox_integral_limit hiμ (fun x hx => eigenvalueWeight_of_not_positive α hx)
  have hlimF := positiveBox_integral_limit hiF (fun x hx => by
    rw [eigenvalueWeight_of_not_positive α hx, zero_mul])
  have hlimG := positiveBox_integral_limit hiG (fun x hx => by
    rw [eigenvalueWeight_of_not_positive α hx, zero_mul])
  have hlimFG := positiveBox_integral_limit hiFG (fun x hx => by
    rw [eigenvalueWeight_of_not_positive α hx, zero_mul])
  apply le_of_tendsto_of_tendsto (hlimF.mul hlimG) (hμ.mul hlimFG)
  exact Filter.Eventually.of_forall fun N =>
    eigenvalue_box_association α (by positivity : 0 < 1 / ((N : ℝ) + 1))
      hcF hcG hF hG hmF hmG

end ResearchMain.WishartBlocks
