import MainTheorems.DominationRoots.Brackets

namespace ResearchMain.DominationRoots

open Set

noncomputable def lowerRoot : ℝ := (3 - Real.sqrt 5) / 2

noncomputable def upperRoot : ℝ := (3 + Real.sqrt 5) / 2

theorem sqrt_five_bounds : 2 < Real.sqrt 5 ∧ Real.sqrt 5 < 9 / 4 := by
  have h0 := Real.sqrt_nonneg (5 : ℝ)
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  constructor <;> nlinarith

theorem lowerRoot_bounds : 3 / 8 < lowerRoot ∧ lowerRoot < 1 / 2 := by
  unfold lowerRoot
  have h := sqrt_five_bounds
  constructor <;> linarith [h.1, h.2]

theorem upperRoot_bounds : 5 / 2 < upperRoot ∧ upperRoot < 21 / 8 := by
  unfold upperRoot
  have h := sqrt_five_bounds
  constructor <;> linarith [h.1, h.2]

theorem quadratic_factor (x : ℝ) :
    quadratic 3 1 x = (x - lowerRoot) * (x - upperRoot) := by
  unfold quadratic lowerRoot upperRoot
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  nlinarith

theorem quadratic_eq_zero_iff (x : ℝ) :
    quadratic 3 1 x = 0 ↔ x = lowerRoot ∨ x = upperRoot := by
  rw [quadratic_factor, mul_eq_zero]
  simp only [sub_eq_zero]

noncomputable def component : Fin 5 → Set ℝ :=
  ![Ioo 0 lowerRoot, Ioo lowerRoot 1, Ioo 1 2, Ioo 2 upperRoot, Ioi upperRoot]

theorem component_convex (i : Fin 5) : Convex ℝ (component i) := by
  fin_cases i
  · exact convex_Ioo 0 lowerRoot
  · exact convex_Ioo lowerRoot 1
  · exact convex_Ioo 1 2
  · exact convex_Ioo 2 upperRoot
  · exact convex_Ioi upperRoot

theorem component_regular (i : Fin 5) (x : ℝ) (hx : x ∈ component i) : Regular x := by
  have hlo := lowerRoot_bounds
  have hhi := upperRoot_bounds
  unfold Regular
  have hq : quadratic 3 1 x ≠ 0 := by
    intro h
    rcases (quadratic_eq_zero_iff x).mp h with h | h
    all_goals subst x; fin_cases i <;> simp [component] at hx <;> grind
  refine ⟨?_, ?_, ?_, hq⟩
  all_goals fin_cases i <;> simp [component] at hx <;> grind

theorem brackets_in_components (i : Fin 5) :
    bracketLeft i ∈ component i ∧ bracketRight i ∈ component i := by
  have hlo := lowerRoot_bounds
  have hhi := upperRoot_bounds
  fin_cases i <;> norm_num [bracketLeft, bracketRight, component] <;>
    constructor <;> linarith [hlo.1, hlo.2, hhi.1, hhi.2]

theorem positive_regular_mem_component {x : ℝ} (hx : 0 < x) (hreg : Regular x) :
    ∃ i : Fin 5, x ∈ component i := by
  have hq := quadratic_eq_zero_iff x
  have hlo : x ≠ lowerRoot := fun h => hreg.2.2.2 (hq.mpr (Or.inl h))
  have hhi : x ≠ upperRoot := fun h => hreg.2.2.2 (hq.mpr (Or.inr h))
  by_cases h0 : x < lowerRoot
  · exact ⟨0, by simpa [component] using ⟨hx, h0⟩⟩
  by_cases h1 : x < 1
  · exact ⟨1, by simpa [component] using ⟨lt_of_le_of_ne (le_of_not_gt h0) hlo.symm, h1⟩⟩
  by_cases h2 : x < 2
  · exact ⟨2, by simpa [component] using
      ⟨lt_of_le_of_ne (le_of_not_gt h1) hreg.2.1.symm, h2⟩⟩
  by_cases h3 : x < upperRoot
  · exact ⟨3, by simpa [component] using
      ⟨lt_of_le_of_ne (le_of_not_gt h2) hreg.2.2.1.symm, h3⟩⟩
  exact ⟨4, by simpa [component] using
    lt_of_le_of_ne (le_of_not_gt h3) hhi.symm⟩

theorem auxiliary_inequality {x : ℝ} (hx : 0 < x) (hQ : auxiliaryQ x ≠ 0) :
    2 < x ^ 2 - x - Real.log |auxiliaryQ x| := by
  have hreg := (regular_iff_auxiliaryQ_ne_zero x).mpr hQ
  obtain ⟨i, hi⟩ := positive_regular_mem_component hx hreg
  have hb := brackets_in_components i
  have h := auxiliaryFunction_above_component (component_convex i) (component_regular i)
    hb.1 hb.2 (bracket_certificates i) x hi
  rwa [auxiliaryFunction_eq x hreg] at h

end ResearchMain.DominationRoots
