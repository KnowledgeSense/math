import MainTheorems.DiagonalSchatten.StationaryMaximum
import MainTheorems.DiagonalSchatten.RayKeys
import MainTheorems.DiagonalSchatten.ThreeRayObjective

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

namespace RayParameters

variable (g : RayParameters)

theorem finite_ray_bound (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (hc : 0 < gramCross X)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2)
    (s R : ℝ)
    (hD : ∀ x, 0 ≤ x 0 → 0 ≤ x 1 → (0 < x 0 ∨ 0 < x 1) → g.denominator x ≠ 0)
    (hTwo : ∀ T : Matrix (Fin 2) (Fin 2) ℝ, (∀ i j, 0 ≤ T i j) →
      gramFirst T = gramFirst X → gramSecond T = gramSecond X → gramCross T = gramCross X →
      columnObjective (fun x => s * g.functional x) T ≤ R)
    (hThree : ∀ r ∈ Set.Icc (gramCross X / gramFirst X) (gramSecond X / gramCross X),
      (gramFirst X - gramCross X / r) * (s * g.functional ![1, 0]) +
        (gramSecond X - gramCross X * r) * (s * g.functional ![0, 1]) +
        (gramCross X / r) * (s * g.functional ![1, r]) ≤ R) :
    columnObjective (fun x => s * g.functional x) X ≤ R := by
  classical
  have hmem : X ∈ gramFiber (gramFirst X) (gramSecond X) (gramCross X) :=
    ⟨hX, rfl, rfl, rfl⟩
  obtain ⟨Y, hY, hmax, hcase⟩ := g.stationary_maximum_reduction s ⟨X, hmem⟩ hc hdet hD
  apply (hmax X hmem).trans
  have hcy : 0 < gramCross Y := by rw [hY.2.2.2]; exact hc
  have hdy : 0 < gramFirst Y * gramSecond Y - gramCross Y ^ 2 := by
    rw [hY.2.1, hY.2.2.1, hY.2.2.2]
    exact hdet
  rcases hcase with (hcount | ⟨hslopes, _, _⟩) | ⟨T, hT, ha, hb, hcT, he⟩
  · obtain ⟨j, hj0, hj1⟩ := exists_interior_column Y hY.1 hcy
    have hw : columnRayWeight Y j ≠ 0 := by
      simp only [columnRayWeight, hj0.ne', ite_false]
      exact pow_ne_zero 2 hj0.ne'
    have hne : (rayKeys Y).Nonempty := ⟨_, columnRayKey_mem Y hY.1 j hw⟩
    obtain ⟨T, hT, ha, hb, hcT, he⟩ := ray_support_two_replacement Y hY.1 hne hcount
      (fun x => s * g.functional x) (g.signed_functional_homogeneous s)
    rw [← he]
    exact hTwo T hT (ha.trans hY.2.1) (hb.trans hY.2.2.1) (hcT.trans hY.2.2.2)
  · obtain ⟨r, hr, hsr⟩ := one_interior_slope Y hslopes
    have hb : 0 ≤ gramSecond Y := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have ha : 0 < gramFirst Y := by
      by_contra hn
      have hm : gramFirst Y * gramSecond Y ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hn) hb
      nlinarith [sq_nonneg (gramCross Y)]
    have hi := three_ray_slope_interval Y hY.1 hr ha hcy hsr
    rw [three_ray_objective Y hY.1 hr hsr (fun x => s * g.functional x)
      (g.signed_functional_homogeneous s), hY.2.1, hY.2.2.1, hY.2.2.2]
    apply hThree r
    simpa only [Set.mem_Icc, hY.2.1, hY.2.2.1, hY.2.2.2] using hi
  · rw [← he]
    exact hTwo T hT ha hb hcT

end RayParameters

end

end ResearchMain.DiagonalSchatten
