import MainTheorems.Chollet.StrictBorder
import MainTheorems.Chollet.CoefficientCongruence
import MainTheorems.Chollet.RankCoefficients.DDCoefficient

noncomputable section

namespace ResearchMain.Chollet

variable {I : Type*} [Fintype I] [LinearOrder I]

theorem positive_border_coefficient_bound {a : ℝ} {z : I → ℂ}
    {B : Matrix I I ℂ} (hA : ComparisonPD (border a z B)) (ha : 0 < a)
    (k : ℕ) (hk : 1 ≤ k) :
    rankCoefficient B (normalizedBorder a z) k ≤
      rankCoefficient B (normalizedBorder a z) 1 ∧
    rankCoefficient B (normalizedBorder a z) 1 ≤
      rankCoefficient B (normalizedBorder a z) 0 := by
  obtain ⟨d, hd, hm, hrow⟩ := positive_border_dominance hA
  let s := d (Sum.inl ())
  let e : I → ℝ := fun i => d (Sum.inr i)
  let a' := s ^ 2 * a
  let z' : I → ℂ := fun i => ((s * e i : ℝ) : ℂ) * z i
  let B' := scaledMatrix B e
  have hs : 0 < s := hd (Sum.inl ())
  have he : ∀ i, 0 < e i := fun i => hd (Sum.inr i)
  have ha' : 0 < a' := mul_pos (sq_pos_of_pos hs) ha
  have hB : B.IsHermitian := hA.1.submatrix Sum.inr
  have hB' : B'.IsHermitian := scaledMatrix_hermitian hB e
  have hrem : ∀ i, ‖z' i‖ ≤ ddRemainder B' i := by
    intro i
    have h := (hrow i).le
    change ‖z' i‖ + (∑ j ∈ Finset.univ.erase i, ‖B' i j‖) ≤ (B' i i).re at h
    exact (le_sub_iff_add_le).mpr h
  have hmass : ∑ i, ‖z' i‖ ≤ a' := hm.le
  have h := RankCoefficients.dd_coefficient_bound B' hB' a' z' ha' hrem hmass k hk
  have hnorm : normalizedBorder a' z' =
      fun i => (e i : ℂ) * normalizedBorder a z i :=
    normalizedBorder_scaled a z s hs e
  rw [hnorm] at h
  exact ⟨rankCoefficient_le_of_congruence B _ e he k 1 h.1,
    rankCoefficient_le_of_congruence B _ e he 1 0 h.2⟩

end ResearchMain.Chollet
