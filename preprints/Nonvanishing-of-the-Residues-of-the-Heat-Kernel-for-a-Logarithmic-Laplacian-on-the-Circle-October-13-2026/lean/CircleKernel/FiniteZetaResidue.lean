import CircleKernel.ZetaResidue

noncomputable section
open Filter Finset
open scoped Topology
namespace CircleKernel

theorem weighted_zeta_residue (m j : ℕ) :
    Tendsto (fun t : ℂ => (t-polePoint m)*(complexResiduePolynomial j).eval t*riemannZeta (2*t+j))
      (𝓝[≠] polePoint m)
      (𝓝 (if j=2*m then (complexResiduePolynomial j).eval (polePoint m)/2 else 0)) := by
  have hp := (complexResiduePolynomial j).continuous.continuousAt.tendsto.mono_left
    (nhdsWithin_le_nhds (a := polePoint m) (s := ({polePoint m}ᶜ : Set ℂ)))
  by_cases hj : j=2*m
  · subst j
    rw [ite_eq_left rfl]
    have h := hp.mul (shifted_zeta_residue (polePoint m) (2*m) (polePoint_shift m))
    simp only [mul_one_div] at h
    apply h.congr'
    apply Filter.Eventually.of_forall
    intro t
    ring
  · rw [ite_eq_right hj]
    have hz := ((differentiableAt_riemannZeta (polePoint_shift_ne m j hj)).continuousAt.comp (f := fun t : ℂ => 2*t+j)
      (show ContinuousAt (fun t : ℂ => 2*t+j) (polePoint m) by fun_prop)).tendsto.mono_left
        (nhdsWithin_le_nhds (a := polePoint m) (s := ({polePoint m}ᶜ : Set ℂ)))
    have ht := (tendsto_id.sub_const (polePoint m)).mono_left
      (nhdsWithin_le_nhds (a := polePoint m) (s := ({polePoint m}ᶜ : Set ℂ)))
    simpa only [sub_self, zero_mul, Function.comp_apply, id_eq] using (ht.mul hp).mul hz

theorem finite_zeta_residue (m M : ℕ) (hM : 2*m < M) :
    Tendsto (fun t : ℂ => (t-polePoint m)*
      (∑ j ∈ range M, (complexResiduePolynomial j).eval t*riemannZeta (2*t+j)))
      (𝓝[≠] polePoint m) (𝓝 ((complexResiduePolynomial (2*m)).eval (polePoint m)/2)) := by
  have h := tendsto_finsetSum (range M) (fun j _ => weighted_zeta_residue m j)
  have hs : (∑ j ∈ range M,
      if j=2*m then (complexResiduePolynomial j).eval (polePoint m)/2 else 0) =
        (complexResiduePolynomial (2*m)).eval (polePoint m)/2 := by simp [hM]
  rw [hs] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  ring

end CircleKernel
