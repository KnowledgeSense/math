import CircleKernel.HolomorphicLocus

noncomputable section
open Filter
open scoped Topology
namespace CircleKernel

theorem shifted_zeta_residue (a : ℂ) (j : ℕ) (ha : 2*a+(j : ℂ)=1) :
    Tendsto (fun t : ℂ => (t-a)*riemannZeta (2*t+j)) (𝓝[≠] a) (𝓝 (1/2 : ℂ)) := by
  have hc : Tendsto (fun t : ℂ => 2*t+j) (𝓝[≠] a) (𝓝 (1 : ℂ)) := by
    rw [← ha]
    exact (show Continuous (fun t : ℂ => 2*t+j) by fun_prop).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hm : Tendsto (fun t : ℂ => 2*t+j) (𝓝[≠] a) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hc,?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at ht ⊢
    intro he
    apply ht
    linear_combination (1/2 : ℂ)*(he-ha)
  have h := (riemannZeta_residue_one.comp hm).const_mul (1/2 : ℂ)
  simp only [mul_one] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro t
  dsimp only [Function.comp_def]
  have he : 2*t+(j : ℂ)-1 = 2*(t-a) := by linear_combination ha
  rw [he]
  ring

theorem polePoint_shift (m : ℕ) : 2*polePoint m+(2*m : ℕ)=1 := by
  simp only [polePoint, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem polePoint_shift_ne (m j : ℕ) (hj : j ≠ 2*m) : 2*polePoint m+(j : ℂ) ≠ 1 := by
  intro h
  apply hj
  have he : (j : ℂ) = ((2*m : ℕ) : ℂ) := by linear_combination h-polePoint_shift m
  exact_mod_cast he

end CircleKernel
