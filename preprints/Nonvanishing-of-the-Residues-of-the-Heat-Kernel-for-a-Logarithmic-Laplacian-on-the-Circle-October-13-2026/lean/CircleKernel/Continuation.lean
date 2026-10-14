import CircleKernel.RegularizedOverlap

noncomputable section
open Filter
open scoped Topology
namespace CircleKernel

theorem exists_regularization_order (t : ℂ) : ∃ M : ℕ, 0 < M ∧ 1 < 2*t.re+(M : ℝ) := by
  obtain ⟨M,hM⟩ := exists_nat_gt (max 0 (1-2*t.re))
  refine ⟨M,?_,?_⟩
  · have hp : (0 : ℝ) < M := lt_of_le_of_lt (le_max_left _ _) hM
    exact_mod_cast hp
  · have hp := lt_of_le_of_lt (le_max_right _ _) hM
    linarith

def regularizationOrder (t : ℂ) : ℕ := Classical.choose (exists_regularization_order t)

theorem regularizationOrder_spec (t : ℂ) :
    0 < regularizationOrder t ∧ 1 < 2*t.re+(regularizationOrder t : ℝ) :=
  Classical.choose_spec (exists_regularization_order t)

/-- The global continuation constructed from compatible genuine spectral remainders. -/
def continuedKernel (t : ℂ) : ℂ := regularizedKernel (regularizationOrder t) t

theorem continuedKernel_eq_regularized (M : ℕ) (hM : 0 < M) (t : ℂ)
    (ht : 1 < 2*t.re+(M : ℝ)) : continuedKernel t = regularizedKernel M t := by
  have hspec := regularizationOrder_spec t
  exact (regularizedKernel_overlap _ (max (regularizationOrder t) M) hspec.1
      (le_max_left _ _) t hspec.2).trans
    (regularizedKernel_overlap M _ hM (le_max_right _ _) t ht).symm

theorem continuedKernel_initial (t : ℂ) (ht : 1/2 < t.re) :
    continuedKernel t = diagonalSpectralKernel t :=
  regularizedKernel_initial _ t ht

theorem continuedKernel_eventuallyEq (M : ℕ) (hM : 0 < M) (t : ℂ)
    (ht : 1 < 2*t.re+(M : ℝ)) : continuedKernel =ᶠ[𝓝 t] regularizedKernel M := by
  have ho : IsOpen {w : ℂ | 1 < 2*w.re+(M : ℝ)} := isOpen_lt continuous_const (by fun_prop)
  filter_upwards [ho.mem_nhds ht] with w hw
  exact continuedKernel_eq_regularized M hM w hw

end CircleKernel
