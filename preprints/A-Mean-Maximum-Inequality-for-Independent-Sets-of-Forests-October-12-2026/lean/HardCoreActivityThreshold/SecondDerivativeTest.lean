import HardCoreActivityThreshold.CurvatureConvexity
import Mathlib.Analysis.Calculus.LocalExtr.Basic

namespace HardCoreActivityThreshold

open Set Filter

theorem not_local_max_of_positive_second_derivative
    (f g h : ℝ → ℝ) (b : ℝ) (hb : 0<b)
    (hf : ∀t∈Ioo (-b) b,HasDerivAt f (g t) t)
    (hg : ∀t∈Ioo (-b) b,HasDerivAt g (h t) t)
    (hc : ContinuousAt h 0) (hp : 0<h 0) : ¬IsLocalMax f 0 := by
  intro hm
  have he : ∀ᶠt in nhds (0 : ℝ),f t≤f 0 ∧ 0<h t ∧ t∈Ioo (-b) b := by
    filter_upwards [hm,hc.eventually (lt_mem_nhds hp),Ioo_mem_nhds (by linarith : -b<0) hb] with t ht hh hi
    exact ⟨ht,hh,hi⟩
  obtain ⟨e,he0,he⟩ := Metric.eventually_nhds_iff.mp he
  have hall : ∀t∈Icc (-e/2) (e/2), f t≤f 0 ∧ 0<h t ∧ t∈Ioo (-b) b := by
    intro t ht
    apply he
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith [ht.1,ht.2]
  have hmG : StrictMonoOn g (Icc (-e/2) (e/2)) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    · intro t ht
      exact (hg t (hall t ht).2.2).continuousAt.continuousWithinAt
    · intro t ht
      have hi := hall t (interior_subset ht)
      rw [(hg t hi.2.2).deriv]
      exact hi.2.1
  have hcv : StrictConvexOn ℝ (Icc (-e/2) (e/2)) f := by
    apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc _ _)
    · intro t ht
      exact (hf t (hall t ht).2.2).continuousAt.continuousWithinAt
    · intro s hs t ht hst
      have his := interior_subset hs
      have hit := interior_subset ht
      rw [(hf s (hall s his).2.2).deriv,(hf t (hall t hit).2.2).deriv]
      exact hmG his hit hst
  have ha : -e/2∈Icc (-e/2) (e/2) := ⟨le_rfl,by linarith⟩
  have hz : e/2∈Icc (-e/2) (e/2) := ⟨by linarith,le_rfl⟩
  have hs := hcv.2 ha hz (by linarith : -e/2≠e/2)
    (by norm_num : (0 : ℝ)<1/2) (by norm_num : (0 : ℝ)<1/2) (by norm_num)
  simp only [smul_eq_mul] at hs
  have hmid : (1/2 : ℝ)*(-e/2)+(1/2)*(e/2)=0 := by ring
  rw [hmid] at hs
  linarith [(hall _ ha).1,(hall _ hz).1]

end HardCoreActivityThreshold
