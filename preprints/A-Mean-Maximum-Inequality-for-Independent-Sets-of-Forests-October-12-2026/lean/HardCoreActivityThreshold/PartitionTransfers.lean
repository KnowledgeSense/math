import HardCoreActivityThreshold.CurvaturePair
import HardCoreActivityThreshold.PartitionContinuity
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import HardCoreActivityThreshold.SecondDerivativeTest

namespace HardCoreActivityThreshold

noncomputable def transferFunction (u v t : ℝ) : ℝ :=
  scalarPartitionFunction (u+t)+scalarPartitionFunction (v-t)
noncomputable def transferFirst (u v t : ℝ) : ℝ :=
  firstPartitionDerivative (u+t)-firstPartitionDerivative (v-t)
noncomputable def transferSecond (u v t : ℝ) : ℝ :=
  secondPartitionDerivative (u+t)+secondPartitionDerivative (v-t)

theorem transferFunction_hasDerivAt (u v t : ℝ) (hu : 0<u+t) (hv : 0<v-t) :
    HasDerivAt (transferFunction u v) (transferFirst u v t) t := by
  have h1 := (partitionFunction_hasDerivAt (u+t) hu).comp t ((hasDerivAt_id t).const_add u)
  have h2 := (partitionFunction_hasDerivAt (v-t) hv).comp t ((hasDerivAt_const t v).sub (hasDerivAt_id t))
  convert h1.add h2 using 1
  · rfl
  · simp [transferFirst,sub_eq_add_neg]

theorem transferFirst_hasDerivAt (u v t : ℝ) (hu : 0<u+t) (hv : 0<v-t) :
    HasDerivAt (transferFirst u v) (transferSecond u v t) t := by
  have h1 := (firstPartitionDerivative_hasDerivAt (u+t) hu).comp t ((hasDerivAt_id t).const_add u)
  have h2 := (firstPartitionDerivative_hasDerivAt (v-t) hv).comp t ((hasDerivAt_const t v).sub (hasDerivAt_id t))
  convert h1.sub h2 using 1
  · rfl
  · simp [transferSecond]

theorem transferSecond_continuousAt (u v t : ℝ) (hu : 0<u+t) (hv : 0<v-t) :
    ContinuousAt (transferSecond u v) t := by
  exact ((secondPartitionDerivative_hasDerivAt (u+t) hu).continuousAt.comp
    (continuousAt_const.add continuousAt_id)).add
    ((secondPartitionDerivative_hasDerivAt (v-t) hv).continuousAt.comp
      (continuousAt_const.sub continuousAt_id))

theorem transfer_max_first_equal (u v : ℝ) (hu : 0<u) (hv : 0<v)
    (hm : IsLocalMax (transferFunction u v) 0) :
    firstPartitionDerivative u=firstPartitionDerivative v := by
  have hd := transferFunction_hasDerivAt u v 0 (by simpa) (by simpa)
  have h := hm.hasDerivAt_eq_zero hd
  simpa [transferFirst,sub_eq_zero] using h

theorem transfer_local_max_equal (u v : ℝ) (hu : u∈Set.Ioo 0 concavityEndpoint)
    (hv : v∈Set.Ioo 0 concavityEndpoint) (hm : IsLocalMax (transferFunction u v) 0) : u=v := by
  have he := transfer_max_first_equal u v hu.1 hv.1 hm
  by_contra hne
  have hp : 0<transferSecond u v 0 := by
    simp only [transferSecond,add_zero,sub_zero]
    rcases lt_or_gt_of_ne hne with h | h
    · exact curvature_pair_positive u v hu.1 h hv.2.le he
    · have h' := curvature_pair_positive v u hv.1 h hu.2.le he.symm
      linarith
  let b : ℝ := min u v/2
  have hb : 0<b := div_pos (lt_min hu.1 hv.1) (by norm_num)
  have hadm : ∀t∈Set.Ioo (-b) b,0<u+t ∧ 0<v-t := by
    intro t ht
    have hbu : b≤u/2 := div_le_div_of_nonneg_right (min_le_left u v) (by norm_num)
    have hbv : b≤v/2 := div_le_div_of_nonneg_right (min_le_right u v) (by norm_num)
    constructor <;> linarith [ht.1,ht.2,hu.1,hv.1]
  apply not_local_max_of_positive_second_derivative (transferFunction u v)
    (transferFirst u v) (transferSecond u v) b hb
    (fun t ht => transferFunction_hasDerivAt u v t (hadm t ht).1 (hadm t ht).2)
    (fun t ht => transferFirst_hasDerivAt u v t (hadm t ht).1 (hadm t ht).2)
    (transferSecond_continuousAt u v 0 (by simpa using hu.1) (by simpa using hv.1)) hp hm

end HardCoreActivityThreshold
