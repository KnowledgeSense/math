import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

def euclideanQuadratic (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) : ℝ :=
  ∑ i, ∑ j, x i * A i j * x j

def leastQuadratic (A : Matrix n n ℝ) : ℝ :=
  sInf (euclideanQuadratic A '' Metric.sphere (0 : EuclideanSpace ℝ n) 1)

omit [DecidableEq n] [Nonempty n] in
theorem euclideanQuadratic_eq_dotProduct (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) :
    euclideanQuadratic A x = dotProduct (star (fun i => x i))
      (A.mulVec (fun i => x i)) := by
  simp [euclideanQuadratic, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

omit [DecidableEq n] [Nonempty n] in
theorem euclideanQuadratic_smul (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) (t : ℝ) :
    euclideanQuadratic A (t • x) = t ^ 2 * euclideanQuadratic A x := by
  simp only [euclideanQuadratic, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq n] [Nonempty n] in
theorem continuous_euclideanQuadratic [DecidableEq n] [Nonempty n] :
    Continuous (fun p : Matrix n n ℝ × EuclideanSpace ℝ n => euclideanQuadratic p.1 p.2) := by
  unfold euclideanQuadratic
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  have hi : Continuous (fun p : Matrix n n ℝ × EuclideanSpace ℝ n => p.2 i) :=
    (PiLp.continuous_apply 2 (fun _ : n => ℝ) i).comp continuous_snd
  have hj : Continuous (fun p : Matrix n n ℝ × EuclideanSpace ℝ n => p.2 j) :=
    (PiLp.continuous_apply 2 (fun _ : n => ℝ) j).comp continuous_snd
  exact (hi.mul (by fun_prop)).mul hj

theorem continuous_leastQuadratic : Continuous (leastQuadratic (n := n)) :=
  (isCompact_sphere (0 : EuclideanSpace ℝ n) 1).continuous_sInf continuous_euclideanQuadratic

theorem exists_leastQuadratic (A : Matrix n n ℝ) :
    ∃ x : EuclideanSpace ℝ n, ‖x‖ = 1 ∧ leastQuadratic A = euclideanQuadratic A x ∧
      ∀ y : EuclideanSpace ℝ n, ‖y‖ = 1 → euclideanQuadratic A x ≤ euclideanQuadratic A y := by
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ n) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  obtain ⟨x, hx, he, hmin⟩ := (isCompact_sphere (0 : EuclideanSpace ℝ n) 1).exists_sInf_image_eq_and_le hne
      (continuous_euclideanQuadratic.comp (continuous_const.prodMk continuous_id)).continuousOn
  refine ⟨x, ?_, he, ?_⟩
  · simpa only [Metric.mem_sphere, dist_zero_right] using hx
  · intro y hy
    exact hmin y (by simpa only [Metric.mem_sphere, dist_zero_right] using hy)

theorem leastQuadratic_le (A : Matrix n n ℝ) (x : EuclideanSpace ℝ n) (hx : ‖x‖ = 1) :
    leastQuadratic A ≤ euclideanQuadratic A x := by
  obtain ⟨y, _, he, hmin⟩ := exists_leastQuadratic A
  rw [he]
  exact hmin x hx

theorem posDef_leastQuadratic_pos (A : Matrix n n ℝ) (hA : A.PosDef) :
    0 < leastQuadratic A := by
  obtain ⟨x, hx, he, _⟩ := exists_leastQuadratic A
  have hx0 : (fun i => x i) ≠ 0 := by
    intro h
    have hz : x = 0 := by ext i; exact congrFun h i
    rw [hz, norm_zero] at hx
    norm_num at hx
  rw [he, euclideanQuadratic_eq_dotProduct]
  exact hA.dotProduct_mulVec_pos hx0

theorem posSemidef_of_leastQuadratic_nonneg (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hmin : 0 ≤ leastQuadratic A) : A.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA
  intro v
  by_cases hv : v = 0
  · simp [hv]
  · let x : EuclideanSpace ℝ n := WithLp.toLp 2 v
    have hx : x ≠ 0 := by
      intro h
      apply hv
      funext i
      exact congrArg (fun y : EuclideanSpace ℝ n => y i) h
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have he := leastQuadratic_le A ((‖x‖⁻¹ : ℝ) • x) hunit
    rw [euclideanQuadratic_smul] at he
    have hq : 0 ≤ euclideanQuadratic A x := by
      have ht : 0 < (‖x‖⁻¹ : ℝ) ^ 2 := sq_pos_of_pos (inv_pos.mpr hn)
      exact nonneg_of_mul_nonneg_right (hmin.trans he) ht
    simpa only [euclideanQuadratic_eq_dotProduct, x, PiLp.toLp_apply] using hq

theorem posDef_of_leastQuadratic_pos (A : Matrix n n ℝ) (hA : A.IsHermitian)
    (hmin : 0 < leastQuadratic A) : A.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hA
  intro v hv
  let x : EuclideanSpace ℝ n := WithLp.toLp 2 v
  have hx : x ≠ 0 := by
    intro h
    apply hv
    funext i
    exact congrArg (fun y : EuclideanSpace ℝ n => y i) h
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
  have he := leastQuadratic_le A ((‖x‖⁻¹ : ℝ) • x) hunit
  rw [euclideanQuadratic_smul] at he
  have hq : 0 < euclideanQuadratic A x :=
    pos_of_mul_pos_right (hmin.trans_le he) (sq_nonneg _)
  simpa only [euclideanQuadratic_eq_dotProduct, x, PiLp.toLp_apply] using hq

theorem positiveDefinite_continuation {S : Type*} [TopologicalSpace S] {s : Set S}
    (hs : IsPreconnected s) (F : S → Matrix n n ℝ) (hF : ContinuousOn F s)
    (hHermitian : ∀ x ∈ s, (F x).IsHermitian) (hdet : ∀ x ∈ s, (F x).det ≠ 0)
    {x0 : S} (hx0 : x0 ∈ s) (hbase : (F x0).PosDef) : ∀ x ∈ s, (F x).PosDef := by
  have hminContinuous : ContinuousOn (fun x => leastQuadratic (F x)) s :=
    continuous_leastQuadratic.comp_continuousOn hF
  have hminNonzero : ∀ x ∈ s, leastQuadratic (F x) ≠ 0 := by
    intro x hx hz
    have hps := posSemidef_of_leastQuadratic_nonneg (F x) (hHermitian x hx) (by rw [hz])
    have hpd := hps.posDef_iff_det_ne_zero.mpr (hdet x hx)
    have hp := posDef_leastQuadratic_pos (F x) hpd
    rw [hz] at hp
    exact (lt_irrefl (0 : ℝ)) hp
  have hbaseMin := posDef_leastQuadratic_pos (F x0) hbase
  intro x hx
  apply posDef_of_leastQuadratic_pos (F x) (hHermitian x hx)
  by_contra h
  have hxMin : leastQuadratic (F x) ≤ 0 := not_lt.mp h
  obtain ⟨y, hy, he⟩ := hs.intermediate_value hx hx0 hminContinuous ⟨hxMin, hbaseMin.le⟩
  exact hminNonzero y hy he

end

end ResearchMain.DiagonalSchatten
