import HardCoreActivityThreshold.InnovationMatrix
import HardCoreActivityThreshold.MessageRecursion
import HardCoreActivityThreshold.WeightedColumnDecay
import HardCoreActivityThreshold.CubicPotential

/-! Actual parent-matrix column estimates from the hard-core message recursions. -/
namespace HardCoreActivityThreshold
open Finset Forest Matrix
attribute [local instance] Classical.propDecidable

theorem parentCorrelationMatrix_support (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (u v : A.Vertex)
    (h : parentCorrelationMatrix A activity ha u v ≠ 0) : forestParent A u = some v := by
  by_contra hn
  exact h (by simp [parentCorrelationMatrix, hn])

theorem parentCorrelationMatrix_unique (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (u v w : A.Vertex)
    (hv : parentCorrelationMatrix A activity ha u v ≠ 0)
    (hw : parentCorrelationMatrix A activity ha u w ≠ 0) : v = w :=
  Option.some.inj ((parentCorrelationMatrix_support A activity ha u v hv).symm.trans
    (parentCorrelationMatrix_support A activity ha u w hw))

theorem parentCorrelationMatrix_nilpotent (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) :
    parentCorrelationMatrix A activity ha ^ (univ.sup A.depth + 1) = 0 := by
  apply parent_matrix_nilpotent _ A.depth
  · intro u v huv
    have hd := forestParent_depth A u v (parentCorrelationMatrix_support A activity ha u v huv)
    omega
  · intro u
    have hd := Finset.le_sup (f := A.depth) (mem_univ u)
    omega

theorem parentCorrelationMatrix_square (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (u v : A.Vertex) :
    (parentCorrelationMatrix A activity ha u v)^2 =
      if forestParent A u = some v then
        (vertexMessage A activity u)^2 * occupationVariance (forestHC A activity ha) v /
          occupationVariance (forestHC A activity ha) u else 0 := by
  have hvar (w : A.Vertex) : 0 < occupationVariance (forestHC A activity ha) w := hardCore_occupation_variance_pos _ _ ha w
  unfold parentCorrelationMatrix
  simp only [Matrix.of_apply]
  split_ifs
  · rw [div_pow, mul_pow, neg_sq, Real.sq_sqrt (hvar v).le, Real.sq_sqrt (hvar u).le]
  · simp

noncomputable def forestPotentialWeight (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) : ℝ :=
  occupationVariance (forestHC A activity ha) v * potential (vertexLogPotential A activity v)

theorem parentColumn_square_sum (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    (∑ u, (parentCorrelationMatrix A activity ha u v)^2) =
      occupationVariance (forestHC A activity ha) v *
        childSum A (fun u => (vertexMessage A activity u)^2 / occupationVariance (forestHC A activity ha) u) v := by
  simp only [parentCorrelationMatrix_square, childSum, mul_sum]
  apply sum_congr rfl
  intro u _
  split_ifs <;> ring

theorem parentColumn_weighted_sum (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) (v : A.Vertex) :
    (∑ u, (parentCorrelationMatrix A activity ha u v)^2 * forestPotentialWeight A activity ha u) =
      occupationVariance (forestHC A activity ha) v *
        childSum A (fun u => (vertexMessage A activity u)^2 * potential (vertexLogPotential A activity u)) v := by
  simp only [parentCorrelationMatrix_square, forestPotentialWeight, childSum, mul_sum]
  apply sum_congr rfl
  intro u _
  have hs : occupationVariance (forestHC A activity ha) u ≠ 0 := (hardCore_occupation_variance_pos _ _ ha u).ne'
  split_ifs
  · field_simp
  · ring

theorem parentColumn_first_bound (A : ForestExpr) (activity : A.Vertex → ℝ)
    (ha : ∀ v, 0 < activity v) {Λ : ℝ} (hΛ : 0 < Λ) (hcap : ∀ v, activity v ≤ Λ) (v : A.Vertex) :
    (∑ u, (parentCorrelationMatrix A activity ha u v)^2) ≤
      (1+Λ)^2 * forestPotentialWeight A activity ha v := by
  have hlocal (u : A.Vertex) : (vertexMessage A activity u)^2 /
      occupationVariance (forestHC A activity ha) u ≤ (1+Λ)^2 * vertexMessage A activity u := by
    have hq := (vertexMessage_mem_Ioo A activity ha u).1
    have hs := (div_le_iff₀ (by positivity : 0 < (1+Λ)^2)).mp
      (forest_variance_message_lower A activity ha hΛ hcap u)
    apply (div_le_iff₀ (hardCore_occupation_variance_pos _ _ ha u)).mpr
    have hm := mul_le_mul_of_nonneg_left hs hq.le
    unfold occupationVariance at hs hm
    nlinarith
  rw [parentColumn_square_sum]
  have hs : childSum A (fun u => (vertexMessage A activity u)^2 / occupationVariance (forestHC A activity ha) u) v ≤
      (1+Λ)^2 * childSum A (vertexMessage A activity) v := by
    unfold childSum
    rw [mul_sum]
    apply sum_le_sum
    intro u _
    split_ifs
    · exact hlocal u
    · simp
  have hy := childSum_messages_le_logPotential A activity ha v
  have hphi : vertexLogPotential A activity v ≤ potential (vertexLogPotential A activity v) :=
    cubicPotential_ge _ _ (vertexLogPotential_nonneg A activity ha v)
  have he := hs.trans (mul_le_mul_of_nonneg_left (hy.trans hphi) (sq_nonneg _))
  have hv : 0 ≤ occupationVariance (forestHC A activity ha) v := (hardCore_occupation_variance_pos _ _ ha v).le
  have hm := mul_le_mul_of_nonneg_left he hv
  unfold forestPotentialWeight
  convert hm using 1; ring

end HardCoreActivityThreshold
