import Dowling.DowlingMixtureStrict

noncomputable section
namespace Dowling

/-- The exact rational base curvature pays an arithmetic-mean square without logarithms. -/
theorem dowling_curvature_factor {A B : ℝ} (hA : 0<A) (hA1 : A<1)
    (hB : 0<B) (hB1 : B<1) :
    (1+(A+B)/2)^2*((1-A)*(1-B))<1 := by
  let y := (A+B)/2
  have hy : 0<y := by dsimp [y]; linarith
  have hy1 : y<1 := by dsimp [y]; linarith
  have hbase : (1-A)*(1-B)≤(1-y)^2 := by
    dsimp [y]
    nlinarith [sq_nonneg (A-B)]
  have hmul := mul_le_mul_of_nonneg_left hbase (sq_nonneg (1+y))
  have heq : (1+y)^2*(1-y)^2=(1-y^2)^2 := by ring
  rw [heq] at hmul
  have hy2 : 0<y^2 := sq_pos_of_pos hy
  have hy21 : y^2<1 := by nlinarith
  change (1+y)^2*((1-A)*(1-B))<1
  exact hmul.trans_lt (by nlinarith [sq_nonneg (1-y^2)])

/-- A normalized second-difference budget implies strict log-concavity of the actual weighted triple. -/
theorem dowling_curvature_payment {A B um uc up qm qc qp : ℝ}
    (hA : 0<A) (hA1 : A<1) (hB : 0<B) (hB1 : B<1)
    (hum : 0<um) (huc : 0<uc) (hup : 0<up)
    (hqm : 0≤qm) (hqc : 0<qc) (hqp : 0≤qp)
    (hbase : um*up=(1-A)*(1-B)*uc^2)
    (hbudget : qm+qp-2*qc≤(A+B)*qc) :
    (um*qm)*(up*qp)<(uc*qc)^2 := by
  let y := (A+B)/2
  have hy : 0<y := by dsimp [y]; linarith
  have hsum : qm+qp≤2*(1+y)*qc := by dsimp [y]; linarith
  have hsum2 : (qm+qp)^2≤(2*(1+y)*qc)^2 :=
    (sq_le_sq₀ (by positivity) (by positivity)).mpr hsum
  have hq : qm*qp≤(1+y)^2*qc^2 := by nlinarith [sq_nonneg (qm-qp)]
  have hscale : 0<um*up := mul_pos hum hup
  have hprod := mul_le_mul_of_nonneg_left hq hscale.le
  have hf := dowling_curvature_factor hA hA1 hB hB1
  change (1+y)^2*((1-A)*(1-B))<1 at hf
  have hstrict := mul_lt_mul_of_pos_right hf (mul_pos (sq_pos_of_pos huc) (sq_pos_of_pos hqc))
  rw [hbase] at hprod
  nlinarith [hprod,hstrict]

/-- Every convex interpolation with the constant normalized row preserves the same budget. -/
theorem dowling_interpolated_budget {qm qc qp θ L : ℝ}
    (hθ : 0≤θ) (hθ1 : θ≤1) (hL : 0≤L)
    (h : qm+qp-2*qc≤L*qc) :
    (1-θ+θ*qm)+(1-θ+θ*qp)-2*(1-θ+θ*qc)≤L*(1-θ+θ*qc) := by
  have hmul := mul_le_mul_of_nonneg_left h hθ
  have hrest : 0≤L*(1-θ) := mul_nonneg hL (by linarith)
  nlinarith

 theorem dowling_interpolated_pos {q θ : ℝ} (hq : 0<q) (hθ : 0≤θ) (hθ1 : θ≤1) :
    0<1-θ+θ*q := by
  by_cases ht : θ=1
  · simp [ht,hq]
  · have hfirst : 0<1-θ := sub_pos.mpr (lt_of_le_of_ne hθ1 ht)
    have hlast : 0≤θ*q := mul_nonneg hθ hq.le
    linarith

end Dowling
