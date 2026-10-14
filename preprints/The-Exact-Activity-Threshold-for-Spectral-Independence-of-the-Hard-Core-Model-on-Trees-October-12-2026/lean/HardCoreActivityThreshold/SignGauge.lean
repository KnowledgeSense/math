import HardCoreActivityThreshold.ParentMatrix
import HardCoreActivityThreshold.Correlation

namespace HardCoreActivityThreshold
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A diagonal sign change makes every actual correlation nonnegative. -/
def CorrelationSignable (μ : FiniteLaw (Finset V)) : Prop :=
  ∃ s : V → ℝ, (∀ v, s v * s v = 1) ∧
    ∀ u v, 0 ≤ s u * correlationMatrix μ u v * s v

noncomputable def signGauge (s : V → ℝ) (A : Matrix V V ℝ) : Matrix V V ℝ := diagonal s*A*diagonal s

theorem signGauge_entry (s : V → ℝ) (A : Matrix V V ℝ) (u v : V) :
    signGauge s A u v=s u*A u v*s v := by simp [signGauge,diagonal_mul,mul_diagonal]

theorem signGauge_one (s : V → ℝ) (hs : ∀v,s v*s v=1) : signGauge s 1=1 := by
  simp only [signGauge,mul_one,diagonal_mul_diagonal,hs,diagonal_one]

theorem signGauge_mul (s : V → ℝ) (hs : ∀v,s v*s v=1) (A B : Matrix V V ℝ) :
    signGauge s (A*B)=signGauge s A*signGauge s B := by
  have hJ : diagonal s*diagonal s=(1 : Matrix V V ℝ) := by
    simp only [diagonal_mul_diagonal,hs,diagonal_one]
  unfold signGauge
  symm
  calc
    _=diagonal s*A*(diagonal s*diagonal s)*B*diagonal s := by simp only [mul_assoc]
    _=diagonal s*(A*B)*diagonal s := by rw [hJ]; simp only [mul_one,mul_assoc]

theorem signGauge_pow (s : V → ℝ) (hs : ∀v,s v*s v=1) (A : Matrix V V ℝ) (h : ℕ) :
    signGauge s (A^h)=(signGauge s A)^h := by
  induction h with
  | zero => simp only [pow_zero,signGauge_one s hs]
  | succ h ih => rw [pow_succ,signGauge_mul s hs,ih,pow_succ]

theorem matrix_nonnegative_power (A : Matrix V V ℝ) (hA : ∀u v,0≤A u v) :
    ∀h : ℕ,∀u v,0≤(A^h) u v := by
  intro h
  induction h with
  | zero => intro u v; simp only [pow_zero,one_apply]; split_ifs <;> norm_num
  | succ h ih =>
    intro u v
    rw [pow_succ,mul_apply]
    exact sum_nonneg (fun w _ => mul_nonneg (ih u w) (hA w v))

omit [Fintype V] [DecidableEq V] in
theorem rank_sign_square (rank : V → ℕ) (v : V) :
    ((-1 : ℝ)^rank v)*((-1 : ℝ)^rank v)=1 := by rw [←mul_pow]; norm_num

theorem rank_sign_parent (B : Matrix V V ℝ) (rank : V → ℕ)
    (hrank : ∀u v,B u v≠0 → rank u=rank v+1) :
    signGauge (fun v => (-1 : ℝ)^rank v) B= -B := by
  ext u v
  rw [signGauge_entry]
  by_cases hz : B u v=0
  · simp [hz]
  · rw [hrank u v hz,pow_succ]
    have hs := rank_sign_square rank v
    change _ = -(B u v)
    calc
      _= -(B u v)*(((-1 : ℝ)^rank v)*((-1 : ℝ)^rank v)) := by ring
      _= -(B u v) := by rw [hs,mul_one]

 theorem rank_sign_geometric_nonnegative (B : Matrix V V ℝ) (rank : V → ℕ)
    (hrank : ∀u v,B u v≠0 → rank u=rank v+1) (hB : ∀u v,B u v≤0) (N : ℕ) :
    ∀u v,0≤signGauge (fun v => (-1 : ℝ)^rank v) (∑h : Fin (N+1),B^h.val) u v := by
  intro u v
  have he : signGauge (fun v => (-1 : ℝ)^rank v) (∑h : Fin (N+1),B^h.val)=
      ∑h : Fin (N+1),(-B)^h.val := by
    unfold signGauge
    rw [mul_sum,sum_mul]
    apply sum_congr rfl
    intro h _
    change signGauge _ (B^h.val)=_
    rw [signGauge_pow _ (rank_sign_square rank),rank_sign_parent B rank hrank]
  rw [he]
  simp only [Matrix.sum_apply]
  exact sum_nonneg (fun h _ => matrix_nonnegative_power (-B) (fun u v => neg_nonneg.mpr (hB u v)) h.val u v)

theorem signGauge_factor_nonnegative (s : V → ℝ) (hs : ∀v,s v*s v=1)
    (K : Matrix V V ℝ) (d : V → ℝ) (hd : ∀v,0≤d v)
    (hK : ∀u v,0≤signGauge s K u v) :
    ∀u v,0≤signGauge s (K*diagonal d*K.transpose) u v := by
  intro u v
  rw [signGauge_entry]
  have he : s u*(K*diagonal d*K.transpose) u v*s v=
      ∑w,signGauge s K u w*d w*signGauge s K v w := by
    rw [Matrix.mul_apply]
    simp only [mul_diagonal,transpose_apply,signGauge_entry,mul_sum,sum_mul]
    apply sum_congr rfl
    intro w _
    have hw := hs w
    calc
      s u*(K u w*d w*K v w)*s v=
          (s u*K u w*d w*s v*K v w)*(s w*s w) := by rw [hw,mul_one]; ring
      _=s u*K u w*s w*d w*(s v*K v w*s w) := by ring
  rw [he]
  exact sum_nonneg (fun w _ => mul_nonneg (mul_nonneg (hK u w) (hd w)) (hK v w))

 theorem absolute_eq_signGauge (s : V → ℝ) (hs : ∀v,s v*s v=1)
    (R : Matrix V V ℝ) (hR : ∀u v,0≤signGauge s R u v) :
    Matrix.of (fun u v => |R u v|)=signGauge s R := by
  ext u v
  have hu : |s u|=1 := by nlinarith [sq_abs (s u),abs_nonneg (s u),hs u]
  have hv : |s v|=1 := by nlinarith [sq_abs (s v),abs_nonneg (s v),hs v]
  have he := abs_of_nonneg (hR u v)
  rw [signGauge_entry,abs_mul,abs_mul,hu,hv,one_mul,mul_one] at he
  simpa only [Matrix.of_apply, signGauge_entry] using he

end HardCoreActivityThreshold
