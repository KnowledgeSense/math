import HardCoreActivityThreshold.PotentialEnvelope
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace HardCoreActivityThreshold
open Finset Matrix
variable {V : Type*} [Fintype V]

theorem sparse_square_sum (a x : V → ℝ)
    (ha : ∀v w,v≠w → a v*a w=0) :
    (∑v,a v*x v)^2=∑v,(a v)^2*(x v)^2 := by
  rw [sq,Fintype.sum_mul_sum]
  apply sum_congr rfl
  intro v _
  rw [sum_eq_single v]
  · ring
  · intro w _ hw
    have h := ha v w hw.symm
    calc
      a v*x v*(a w*x w)=(a v*a w)*(x v*x w) := by ring
      _=0 := by rw [h,zero_mul]
  · simp

 theorem sparse_matrix_square_bound (A : Matrix V V ℝ) (M : ℝ)
    (hrow : ∀u v w,v≠w → A u v*A u w=0)
    (hcol : ∀v,(∑u,(A u v)^2)≤M) (x : V → ℝ) :
    (∑u,(A.mulVec x u)^2)≤M*(∑v,(x v)^2) := by
  calc
    _=∑u,∑v,(A u v)^2*(x v)^2 := by
      apply sum_congr rfl
      intro u _
      exact sparse_square_sum (A u) x (hrow u)
    _=∑v,(∑u,(A u v)^2)*(x v)^2 := by rw [sum_comm]; simp_rw [sum_mul]
    _≤∑v,M*(x v)^2 := sum_le_sum (fun v _ => mul_le_mul_of_nonneg_right (hcol v) (sq_nonneg _))
    _=M*(∑v,(x v)^2) := (mul_sum _ _ _).symm

theorem transpose_square_bound (A : Matrix V V ℝ) (M : ℝ)
    (hbound : ∀x : V → ℝ,(∑u,(A.mulVec x u)^2)≤M*(∑v,(x v)^2))
    (x : V → ℝ) : (∑u,(A.transpose.mulVec x u)^2)≤M*(∑v,(x v)^2) := by
  let y := A.transpose.mulVec x
  have hdual : (∑v,(y v)^2)=∑u,x u*(A.mulVec y u) := by
    calc
      _=∑v,(A.transpose.mulVec x v)*y v := by simp only [y,sq]
      _=∑v,∑u,(A u v*x u)*y v := by simp only [mulVec,dotProduct,transpose_apply,sum_mul]
      _=∑u,x u*(A.mulVec y u) := by
        rw [sum_comm]
        simp only [mulVec,dotProduct,mul_sum]
        apply sum_congr rfl
        intro u _
        apply sum_congr rfl
        intro v _
        ring
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset V) x (A.mulVec y)
  rw [←hdual] at hcs
  have hx : 0≤∑v,(x v)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hy : 0≤∑v,(y v)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
  have hm := mul_le_mul_of_nonneg_left (hbound y) hx
  change (∑v,(y v)^2)≤M*(∑v,(x v)^2)
  by_cases hz : (∑v,(y v)^2)=0
  · have hb := hbound x
    have hn : 0≤∑u,(A.mulVec x u)^2 := sum_nonneg (fun _ _ => sq_nonneg _)
    rw [hz]
    linarith
  · have hp : 0<∑v,(y v)^2 := lt_of_le_of_ne hy (Ne.symm hz)
    nlinarith

theorem vector_sum_square_bound {H : Type*} [Fintype H] (v : H → V → ℝ)
    (b : H → ℝ) (S : ℝ) (hb : ∀h,0≤b h) (hS : 0≤S)
    (hv : ∀h,(∑i,(v h i)^2)≤(b h)^2*S) :
    (∑i,(∑h,v h i)^2)≤(∑h,b h)^2*S := by
  let w : H → EuclideanSpace ℝ V := fun h => WithLp.toLp 2 (v h)
  have hwn : ∀h,‖w h‖≤b h*Real.sqrt S := by
    intro h
    have he := EuclideanSpace.real_norm_sq_eq (w h)
    have hs := Real.sq_sqrt hS
    have hvh := hv h
    have hp : 0≤b h*Real.sqrt S := mul_nonneg (hb h) (Real.sqrt_nonneg _)
    dsimp [w] at he
    nlinarith [norm_nonneg (w h)]
  have ht : ‖∑h,w h‖≤(∑h,b h)*Real.sqrt S := by
    calc
      _≤∑h,‖w h‖ := norm_sum_le _ _
      _≤∑h,b h*Real.sqrt S := sum_le_sum (fun h _ => hwn h)
      _=(∑h,b h)*Real.sqrt S := (sum_mul _ _ _).symm
  have he := EuclideanSpace.real_norm_sq_eq (∑h,w h)
  have hvsum : ∀i,(∑h,w h).ofLp i=∑h,v h i := by
    intro i
    simp [w]
  simp_rw [hvsum] at he
  have hbS : 0≤(∑h,b h)*Real.sqrt S := mul_nonneg (sum_nonneg (fun h _ => hb h)) (Real.sqrt_nonneg _)
  have hs := Real.sq_sqrt hS
  have hn := norm_nonneg (∑h,w h)
  nlinarith

theorem matrix_sum_square_bound {H : Type*} [Fintype H] (A : H → Matrix V V ℝ)
    (b : H → ℝ) (hb : ∀h,0≤b h)
    (hA : ∀h,∀x : V → ℝ,(∑i,((A h*ᵥx) i)^2)≤(b h)^2*(∑i,(x i)^2))
    (x : V → ℝ) : (∑i,(((∑h,A h)*ᵥx) i)^2)≤(∑h,b h)^2*(∑i,(x i)^2) := by
  have he : ∀i,((∑h,A h)*ᵥx) i=∑h,(A h*ᵥx) i := by simp [sum_mulVec]
  simp_rw [he]
  exact vector_sum_square_bound (fun h => A h*ᵥx) b _ hb
    (sum_nonneg (fun _ _ => sq_nonneg _)) (fun h => hA h x)

 theorem diagonal_factor_quadratic_bound [DecidableEq V] (K : Matrix V V ℝ) (d : V → ℝ) (M : ℝ)
    (hd : ∀i,d i≤1)
    (hK : ∀x : V → ℝ,(∑i,(K.mulVec x i)^2)≤M*(∑i,(x i)^2)) (x : V → ℝ) :
    x ⬝ᵥ ((K*diagonal d*K.transpose)*ᵥx)≤M*(∑i,(x i)^2) := by
  have he : x ⬝ᵥ ((K*diagonal d*K.transpose)*ᵥx)=
      ∑i,d i*(K.transpose.mulVec x i)^2 := by
    rw [←mulVec_mulVec,←mulVec_mulVec,dotProduct_mulVec]
    have hx : x ᵥ* K=K.transpose*ᵥx := by ext i; simp [vecMul,mulVec,dotProduct,mul_comm]
    rw [hx]
    simp only [dotProduct,mulVec_diagonal]
    apply sum_congr rfl
    intro i _
    ring
  rw [he]
  calc
    _≤∑i,(K.transpose.mulVec x i)^2 := by
      apply sum_le_sum
      intro i _
      nlinarith [sq_nonneg (K.transpose.mulVec x i),mul_le_mul_of_nonneg_right (hd i) (sq_nonneg (K.transpose.mulVec x i))]
    _≤M*(∑i,(x i)^2) := transpose_square_bound K M hK x

theorem bounded_diagonal_factor_quadratic_bound [DecidableEq V] (K : Matrix V V ℝ)
    (d : V → ℝ) (D M : ℝ) (hD : 0≤D) (hd : ∀i,d i≤D)
    (hK : ∀x : V → ℝ,(∑i,(K.mulVec x i)^2)≤M*(∑i,(x i)^2)) (x : V → ℝ) :
    x ⬝ᵥ ((K*diagonal d*K.transpose)*ᵥx)≤D*M*(∑i,(x i)^2) := by
  have he : x ⬝ᵥ ((K*diagonal d*K.transpose)*ᵥx)=
      ∑i,d i*(K.transpose.mulVec x i)^2 := by
    rw [←mulVec_mulVec,←mulVec_mulVec,dotProduct_mulVec]
    have hx : x ᵥ* K=K.transpose*ᵥx := by ext i; simp [vecMul,mulVec,dotProduct,mul_comm]
    rw [hx]
    simp only [dotProduct,mulVec_diagonal]
    apply sum_congr rfl
    intro i _
    ring
  rw [he]
  calc
    _≤∑i,D*(K.transpose.mulVec x i)^2 :=
      sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hd i) (sq_nonneg _))
    _=D*(∑i,(K.transpose.mulVec x i)^2) := (mul_sum _ _ _).symm
    _≤D*(M*(∑i,(x i)^2)) := mul_le_mul_of_nonneg_left (transpose_square_bound K M hK x) hD
    _=D*M*(∑i,(x i)^2) := by ring

end HardCoreActivityThreshold
