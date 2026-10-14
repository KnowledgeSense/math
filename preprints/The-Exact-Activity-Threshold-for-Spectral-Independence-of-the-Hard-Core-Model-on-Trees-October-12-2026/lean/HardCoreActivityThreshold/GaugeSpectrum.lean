import HardCoreActivityThreshold.QuadraticSpectrum

namespace HardCoreActivityThreshold
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem signed_quadratic_identity (R : Matrix V V ℝ) (s x : V → ℝ) :
    x ⬝ᵥ ((Matrix.of (fun u v => s u*R u v*s v))*ᵥx)=
      (fun u => s u*x u) ⬝ᵥ (R*ᵥ(fun u => s u*x u)) := by
  simp only [dotProduct,mulVec,of_apply,mul_sum]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  ring

omit [DecidableEq V] in
theorem signed_square_sum (s x : V → ℝ) (hs : ∀v,s v*s v=1) :
    (∑v,(s v*x v)^2)=∑v,(x v)^2 := by
  apply sum_congr rfl
  intro v _
  have h := hs v
  nlinarith [sq_nonneg (x v)]

theorem signed_active_radius_bound (R : Matrix V V ℝ) (hR : R.IsHermitian)
    (s p : V → ℝ) (hs : ∀v,s v*s v=1) (hp : ∀v,0≤p v ∧ p v≤1)
    (C : ℝ) (hC : 0≤C)
    (hlo : ∀x : V → ℝ,0≤x ⬝ᵥ (R*ᵥx))
    (hhi : ∀x : V → ℝ,x ⬝ᵥ (R*ᵥx)≤C*(∑v,(x v)^2)) :
    spectralRadius ℂ ((Matrix.of (fun u v => s u*R u v*s v)-diagonal p).map
      (fun x : ℝ => (x : ℂ)))≤ENNReal.ofReal (C+1) := by
  let A : Matrix V V ℝ := Matrix.of (fun u v => s u*R u v*s v)
  have hA : A.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro u v
    have h := hR.apply u v
    simp only [star_trivial] at h ⊢
    dsimp [A]
    rw [h]
    ring
  have hq (x : V → ℝ) : x ⬝ᵥ ((A-diagonal p)*ᵥx)=
      (fun u => s u*x u) ⬝ᵥ (R*ᵥ(fun u => s u*x u))-∑v,p v*(x v)^2 := by
    rw [sub_mulVec,dotProduct_sub,signed_quadratic_identity]
    congr 1
    simp only [mulVec_diagonal,dotProduct]
    apply sum_congr rfl
    intro v _
    ring
  apply hermitian_radius_quadratic_bound _ (hA.sub (isHermitian_diagonal p)) C hC
  · intro x
    rw [hq]
    have hl := hlo (fun u => s u*x u)
    have hd : (∑v,p v*(x v)^2)≤∑v,(x v)^2 := by
      apply sum_le_sum
      intro v _
      exact mul_le_of_le_one_left (sq_nonneg _) (hp v).2
    linarith
  · intro x
    rw [hq]
    have hh := hhi (fun u => s u*x u)
    rw [signed_square_sum s x hs] at hh
    have hd : 0≤∑v,p v*(x v)^2 := sum_nonneg (fun v _ => mul_nonneg (hp v).1 (sq_nonneg _))
    linarith

end HardCoreActivityThreshold
