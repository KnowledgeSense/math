import HankelAutomaticity.UpperShear

noncomputable section
namespace HankelAutomaticity
open Matrix

 def perturbed (L n : ℕ) (x z : ℚ) : ℚ :=
  (hankelMatrix L n x+Matrix.of (fun _ _ => z)).det

 def derivativeCompanion (L n : ℕ) (x : ℚ) : ℚ :=
  -(bordered (hankelMatrix L n x) 1 0).det

 theorem perturbed_affine (L n : ℕ) (x z : ℚ) :
    perturbed L n x z=hankel L n x+z*derivativeCompanion L n x := by
  rw [perturbed, det_constant_add]
  simp [hankel, derivativeCompanion, sub_eq_add_neg]

 theorem bordered_perturbed (L n : ℕ) (x z c : ℚ) :
    (bordered (hankelMatrix L n x+Matrix.of (fun _ _ => z)) 1 c).det=
      c*perturbed L n x z-derivativeCompanion L n x := by
  rw [det_bordered, bordered_constant_add]
  simp [derivativeCompanion, perturbed, add_comm]

 theorem ordinaryBiased_eq_hankel {L t : ℕ} (hL : 0<L) (ht : t ≤ 2^L) (z : ℚ) :
    ordinaryBiased t z=hankelMatrix (L-1) t 1+Matrix.of (fun _ _ => z) := by
  ext i j
  have hij : i.val+j.val<2^((L-1)+2) := by
    have hi := i.isLt
    have hj := j.isLt
    rw [show L-1+2=L+1 by omega, pow_succ]
    omega
  simp [ordinaryBiased, hankelMatrix, weightedMoment_one hij]

 theorem lower_perturbed_recurrence (L t r : ℕ) (hL : 0<L)
    (h : t+r=2^L) (hr : 2*r<2^L) (x z : ℚ) :
    perturbed L (2^L+(r+1)) x z=(-1 : ℚ)^r*(x-2)^(2*r)*
      ((x-2)*perturbed (L-1) t 1 z-derivativeCompanion (L-1) t 1) := by
  rw [perturbed, ← first_reduction L (r+1) (by omega), ← second_reduction L r (by omega),
    lower_second_reduction L t r h hr, ordinaryBiased_eq_hankel hL (by omega),
    bordered_perturbed]

 theorem upper_sign_factor {L a b : ℕ} (hL : 2 ≤ L) (h : a+b+1+a=2^L) (u : ℚ) :
    (-1 : ℚ)^a*u^(2*a)*(-2*u)^b*(-1 : ℚ)^(b/2)=2^b*u^(2^L-1) := by
  have hM : 2^L%4=0 := by
    rw [show L=2+(L-2) by omega, pow_add]
    omega
  have heven : Even (a+b+b/2) := by
    rw [Nat.even_iff]
    omega
  have hs : (-1 : ℚ)^a*(-1 : ℚ)^b*(-1 : ℚ)^(b/2)=1 := by
    rw [← pow_add, ← pow_add]
    exact heven.neg_one_pow
  have he : 2*a+b=2^L-1 := by omega
  calc
    _ = ((-1 : ℚ)^a*(-1 : ℚ)^b*(-1 : ℚ)^(b/2))*2^b*u^(2*a+b) := by
      rw [show (-2*u : ℚ)=(-1)*2*u by ring, mul_pow, mul_pow, pow_add]
      ring
    _ = _ := by rw [hs, one_mul, he]

 theorem upper_perturbed_recurrence (L a b : ℕ) (hL : 2 ≤ L)
    (h : a+b+1+a=2^L) (x z : ℚ) :
    perturbed L (2^L+(a+b+1)) x z=2^b*(x-2)^(2^L-1)*
      ((x-2)*perturbed (L-1) (a+b+1) (x/2) z-
        derivativeCompanion (L-1) (a+b+1) (x/2)) := by
  rw [perturbed, ← first_reduction L (a+b+1) (by omega),
    ← second_reduction L (a+b) (by omega), upper_paired_reduction L a b h,
    upper_core_reduction, shiftedBiased_eq_hankel (by omega) h,
    bordered_perturbed, det_antiTriangle]
  have hs := upper_sign_factor hL h (x-2)
  linear_combination
    ((x-2)*perturbed (L-1) (a+b+1) (x/2) z-
      derivativeCompanion (L-1) (a+b+1) (x/2))*hs

 theorem lower_pair_recurrence (L t r : ℕ) (hL : 0<L)
    (h : t+r=2^L) (hr : 2*r<2^L) (x : ℚ) :
    hankel L (2^L+(r+1)) x=(-1 : ℚ)^r*(x-2)^(2*r)*
      ((x-2)*hankel (L-1) t 1-derivativeCompanion (L-1) t 1) ∧
    derivativeCompanion L (2^L+(r+1)) x=
      (-1 : ℚ)^r*(x-2)^(2*r+1)*derivativeCompanion (L-1) t 1 := by
  have h0 := lower_perturbed_recurrence L t r hL h hr x 0
  have h1 := lower_perturbed_recurrence L t r hL h hr x 1
  simp only [perturbed_affine, zero_mul, add_zero, one_mul] at h0 h1
  refine ⟨h0, ?_⟩
  rw [pow_succ]
  linear_combination h1-h0

 theorem upper_pair_recurrence (L a b : ℕ) (hL : 2 ≤ L)
    (h : a+b+1+a=2^L) (x : ℚ) :
    hankel L (2^L+(a+b+1)) x=2^b*(x-2)^(2^L-1)*
      ((x-2)*hankel (L-1) (a+b+1) (x/2)-derivativeCompanion (L-1) (a+b+1) (x/2)) ∧
    derivativeCompanion L (2^L+(a+b+1)) x=
      2^b*(x-2)^(2^L)*derivativeCompanion (L-1) (a+b+1) (x/2) := by
  have h0 := upper_perturbed_recurrence L a b hL h x 0
  have h1 := upper_perturbed_recurrence L a b hL h x 1
  simp only [perturbed_affine, zero_mul, add_zero, one_mul] at h0 h1
  refine ⟨h0, ?_⟩
  have hp : (0 : ℕ)<2^L := by positivity
  rw [show (x-2)^(2^L)=(x-2)^(2^L-1)*(x-2) by
    rw [← pow_succ]
    congr 1
    omega]
  linear_combination h1-h0

end HankelAutomaticity
