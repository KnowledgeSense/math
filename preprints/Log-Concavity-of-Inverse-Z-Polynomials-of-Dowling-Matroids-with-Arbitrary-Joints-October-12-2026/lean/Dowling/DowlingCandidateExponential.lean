import Dowling.DowlingCandidateP

noncomputable section
namespace Dowling
open PowerSeries Finset
variable {R : Type*} [CommRing R] [NoZeroDivisors R] [CharZero R]

/-- Uniqueness for a homogeneous first-order formal differential equation. -/
theorem candidate_ode_zero (f h : PowerSeries R) (h0 : f.constantCoeff=0)
    (hD : derivative f=f*h) : f=0 := by
  apply PowerSeries.ext
  intro n
  suffices coeff n f=0 by simpa using this
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff_apply] using h0
    | succ n =>
      have hc := congrArg (coeff n) hD
      rw [coeff_derivative,coeff_mul] at hc
      have hz : ∑ ij ∈ antidiagonal n, coeff ij.1 f * coeff ij.2 h = 0 := by
        apply sum_eq_zero
        intro ij hij
        rw [ih ij.1 (by have := mem_antidiagonal.mp hij; omega),zero_mul]
      rw [hz] at hc
      exact (mul_eq_zero.mp hc).resolve_right (by exact_mod_cast Nat.succ_ne_zero n)

theorem candidate_ode_unique (f g h : PowerSeries R) (h0 : f.constantCoeff=g.constantCoeff)
    (hf : derivative f=f*h) (hg : derivative g=g*h) : f=g := by
  apply sub_eq_zero.mp
  apply candidate_ode_zero (f-g) h
  · simpa only [map_sub,sub_eq_zero] using h0
  · rw [map_sub,hf,hg,sub_mul]

variable [Algebra ℚ R]

/-- Formal exponential evaluated at an actual zero-constant series. -/
def candidateExp (f : PowerSeries R) : PowerSeries R := (exp R).subst f

omit [NoZeroDivisors R] [CharZero R] in
theorem candidateExp_constantCoeff {f : PowerSeries R} (hf : f.constantCoeff=0) :
    PowerSeries.constantCoeff (candidateExp f)=1 := by
  rw [PowerSeries.constantCoeff_eq,candidateExp,
    constantCoeff_subst_of_constantCoeff_zero hf]
  exact constantCoeff_exp

omit [NoZeroDivisors R] [CharZero R] in
theorem derivative_candidateExp {f : PowerSeries R} (hf : f.constantCoeff=0) :
    derivative (candidateExp f)=candidateExp f * derivative f := by
  rw [candidateExp,derivative_subst (HasSubst.of_constantCoeff_zero' hf),derivative_exp]

 theorem candidateExp_add {f g : PowerSeries R} (hf : f.constantCoeff=0)
    (hg : g.constantCoeff=0) : candidateExp (f+g)=candidateExp f*candidateExp g := by
  have hfg : (f+g).constantCoeff=0 := by simp [hf,hg]
  apply candidate_ode_unique _ _ (derivative f+derivative g)
  · rw [candidateExp_constantCoeff hfg,map_mul,candidateExp_constantCoeff hf,
      candidateExp_constantCoeff hg,one_mul]
  · rw [derivative_candidateExp hfg,map_add]
  · rw [Derivation.leibniz,derivative_candidateExp hf,derivative_candidateExp hg]
    simp only [smul_eq_mul]
    ring

@[simp] theorem candidateExp_zero : candidateExp (0 : PowerSeries R)=1 := by
  apply candidate_ode_unique _ _ 0
  · rw [candidateExp_constantCoeff rfl,map_one]
  · rw [derivative_candidateExp rfl,map_zero,mul_zero]
  · rw [derivative_one,mul_zero]

 theorem candidateExp_neg {f : PowerSeries R} (hf : f.constantCoeff=0) :
    candidateExp f*candidateExp (-f)=1 := by
  rw [← candidateExp_add hf (by simp [hf]),add_neg_cancel,candidateExp_zero]

omit [NoZeroDivisors R] [CharZero R] in
theorem candidateExp_subst {f g : PowerSeries R} (hf : f.constantCoeff=0)
    (hg : g.constantCoeff=0) :
    PowerSeries.subst g (candidateExp f)=candidateExp (f.subst g) := by
  exact subst_comp_subst_apply (HasSubst.of_constantCoeff_zero' hf)
    (HasSubst.of_constantCoeff_zero' hg) _

end Dowling
