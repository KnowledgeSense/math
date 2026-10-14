import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic

noncomputable section
open PowerSeries Finset
open scoped PowerSeries BigOperators
namespace ASR312

private theorem reciprocal_derivative (u v : PowerSeries ℚ) (huv : u*v=1) :
    derivative v = -v^2*derivative u := by
  have h := congrArg (derivative : PowerSeries ℚ → PowerSeries ℚ) huv
  simp only [Derivation.leibniz,smul_eq_mul,derivative_one] at h
  linear_combination v*h-derivative v*huv

/-- The positive-degree residue of a substituted exact differential vanishes. -/
theorem reciprocal_jacobian_coeff (u v : PowerSeries ℚ) (huv : u*v=1) (n : ℕ) :
    coeff (n+1) (v^(n+1)+X*(v^(n+2)*derivative u))=0 := by
  have hd : derivative (v^(n+1)) =
      -C (n+1:ℚ)*(v^(n+2)*derivative u) := by
    rw [derivative_pow,reciprocal_derivative u v huv]
    simp only [Nat.add_sub_cancel]
    rw [pow_add]
    simp only [map_natCast,map_add,map_one,Nat.cast_add,Nat.cast_one]
    ring
  have hc := congrArg (coeff n) hd
  rw [coeff_derivative] at hc
  simp only [neg_mul,map_neg,coeff_C_mul] at hc
  rw [map_add,coeff_succ_X_mul]
  have hn : (n+1:ℚ) ≠ 0 := by positivity
  apply (mul_left_cancel₀ hn)
  nlinarith

private theorem reciprocal_pow_cancel (u v : PowerSeries ℚ) (huv : u*v=1) (j m : ℕ) :
    u^j*v^(j+m)=v^m := by
  rw [pow_add,← mul_assoc,← mul_pow,huv,one_pow,one_mul]

/-- The Jacobian pairing on monomials is the identity matrix. -/
theorem substitution_monomial_coeff (u v : PowerSeries ℚ) (huv : u*v=1)
    (n j : ℕ) (hj : j ≤ n) :
    coeff n ((X*u)^j*(u+X*derivative u)*v^(n+1)) = if j=n then 1 else 0 := by
  have h0 : u^(j+1)*v^(n+1)=v^(n-j) := by
    rw [show n+1=j+1+(n-j) by omega]
    exact reciprocal_pow_cancel u v huv (j+1) (n-j)
  have h1 : u^j*v^(n+1)=v^(n-j+1) := by
    rw [show n+1=j+(n-j+1) by omega]
    exact reciprocal_pow_cancel u v huv j (n-j+1)
  have he : (X*u)^j*(u+X*derivative u)*v^(n+1) =
      X^j*(v^(n-j)+X*(v^(n-j+1)*derivative u)) := by
    rw [mul_pow]
    rw [pow_succ] at h0
    linear_combination X^j*h0+X^(j+1)*derivative u*h1
  rw [he,coeff_X_pow_mul',ite_eq_left hj]
  by_cases hjn : j=n
  · subst j
    simp
  · rw [ite_eq_right hjn]
    have hm : n-j=(n-j-1)+1 := by omega
    rw [hm]
    exact reciprocal_jacobian_coeff u v huv (n-j-1)

/-- Coefficients of a substituted series depend on a finite initial segment. -/
theorem coeff_substitution_weight (f u H : PowerSeries ℚ) (n : ℕ) :
    coeff n (f.subst (X*u)*H) =
      ∑ j ∈ range (n+1), coeff j f * coeff n ((X*u)^j*H) := by
  let g : PowerSeries ℚ := X*u
  have hg : HasSubst g := HasSubst.X'.mul_left
  have hs := congrArg (fun p : PowerSeries ℚ => p.subst g)
    (eq_X_pow_mul_shift_add_trunc (n+1) f)
  rw [subst_add hg,subst_mul hg,subst_pow hg,subst_X hg] at hs
  have ht : ((f.trunc (n+1) : PowerSeries ℚ).subst g) =
      ∑ j ∈ range (n+1), C (coeff j f)*g^j := by
    rw [subst_coe hg]
    change (f.trunc (n+1)).eval₂ C g = _
    exact eval₂_trunc_eq_sum_range g C (n+1) f
  rw [ht] at hs
  change coeff n (f.subst g*H)=_
  rw [hs,add_mul,map_add]
  have hz : coeff n ((g^(n+1)*(mk (fun i => coeff (i+(n+1)) f)).subst g)*H)=0 := by
    have he : (g^(n+1)*(mk (fun i => coeff (i+(n+1)) f)).subst g)*H =
        X^(n+1)*(u^(n+1)*(mk (fun i => coeff (i+(n+1)) f)).subst g*H) := by
      dsimp [g]
      rw [mul_pow]
      ring
    rw [he,coeff_X_pow_mul',ite_eq_right (by omega)]
  rw [hz,zero_add,Finset.sum_mul,map_sum]
  apply sum_congr rfl
  intro j _
  rw [mul_assoc,coeff_C_mul]

/-- Formal coefficient change of variables for a series of order one. -/
theorem coefficient_change_of_variable (f u v : PowerSeries ℚ) (huv : u*v=1) (n : ℕ) :
    coeff n (f.subst (X*u)*(u+X*derivative u)*v^(n+1)) = coeff n f := by
  rw [mul_assoc,coeff_substitution_weight]
  have he : (∑ j ∈ range (n+1), coeff j f *
      coeff n ((X*u)^j*((u+X*derivative u)*v^(n+1)))) =
      ∑ j ∈ range (n+1), if j=n then coeff n f else 0 := by
    apply sum_congr rfl
    intro j hj
    rw [← mul_assoc,substitution_monomial_coeff u v huv n j (by have := mem_range.mp hj; omega)]
    split_ifs with h
    · subst j
      simp
    · simp
  rw [he]
  simp

end ASR312
