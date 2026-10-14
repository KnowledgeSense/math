import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.Tactic

/-! Finite coefficient extraction for the formal geometric substitution. -/
namespace Fan
open PowerSeries Finset
variable {R : Type*} [CommRing R]

/-- Zero-constant substitution can be extracted using a genuinely finite sum. -/
theorem coeff_subst_X_mul (f g : PowerSeries R) (n : ℕ) :
    coeff n (f.subst (X * g)) =
      ∑ d ∈ range (n + 1), coeff d f * coeff (n - d) (g ^ d) := by
  have hz : HasSubst ((X : PowerSeries R) * g) := HasSubst.of_constantCoeff_zero' (by simp)
  rw [PowerSeries.coeff_subst' hz]
  simp only [smul_eq_mul]
  rw [finsum_eq_sum_of_support_subset _ (s := range (n + 1)) (by
    intro d hd
    change coeff d f * coeff n ((X * g) ^ d) ≠ 0 at hd
    by_contra hdn
    have hgt : ¬d ≤ n := by simpa only [mem_coe, mem_range, Nat.lt_succ_iff] using hdn
    apply hd
    rw [mul_pow, coeff_X_pow_mul', ite_eq_right hgt, mul_zero])]
  apply sum_congr rfl
  intro d hd
  have hle : d ≤ n := by simpa using mem_range.mp hd
  rw [mul_pow, coeff_X_pow_mul', ite_eq_left hle]

end Fan
