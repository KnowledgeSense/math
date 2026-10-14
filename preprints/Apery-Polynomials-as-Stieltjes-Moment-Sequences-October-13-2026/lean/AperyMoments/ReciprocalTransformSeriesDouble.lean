import AperyMoments.ReciprocalTransformSeriesBounds
import Mathlib.Analysis.Normed.Ring.InfiniteSum

noncomputable section
namespace AperyMoments
open Complex Finset
open scoped Topology

def reciprocalDoubleTerm (α R : ℝ) (m k : ℕ) : ℂ :=
  (spectralMomentCoefficient m α:ℂ)*(- (α:ℂ))^k*((2*m+k).choose k:ℂ)/
    (R:ℂ)^(m+k+1)

theorem reciprocalDoubleTerm_norm {α R : ℝ} (hα : 0≤α) (hR : 0<R) (m k : ℕ) :
    ‖reciprocalDoubleTerm α R m k‖=
      spectralMomentCoefficient m α*α^k*((2*m+k).choose k:ℝ)/R^(m+k+1) := by
  simp [reciprocalDoubleTerm,norm_pow,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hα,
    abs_of_nonneg (spectralMomentCoefficient_nonneg hα m),abs_of_pos hR]

theorem reciprocalDoubleTerm_bound {α R : ℝ} (hα : 0≤α) (hα1 : α≤1)
    (hR : 0<R) (m k : ℕ) :
    ‖reciprocalDoubleTerm α R m k‖≤R⁻¹*(144/R)^m*(2/R)^k := by
  rw [reciprocalDoubleTerm_norm hα hR]
  have hc : ((2*m+k).choose k:ℝ)≤2^(2*m+k) := by
    exact_mod_cast Nat.choose_le_two_pow (2*m+k) k
  have ha : α^k≤1 := pow_le_one₀ hα hα1
  have hm := spectralMomentCoefficient_bound hα hα1 m
  have hb : spectralMomentCoefficient m α*α^k*((2*m+k).choose k:ℝ)≤
      36^m*2^(2*m+k) := by
    have hmα : spectralMomentCoefficient m α*α^k≤36^m := by
      calc
        _ ≤ spectralMomentCoefficient m α*1 :=
          mul_le_mul_of_nonneg_left ha (spectralMomentCoefficient_nonneg hα m)
        _ ≤ 36^m := by simpa using hm
    exact mul_le_mul hmα hc (by positivity) (by positivity)
  calc
    _ ≤ (36^m*2^(2*m+k))/R^(m+k+1) :=
      div_le_div_of_nonneg_right hb (by positivity)
    _ = R⁻¹*(144/R)^m*(2/R)^k := by
      have hp : (36:ℝ)^m*2^(2*m+k)=144^m*2^k := by
        rw [pow_add,pow_mul,← mul_assoc,← mul_pow]
        norm_num
      rw [hp]
      simp only [div_pow,pow_add]
      field_simp


theorem reciprocalDoubleTerm_summable {α R : ℝ} (hα : 0≤α) (hα1 : α≤1)
    (hR : 256<R) : Summable (fun p:ℕ×ℕ=>reciprocalDoubleTerm α R p.1 p.2) := by
  have hR0 : 0<R := by linarith
  have h1 : |144/R|<1 := by rw [abs_of_nonneg (by positivity)]; exact (div_lt_one hR0).mpr (by linarith)
  have h2 : |2/R|<1 := by rw [abs_of_nonneg (by positivity)]; exact (div_lt_one hR0).mpr (by linarith)
  have hs1 := summable_geometric_of_abs_lt_one h1
  have hs2 := summable_geometric_of_abs_lt_one h2
  have hs := (hs1.mul_of_nonneg hs2 (fun _=>by positivity) (fun _=>by positivity)).mul_left R⁻¹
  apply Summable.of_norm_bounded hs
  intro p
  simpa only [mul_assoc] using reciprocalDoubleTerm_bound hα hα1 hR0 p.1 p.2

end AperyMoments
