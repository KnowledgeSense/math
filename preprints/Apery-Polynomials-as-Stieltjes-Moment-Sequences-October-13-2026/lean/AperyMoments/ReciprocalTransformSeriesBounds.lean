import AperyMoments.SpectralCauchySeries
import AperyMoments.SpectralMoments
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory Finset
open scoped Topology

theorem spectralMomentCoefficient_integral {α : ℝ} (hα : 0≤α) (m : ℕ) :
    spectralMomentCoefficient m α=∫ w:ℝ,w^(2*m)*spectralDensity (2*Real.sqrt α) w :=
  (spectralMoment_reciprocal_parameter hα m).symm

theorem spectralMomentCoefficient_nonneg {α : ℝ} (hα : 0≤α) (m : ℕ) :
    0≤spectralMomentCoefficient m α := by
  rw [spectralMomentCoefficient_integral hα]
  apply integral_nonneg
  intro w
  exact mul_nonneg (by rw [pow_mul]; positivity) (spectralDensity_nonneg _ _)

theorem spectralMomentCoefficient_bound {α : ℝ} (hα : 0≤α) (hα1 : α≤1) (m : ℕ) :
    spectralMomentCoefficient m α≤36^m := by
  have hb : 0≤2*Real.sqrt α := by positivity
  have hmass := spectralDensity_integral hb
  have hi := spectralDensity_integrable hb
  have hpow := spectralPower_integrable hb (2*m)
  rw [spectralMomentCoefficient_integral hα]
  have hbound (w : ℝ) : w^(2*m)*spectralDensity (2*Real.sqrt α) w≤
      36^m*spectralDensity (2*Real.sqrt α) w := by
    by_cases hw : spectralDensity (2*Real.sqrt α) w=0
    · simp [hw]
    · have hs := spectralDensity_support hb hw
      have hsqrt : Real.sqrt α≤1 := Real.sqrt_le_one.mpr hα1
      have hw6 : |w|≤6 := by linarith
      have hpower : w^(2*m)≤36^m := by
        calc
          _ ≤ |w^(2*m)| := le_abs_self _
          _ = |w|^(2*m) := abs_pow _ _
          _ ≤ (6:ℝ)^(2*m) := pow_le_pow_left₀ (abs_nonneg w) hw6 _
          _ = 36^m := by rw [pow_mul]; norm_num
      exact mul_le_mul_of_nonneg_right hpower (spectralDensity_nonneg _ _)
  have h := integral_mono hpow (hi.const_mul (36^m)) hbound
  rw [integral_const_mul,hmass,mul_one] at h
  exact h

theorem spectralCauchy_even_hasSum {α y : ℝ} (hα : 0≤α)
    (hy : 4+2*Real.sqrt α<y) :
    HasSum (fun m=>(spectralMomentCoefficient m α:ℂ)/(y:ℂ)^(2*m+1))
      (spectralCauchyTransform (2*Real.sqrt α) (y:ℂ)) := by
  have hb : 0≤2*Real.sqrt α := by positivity
  have hfull := densityCauchy_hasSum (spectralDensity_measurable (2*Real.sqrt α))
    (spectralDensity_integrable hb) (spectralDensity_nonneg _) (by positivity) hy
    (fun w hw=>spectralDensity_support hb hw)
  simp_rw [integral_complex_ofReal] at hfull
  have hinj : Function.Injective (fun m:ℕ=>2*m) := by intro a b h; dsimp at h; omega
  have hz (n : ℕ) (hn : n∉Set.range (fun m:ℕ=>2*m)) :
      ((∫ w:ℝ,w^n*spectralDensity (2*Real.sqrt α) w : ℝ):ℂ)/(y:ℂ)^(n+1)=0 := by
    have hodd : n=2*(n/2)+1 := by
      have hmod := Nat.mod_two_eq_zero_or_one n
      have hnot : n≠2*(n/2) := by intro he; exact hn ⟨n/2,he.symm⟩
      omega
    rw [hodd,spectralMoment_odd hb,Complex.ofReal_zero,zero_div]
  have he := (hinj.hasSum_iff hz).mpr hfull
  simpa only [Function.comp_def,spectralCauchyTransform,← spectralMomentCoefficient_integral hα] using he

end AperyMoments
