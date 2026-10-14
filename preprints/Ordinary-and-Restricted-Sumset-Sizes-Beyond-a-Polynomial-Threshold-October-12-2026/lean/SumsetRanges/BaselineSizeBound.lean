import SumsetRanges.RestrictedLargeChain
import Mathlib.Data.Nat.Choose.Bounds

open Finset Polynomial
namespace SumsetRanges
open scoped BigOperators Classical

theorem baseline_size_bound (h c b x : ℕ) (hh : 2≤h) (hc : 4*h≤c) (hb : 2≤b) (hx : b-1≤x) :
    baselineValue h c b x≤3*(h : ℤ)*(c+b)*(c : ℤ)^(h-1) := by
  rw [baselineValue,coeff_mul_range_reversed,sum_range_split_two _ h (by omega)]
  simp only [coeff_one_add_X_pow,Nat.sub_zero,
    coeff_restrictedPolynomial,dense_restricted_one _ _ hx,restrictedSums_zero,Finset.card_singleton,Nat.cast_one,one_mul]
  have hb' : b-1+1=b := by omega
  rw [hb']
  have ht : (∑e∈Icc 2 h,((restrictedSums (denseSet (b-1) x) e).card : ℤ)*(c.choose (h-e) : ℤ))≤
      2*(h : ℤ)*b*(∑e∈Icc 2 h,(c.choose (h-e) : ℤ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have hg := dense_restricted_bound h (b-1) x e (by omega) hx
      (by have := (mem_Icc.mp he).1; omega) (mem_Icc.mp he).2
    rw [hb'] at hg
    have hg' : ((restrictedSums (denseSet (b-1) x) e).card : ℤ)≤2*(h : ℤ)*b := by exact_mod_cast hg
    exact mul_le_mul_of_nonneg_right hg' (Int.natCast_nonneg _)
  have htail : (∑e∈Icc 2 h,(c.choose (h-e) : ℤ))≤2*(c.choose (h-2) : ℤ) := by
    exact_mod_cast choose_tail_le_twice_top h c hh hc
  have hm := mul_le_mul_of_nonneg_left htail (by positivity : (0 : ℤ)≤2*(h : ℤ)*b)
  have h0 : (c.choose h : ℤ)≤(c : ℤ)^h := by exact_mod_cast Nat.choose_le_pow c h
  have h1 : (c.choose (h-1) : ℤ)≤(c : ℤ)^(h-1) := by exact_mod_cast Nat.choose_le_pow c (h-1)
  have h2 : (c.choose (h-2) : ℤ)≤(c : ℤ)^(h-2) := by exact_mod_cast Nat.choose_le_pow c (h-2)
  have h1m := mul_le_mul_of_nonneg_left h1 (Int.natCast_nonneg b)
  have h2m := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℤ)≤4*(h : ℤ)*b)
  have hp0 : (c : ℤ)^h=(c : ℤ)*(c : ℤ)^(h-1) := by
    have he : h=h-1+1 := by omega
    conv_lhs => rw [he,pow_succ]
    ring
  have hp1 : (c : ℤ)^(h-1)=(c : ℤ)*(c : ℤ)^(h-2) := by
    have he : h-1=h-2+1 := by omega
    conv_lhs => rw [he,pow_succ]
    ring
  have hc' : (2 : ℤ)≤c := by omega
  have hh' : (2 : ℤ)≤h := by omega
  have hpow : 0≤(c : ℤ)^(h-2) := by positivity
  have hsmall : 2*(c : ℤ)^(h-2)≤(c : ℤ)^(h-1) := by nlinarith
  have hsm := mul_le_mul_of_nonneg_left hsmall (by positivity : (0 : ℤ)≤2*(h : ℤ)*b)
  have hcoef : (c : ℤ)+(2*(h : ℤ)+1)*b≤3*(h : ℤ)*(c+b) := by nlinarith
  have hfinal := mul_le_mul_of_nonneg_right hcoef (by positivity : (0 : ℤ)≤(c : ℤ)^(h-1))
  nlinarith

theorem restricted_large_range (h k K : ℕ) (hh : 2≤h) (hK : (32*h^3)^10≤K)
    (hKk : K+2≤k) (hkK : sparseThreshold k≤K) (z : ℤ)
    (hz : 3*(h : ℤ)*k*(K : ℤ)^(h-1)≤z) (hzt : z≤(k.choose h : ℤ)) :
    ∃B : Finset ℤ,B.card=k ∧ (∀a∈B,0≤a ∧ a≤(k^(restrictedExponent h):ℕ)) ∧
      ((restrictedSums B h).card : ℤ)=z := by
  apply restricted_large_chain h k K hh hK hKk hkK z _ hzt
  have hc := (large_c_elementary (by omega : 1≤h) hK).2
  have hb := baseline_size_bound h K (k-K) (k-K-1) hh (by nlinarith) (by omega) (le_refl _)
  have he : (K : ℤ)+((k-K : ℕ) : ℤ)=k := by omega
  rw [he] at hb
  exact hb.trans hz

end SumsetRanges
