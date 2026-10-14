import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace SumsetRanges
open scoped BigOperators

noncomputable def sparseThreshold (k : ℕ) : ℕ := ⌊(k : ℝ)^((7 : ℝ)/10)⌋₊
noncomputable def repetitionCap (c : ℕ) : ℕ := ⌊(c : ℝ)^((9 : ℝ)/10)⌋₊
noncomputable def sharedCap (c : ℕ) : ℕ := ⌊(c : ℝ)^((4 : ℝ)/5)⌋₊

theorem tenth_root_large {h c : ℕ} (hc : (32*h^3)^10≤c) :
    (32*h^3 : ℝ)≤(c : ℝ)^((1 : ℝ)/10) := by
  have he : ((32*h^3 : ℝ)^10)^((1 : ℝ)/10)=(32*h^3 : ℝ) := by
    rw [← Real.rpow_natCast_mul (by positivity)]
    norm_num
  rw [← he]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact_mod_cast hc

theorem nonfree_real_bound {h c : ℕ} (hh : 1≤h) (hc : (32*h^3)^10≤c) :
    8*(h : ℝ)*(3*(h : ℝ)^2*(c : ℝ)^((9 : ℝ)/10))≤c := by
  have ht := tenth_root_large hc
  have cp : 0<c := lt_of_lt_of_le (by positivity) hc
  have he : (c : ℝ)^((1 : ℝ)/10)*(c : ℝ)^((9 : ℝ)/10)=(c : ℝ) := by
    rw [← Real.rpow_add (by exact_mod_cast cp)]
    norm_num
  have hmul := mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (Nat.cast_nonneg c) ((9 : ℝ)/10))
  have hp : 0≤(h : ℝ)^3*(c : ℝ)^((9 : ℝ)/10) := by positivity
  nlinarith

theorem sparseThreshold_large {h k : ℕ} (hh : 2≤h) (hk : (2*h)^80≤k) :
    (32*h^3)^10≤sparseThreshold k := by
  have hsmall : (32*h^3)^10≤(2*h)^56 := by
    have hhpow : h^30≤h^56 := Nat.pow_le_pow_right (by omega) (by omega)
    have hc : 32^10≤2^56 := by norm_num
    simp only [mul_pow,← pow_mul]
    exact Nat.mul_le_mul hc hhpow
  have hreal : (((2*h : ℕ)^80 : ℕ) : ℝ)^((7 : ℝ)/10)=((2*h : ℕ) : ℝ)^56 := by
    push_cast
    rw [← Real.rpow_natCast_mul (by positivity)]
    norm_num
  apply Nat.le_floor
  have hkR : (((2*h : ℕ)^80 : ℕ) : ℝ)≤(k : ℝ) := by exact_mod_cast hk
  have hp := Real.rpow_le_rpow (by positivity : (0 : ℝ)≤((2*h : ℕ)^80 : ℕ))
    hkR (by norm_num : (0 : ℝ)≤(7 : ℝ)/10)
  rw [hreal] at hp
  exact le_trans (by exact_mod_cast hsmall) hp

theorem sharedCap_le_repetitionCap {c : ℕ} (hc : 1≤c) : sharedCap c≤repetitionCap c := by
  apply Nat.floor_mono
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hc) (by norm_num)

theorem repetition_nonfree_bound {h c : ℕ} (hh : 1≤h) (hc : (32*h^3)^10≤c) :
    8*h*(3*h^2*repetitionCap c)≤c := by
  have hf := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg c) ((9 : ℝ)/10))
  have hb := nonfree_real_bound hh hc
  change (repetitionCap c : ℝ)≤_ at hf
  have hm := mul_le_mul_of_nonneg_left hf (by positivity : (0 : ℝ)≤8*h*(3*h^2))
  change (repetitionCap c : ℝ)≤_ at hf
  have hh' : (8*h*(3*h^2*repetitionCap c) : ℝ)≤c := by nlinarith
  exact_mod_cast hh'

theorem large_c_elementary {h c : ℕ} (hh : 1≤h) (hc : (32*h^3)^10≤c) :
    32≤c ∧ 8*h^2≤c := by
  have hp : 0<32*h^3 := by positivity
  have hb : 32*h^3≤(32*h^3)^10 := by
    simpa using Nat.pow_le_pow_right hp (by omega : 1≤10)
  have hpow : h^2≤h^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1≤h^3 := Nat.one_le_pow _ _ hh
  constructor <;> nlinarith

theorem large_caps_positive {h c : ℕ} (hh : 1≤h) (hc : (32*h^3)^10≤c) :
    1≤repetitionCap c ∧ 2≤sharedCap c := by
  have hc32 := (large_c_elementary hh hc).1
  have hc1 : (1 : ℝ)≤c := by exact_mod_cast (show 1≤c by omega)
  constructor
  · apply Nat.le_floor
    simp only [Nat.cast_one]
    simpa using Real.rpow_le_rpow (by norm_num : (0 : ℝ)≤1) hc1 (by norm_num : (0 : ℝ)≤9/10)
  · apply Nat.le_floor
    have hr : (32 : ℝ)^((4 : ℝ)/5)≤(c : ℝ)^((4 : ℝ)/5) :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hc32) (by norm_num)
    have he : (32 : ℝ)^((4 : ℝ)/5)=16 := by
      rw [show (32 : ℝ)=2^5 by norm_num,← Real.rpow_natCast_mul (by norm_num)]
      norm_num
    rw [he] at hr
    exact le_trans (by norm_num) hr

theorem maximum_nonfree_bound {h c : ℕ} (hh : 1≤h) (hc : (32*h^3)^10≤c) :
    8*h*(∑ m ∈ Finset.Icc 2 h,(2*m*repetitionCap c+m*sharedCap c))≤c := by
  have hc1 : 1≤c := by have hh' := (large_c_elementary hh hc).1; omega
  have hs := sharedCap_le_repetitionCap hc1
  have hsum : (∑ m ∈ Finset.Icc 2 h,(2*m*repetitionCap c+m*sharedCap c))≤
      (Finset.Icc 2 h).card*(3*h*repetitionCap c) := by
    apply Finset.sum_le_card_nsmul
    intro m hm
    have hmh := (Finset.mem_Icc.mp hm).2
    nlinarith
  have hcard : (Finset.Icc 2 h).card≤h := by simp only [Nat.card_Icc]; omega
  have hsum' : (∑ m ∈ Finset.Icc 2 h,(2*m*repetitionCap c+m*sharedCap c))≤
      3*h^2*repetitionCap c := by
    have hb := Nat.mul_le_mul_right (3*h*repetitionCap c) hcard
    nlinarith
  exact (Nat.mul_le_mul_left (8*h) hsum').trans (repetition_nonfree_bound hh hc)

theorem shared_width_le_repetition {h c : ℕ} (hh : 1≤h) (hc : (32*h^3)^10≤c) :
    4*(sharedCap c-1)≤repetitionCap c := by
  have hc32 := (large_c_elementary hh hc).1
  have cp : 0<c := by omega
  have ht := tenth_root_large hc
  have h1 : (1 : ℝ)≤(h : ℝ)^3 := by exact_mod_cast Nat.one_le_pow 3 h hh
  have ht4 : (4 : ℝ)≤(c : ℝ)^((1 : ℝ)/10) := by nlinarith
  have hS := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg c) ((4 : ℝ)/5))
  change (sharedCap c : ℝ)≤_ at hS
  have he : (c : ℝ)^((1 : ℝ)/10)*(c : ℝ)^((4 : ℝ)/5)=(c : ℝ)^((9 : ℝ)/10) := by
    rw [← Real.rpow_add (by exact_mod_cast cp)]
    norm_num
  have hm := mul_le_mul_of_nonneg_right ht4 (Real.rpow_nonneg (Nat.cast_nonneg c) ((4 : ℝ)/5))
  have hx : (4*sharedCap c : ℕ)≤repetitionCap c := by
    apply Nat.le_floor
    push_cast
    nlinarith
  omega

theorem sparseThreshold_le_sub_two {h k : ℕ} (hh : 2≤h) (hk : (2*h)^80≤k) :
    sparseThreshold k≤k-2 := by
  have hbase : 2^10≤k := by
    calc
      2^10≤(2*h)^10 := Nat.pow_le_pow_left (by omega : 2≤2*h) 10
      _≤(2*h)^80 := Nat.pow_le_pow_right (by omega) (by omega)
      _≤k := hk
  have kp : 0<k := by norm_num at hbase ⊢; omega
  have ht : (2 : ℝ)≤(k : ℝ)^((3 : ℝ)/10) := by
    have hr : ((2 : ℝ)^10)^((3 : ℝ)/10)≤(k : ℝ)^((3 : ℝ)/10) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hbase) (by norm_num)
    rw [← Real.rpow_natCast_mul (by norm_num)] at hr
    norm_num at hr
    linarith
  have hf := Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg k) ((7 : ℝ)/10))
  change (sparseThreshold k : ℝ)≤_ at hf
  have hm := mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (Nat.cast_nonneg k) ((7 : ℝ)/10))
  have he : (k : ℝ)^((3 : ℝ)/10)*(k : ℝ)^((7 : ℝ)/10)=(k : ℝ) := by
    rw [← Real.rpow_add (by exact_mod_cast kp)]
    norm_num
  have h2r : (2 : ℝ)*sparseThreshold k≤k := by nlinarith
  have h2 : 2*sparseThreshold k≤k := by exact_mod_cast h2r
  norm_num at hbase
  omega

theorem k_le_four_c_rpow {k c : ℕ} (hc : 1≤c) (hkc : sparseThreshold k≤c) :
    (k : ℝ)≤4*(c : ℝ)^((10 : ℝ)/7) := by
  have hf := Nat.lt_floor_add_one ((k : ℝ)^((7 : ℝ)/10))
  change (k : ℝ)^((7 : ℝ)/10)<(sparseThreshold k : ℝ)+1 at hf
  have hkcr : (sparseThreshold k : ℝ)≤c := by exact_mod_cast hkc
  have hcr : (1 : ℝ)≤c := by exact_mod_cast hc
  have hx : (k : ℝ)^((7 : ℝ)/10)≤2*c := by linarith
  have hp := Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg k) ((7 : ℝ)/10)) hx
    (by norm_num : (0 : ℝ)≤10/7)
  rw [← Real.rpow_mul (Nat.cast_nonneg k),Real.mul_rpow (by norm_num) (Nat.cast_nonneg c)] at hp
  norm_num at hp
  have h2 : (2 : ℝ)^((10 : ℝ)/7)≤4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
      (by norm_num : (10 : ℝ)/7≤2)
    norm_num at h
    exact h
  have hm := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg (Nat.cast_nonneg c) ((10 : ℝ)/7))
  exact hp.trans hm

theorem shared_product_lower {h c : ℕ} (hh : 1≤h) (hc : (32*h^3)^10≤c) :
    (c : ℝ)^((8 : ℝ)/5)≤4*(sharedCap c : ℝ)*(sharedCap c-1 : ℕ) := by
  have hs := (large_caps_positive hh hc).2
  have hc32 := (large_c_elementary hh hc).1
  have hx4 : (4 : ℝ)≤(c : ℝ)^((4 : ℝ)/5) := by
    have hb : (32 : ℝ)^((4 : ℝ)/5)≤(c : ℝ)^((4 : ℝ)/5) :=
      Real.rpow_le_rpow (by norm_num) (by exact_mod_cast hc32) (by norm_num)
    have he : (32 : ℝ)^((4 : ℝ)/5)=16 := by
      rw [show (32 : ℝ)=2^5 by norm_num,← Real.rpow_natCast_mul (by norm_num)]
      norm_num
    rw [he] at hb
    linarith
  have hf := Nat.lt_floor_add_one ((c : ℝ)^((4 : ℝ)/5))
  change (c : ℝ)^((4 : ℝ)/5)<(sharedCap c : ℝ)+1 at hf
  have hS : (c : ℝ)^((4 : ℝ)/5)/2≤(sharedCap c : ℝ) := by linarith
  have hSm : (c : ℝ)^((4 : ℝ)/5)/2≤(sharedCap c-1 : ℕ) := by
    rw [Nat.cast_sub (by omega : 1≤sharedCap c),Nat.cast_one]
    linarith
  have hp := mul_le_mul hS hSm (by positivity) (Nat.cast_nonneg (sharedCap c))
  have he : ((c : ℝ)^((4 : ℝ)/5))^2=(c : ℝ)^((8 : ℝ)/5) := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg c)]
    norm_num
  nlinarith

theorem shared_width_covers_k {h k c : ℕ} (hh : 1≤h) (hc : (32*h^3)^10≤c)
    (hkc : sparseThreshold k≤c) : 8*k≤sharedCap c*(sharedCap c-1) := by
  have hc32 := (large_c_elementary hh hc).1
  have cp : 0<c := by omega
  have hk := k_le_four_c_rpow (by omega : 1≤c) hkc
  have hp := shared_product_lower hh hc
  have hbase : 2^50≤c := by
    have h1 : 1≤h^3 := Nat.one_le_pow _ _ hh
    have hb : 32≤32*h^3 := by omega
    have hx := Nat.pow_le_pow_left hb 10
    norm_num at hx ⊢
    omega
  have h128 : (128 : ℝ)≤(c : ℝ)^((6 : ℝ)/35) := by
    have hb : ((2 : ℝ)^50)^((6 : ℝ)/35)≤(c : ℝ)^((6 : ℝ)/35) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hbase) (by norm_num)
    rw [← Real.rpow_natCast_mul (by norm_num)] at hb
    have he := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ)≤2)
      (by norm_num : (7 : ℝ)≤50*(6/35))
    norm_num at he hb
    exact he.trans hb
  have hm := mul_le_mul_of_nonneg_right h128 (Real.rpow_nonneg (Nat.cast_nonneg c) ((10 : ℝ)/7))
  have he : (c : ℝ)^((6 : ℝ)/35)*(c : ℝ)^((10 : ℝ)/7)=(c : ℝ)^((8 : ℝ)/5) := by
    rw [← Real.rpow_add (by exact_mod_cast cp)]
    norm_num
  have hresult : (8 : ℝ)*k≤(sharedCap c : ℝ)*(sharedCap c-1 : ℕ) := by nlinarith
  exact_mod_cast hresult

end SumsetRanges
