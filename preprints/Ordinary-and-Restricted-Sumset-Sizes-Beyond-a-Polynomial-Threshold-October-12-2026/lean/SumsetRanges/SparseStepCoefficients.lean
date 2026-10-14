import SumsetRanges.SparseSharedStep

open Finset Polynomial
namespace SumsetRanges
open scoped BigOperators Classical

theorem nonfreeSize_box_bound (h c : ℕ) (r u : ℕ → ℕ) (hh : 1≤h)
    (hc : (32*h^3)^10≤c) (hr : ∀ m∈Icc 2 h,r m≤repetitionCap c)
    (hu : ∀ m∈Icc 2 h,u m≤sharedCap c) : 8*h*nonfreeSize h r u≤c := by
  have hn : nonfreeSize h r u≤∑ m∈Icc 2 h,(2*m*repetitionCap c+m*sharedCap c) := by
    apply Finset.sum_le_sum
    intro m hm
    exact Nat.add_le_add (Nat.mul_le_mul_left (2*m) (hr m hm)) (Nat.mul_le_mul_left m (hu m hm))
  exact (Nat.mul_le_mul_left (8*h) hn).trans (maximum_nonfree_bound hh hc)

theorem sparse_free_size_positive (h c : ℕ) (r u : ℕ → ℕ) (hh : 1≤h) (hc : 0<c)
    (hn : 8*h*nonfreeSize h r u≤c) : 0<c-nonfreeSize h r u := by
  have hh8 : 2≤8*h := by omega
  have hb := Nat.mul_le_mul_right (nonfreeSize h r u) hh8
  omega

theorem coefficient_half_binomial {P : Polynomial ℤ} {h c n d : ℕ}
    (hh : 1≤h) (hch : 2*h≤c) (hn : n≤c) (hgap : 4*h*(c-n)≤c) (hd : d≤h)
    (hP : CoeffLE ((1+X)^n) P) : (c.choose d : ℤ)≤2*P.coeff d := by
  have hb := choose_le_twice_choose h c n d hh hch hn hgap hd
  have hp := hP d
  rw [coeff_one_add_X_pow] at hp
  have hb' : (c.choose d : ℤ)≤2*(n.choose d : ℤ) := by exact_mod_cast hb
  omega

theorem linear_step_coefficient_bounds (h c μ : ℕ) (r u : ℕ → ℕ)
    (hh : 1≤h) (hch : 2*h≤c) (_hμ : μ∈Icc 2 h)
    (hn : 8*h*(nonfreeSize h r u+2*μ)≤c) (d : ℕ) (hd : d≤h) :
    (c.choose d : ℤ)≤2*(linearStepRemainder h c μ r u).coeff d ∧
      (linearStepRemainder h c μ r u).coeff d≤(c.choose d : ℤ) := by
  have hN : nonfreeSize h r u+2*μ≤c := by
    have hx := Nat.le_mul_of_pos_left (nonfreeSize h r u+2*μ) (by omega : 0<8*h)
    omega
  constructor
  · apply coefficient_half_binomial hh hch ((Nat.sub_le _ _).trans (Nat.sub_le _ _))
      (n := c-nonfreeSize h r u-2*μ) _ hd (linearStepRemainder_lower h c μ r u)
    have he : c-(c-nonfreeSize h r u-2*μ)=nonfreeSize h r u+2*μ := by omega
    rw [he]
    nlinarith
  · have hp := linearStepRemainder_upper h c μ r u hN d
    rw [coeff_one_add_X_pow] at hp
    exact hp.trans (by exact_mod_cast Nat.choose_le_choose d (Nat.sub_le c (2*μ)))

theorem shared_step_coefficient_bounds (h c μ : ℕ) (r u : ℕ → ℕ)
    (hh : 1≤h) (hch : 2*h≤c) (hμ : μ∈Icc 2 h) (hu : 1≤u μ)
    (hn : 8*h*(nonfreeSize h r u+μ)≤c) (d : ℕ) (hd : d≤h) :
    (u μ : ℤ)*(c.choose d : ℤ)≤2*(sharedStepRemainder h c μ r u).coeff d ∧
      (sharedStepRemainder h c μ r u).coeff d≤(u μ : ℤ)*(c.choose d : ℤ) := by
  have hN : nonfreeSize h r u+μ≤c := by
    have hx := Nat.le_mul_of_pos_left (nonfreeSize h r u+μ) (by omega : 0<8*h)
    omega
  constructor
  · have hp := sharedStepRemainder_lower h c μ r u (Finset.mem_Icc.mp hμ).1 hu d
    rw [coeff_natCast_mul,coeff_one_add_X_pow] at hp
    have hgap : 4*h*(c-(c-nonfreeSize h r u-μ))≤c := by
      have he : c-(c-nonfreeSize h r u-μ)=nonfreeSize h r u+μ := by omega
      rw [he]
      nlinarith
    have hb := choose_le_twice_choose h c (c-nonfreeSize h r u-μ) d hh hch (Nat.sub_le (c-nonfreeSize h r u) μ |>.trans (Nat.sub_le c _)) hgap hd
    have hb' : (c.choose d : ℤ)≤2*((c-nonfreeSize h r u-μ).choose d : ℤ) := by exact_mod_cast hb
    have hm := mul_le_mul_of_nonneg_left hb' (Int.natCast_nonneg (u μ))
    nlinarith
  · have hp := sharedStepRemainder_upper h c μ r u hμ hu hN d
    rw [coeff_natCast_mul,coeff_one_add_X_pow] at hp
    have hb : ((c-2*μ).choose d : ℤ)≤(c.choose d : ℤ) := by
      exact_mod_cast Nat.choose_le_choose d (Nat.sub_le c (2*μ))
    exact hp.trans (mul_le_mul_of_nonneg_left hb (Int.natCast_nonneg (u μ)))

theorem linear_step_box_bound (h c μ : ℕ) (r u : ℕ → ℕ) (hh : 1≤h)
    (hc : (32*h^3)^10≤c) (hμ : μ∈Icc 2 h)
    (hr : ∀ m∈Icc 2 h,r m≤repetitionCap c)
    (hu : ∀ m∈Icc 2 h,u m≤sharedCap c) (hs : r μ<repetitionCap c) :
    8*h*(nonfreeSize h r u+2*μ)≤c := by
  have hr' : ∀ m∈Icc 2 h,Function.update r μ (r μ+1) m≤repetitionCap c := by
    intro m hm
    by_cases he : m=μ
    · subst m
      simpa only [Function.update_self] using (show r μ+1≤repetitionCap c by omega)
    · simpa only [Function.update_of_ne he] using hr m hm
  have hn := nonfreeSize_box_bound h c (Function.update r μ (r μ+1)) u hh hc hr' hu
  rwa [nonfreeSize_step_r h μ r u hμ] at hn

theorem shared_step_box_bound (h c μ : ℕ) (r u : ℕ → ℕ) (hh : 1≤h)
    (hc : (32*h^3)^10≤c) (hμ : μ∈Icc 2 h)
    (hr : ∀ m∈Icc 2 h,r m≤repetitionCap c)
    (hu : ∀ m∈Icc 2 h,u m≤sharedCap c) (hs : u μ<sharedCap c) :
    8*h*(nonfreeSize h r u+μ)≤c := by
  have hu' : ∀ m∈Icc 2 h,Function.update u μ (u μ+1) m≤sharedCap c := by
    intro m hm
    by_cases he : m=μ
    · subst m
      simpa only [Function.update_self] using (show u μ+1≤sharedCap c by omega)
    · simpa only [Function.update_of_ne he] using hu m hm
  have hn := nonfreeSize_box_bound h c r (Function.update u μ (u μ+1)) hh hc hr hu'
  rwa [nonfreeSize_step_u h μ r u hμ] at hn

end SumsetRanges
