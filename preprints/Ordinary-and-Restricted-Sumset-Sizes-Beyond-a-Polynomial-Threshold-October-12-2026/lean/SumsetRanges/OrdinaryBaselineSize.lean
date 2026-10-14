import SumsetRanges.OrdinaryLargeChain

open Finset
namespace SumsetRanges

theorem ordinaryBeta_le_pow (c d : ℕ) (hc : 1≤c) : ordinaryBeta c d≤c^d := by
  induction d with
  | zero => simp [ordinaryBeta]
  | succ d ih =>
    have he := ordinaryBeta_recurrence c d hc
    have hb : c+d≤(d+1)*c := by nlinarith
    have hb' := Nat.mul_le_mul_right (ordinaryBeta c d) hb
    have hi := Nat.mul_le_mul_left c ih
    rw [pow_succ]
    nlinarith

theorem ordinary_baseline_size_bound (h c b : ℕ) (hh : 2≤h) (hc : 2*h≤c) (hb : 2≤b) :
    ordinaryBaselineValue h c b (b-1)≤3*(h:ℤ)*(c+b)*(c:ℤ)^(h-1) := by
  have hd : denseSet (b-1) (b-1)=Icc 0 (b-1) := by
    have he : b-1=b-2+1 := by omega
    rw [he,denseSet_ordinary_minimum]
  rw [ordinaryBaselineValue,hd,series_coeff_mul_reversed,Finset.sum_range_succ']
  simp only [coeff_ordinarySeries,ordinarySums_nat_Icc,Nat.card_Icc,Nat.sub_zero,
    Nat.zero_mul,Nat.zero_add,Nat.cast_one,one_mul]
  simp_rw [coeff_geometricSeries_pow c _ (by omega)]
  have htail : (∑e∈range h,(((e+1)*(b-1)+1:ℕ):ℤ)*(ordinaryBeta c (h-(e+1)):ℤ))≤
      (h:ℤ)*b*(∑e∈range h,(ordinaryBeta c (h-(e+1)):ℤ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e he
    have heh : e+1≤h := by have := mem_range.mp he; omega
    have hb' : (e+1)*(b-1)+1≤h*b := by
      have hp := Nat.mul_le_mul_right (b-1) heh
      have heq : b-1+1=b := by omega
      nlinarith
    apply mul_le_mul_of_nonneg_right _ (Int.natCast_nonneg _)
    exact_mod_cast hb'
  have hsum : (∑e∈range h,(ordinaryBeta c (h-(e+1)):ℤ))=∑e∈range h,(ordinaryBeta c e:ℤ) := by
    refine Finset.sum_bij (fun e _ => h-(e+1)) ?_ ?_ ?_ ?_
    · intro e he; simp only [mem_range] at *; omega
    · intro e he f hf hef; simp only [mem_range] at he hf; omega
    · intro e he; refine ⟨h-(e+1),?_,?_⟩ <;> simp only [mem_range] at * <;> omega
    · intro e he; rfl
  rw [hsum] at htail
  have hpart : (∑e∈range h,(ordinaryBeta c e:ℤ))≤2*(ordinaryBeta c (h-1):ℤ) := by
    have he : h-1+1=h := by omega
    exact_mod_cast (he ▸ ordinaryBeta_partial_sum h c (h-1) (by omega) hc (by omega))
  have hm := mul_le_mul_of_nonneg_left hpart (by positivity : (0:ℤ)≤h*b)
  have h0 : (ordinaryBeta c h:ℤ)≤(c:ℤ)^h := by exact_mod_cast ordinaryBeta_le_pow c h (by omega)
  have h1 : (ordinaryBeta c (h-1):ℤ)≤(c:ℤ)^(h-1) := by exact_mod_cast ordinaryBeta_le_pow c (h-1) (by omega)
  have h1m := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℤ)≤2*h*b)
  have hp : (c:ℤ)^h=(c:ℤ)*(c:ℤ)^(h-1) := by
    have he : h=h-1+1 := by omega
    conv_lhs => rw [he,pow_succ]
    ring
  have hs : (c:ℤ)+2*h*b≤3*(h:ℤ)*(c+b) := by
    have hh' : (2:ℤ)≤h := by exact_mod_cast hh
    nlinarith
  have hfinal := mul_le_mul_of_nonneg_right hs (by positivity : (0:ℤ)≤(c:ℤ)^(h-1))
  nlinarith

theorem ordinary_large_range (h k K : ℕ) (hh : 3≤h) (hK : (32*h^3)^10≤K)
    (hKk : K+2≤k) (hkK : sparseThreshold k≤K) (z : ℤ)
    (hz : 3*(h:ℤ)*k*(K:ℤ)^(h-1)≤z) (hzt : z≤((h+k-1).choose h:ℤ)) :
    ∃B : Finset ℤ,B.card=k ∧ (∀a∈B,0≤a ∧ a≤(k^(ordinaryExponent h):ℕ)) ∧
      ((ordinarySums B h).card:ℤ)=z := by
  apply ordinary_large_chain h k K hh hK hKk hkK z _ hzt
  have hc := (large_c_elementary (by omega : 1≤h) hK).2
  have hb := ordinary_baseline_size_bound h K (k-K) (by omega) (by nlinarith) (by omega)
  have he : (K:ℤ)+((k-K:ℕ):ℤ)=k := by omega
  rw [he] at hb
  exact hb.trans hz

end SumsetRanges
