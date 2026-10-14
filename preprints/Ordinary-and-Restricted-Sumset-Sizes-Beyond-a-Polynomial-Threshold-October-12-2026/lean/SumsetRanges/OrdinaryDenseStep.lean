import SumsetRanges.OrdinaryValueSteps

open Finset
namespace SumsetRanges

theorem ordinaryValue_dense_step (h c b x : ℕ) (r u : ℕ → ℕ)
    (hh : 2≤h) (hc : 2*h≤c) (hb : 2≤b) (hx : b-1≤x)
    (hn : ordinaryNonfreeSize h r u≤c) :
    0≤ordinaryValue h c b r u (x+1)-ordinaryValue h c b r u x ∧
    ordinaryValue h c b r u (x+1)-ordinaryValue h c b r u x≤2*h*(ordinaryBeta c (h-2) : ℤ) := by
  let P := ordinarySparseSeries h c r u
  let Y := ordinarySeries (denseSet (b-1) (x+1))-ordinarySeries (denseSet (b-1) x)
  have he : ordinaryValue h c b r u (x+1)-ordinaryValue h c b r u x=PowerSeries.coeff h (P*Y) := by
    simp only [ordinaryValue,P,Y,mul_sub,map_sub]
  rw [he,series_coeff_mul_reversed,sum_range_split_two _ h (by omega)]
  have hy0 : PowerSeries.coeff 0 Y=0 := by simp [Y]
  have hy1 : PowerSeries.coeff 1 Y=0 := by
    simp only [Y,map_sub,coeff_ordinarySeries]
    rw [dense_ordinary_one b (x+1) hb (by omega),dense_ordinary_one b x hb hx]
    omega
  simp only [hy0,hy1,zero_mul,zero_add]
  have hy (e : ℕ) : 0≤PowerSeries.coeff e Y ∧ PowerSeries.coeff e Y≤e := by
    have hb' : b-2+1=b-1 := by omega
    have hs := dense_ordinary_step (b-2) x e (by omega)
    rw [hb'] at hs
    simp only [Y,map_sub,coeff_ordinarySeries]
    have h0 : ((ordinarySums (denseSet (b-1) x) e).card : ℤ)≤
        ((ordinarySums (denseSet (b-1) (x+1)) e).card : ℤ) := by exact_mod_cast hs.1
    have h1 : ((ordinarySums (denseSet (b-1) (x+1)) e).card : ℤ)≤
        ((ordinarySums (denseSet (b-1) x) e).card : ℤ)+e := by exact_mod_cast hs.2
    omega
  have hpn := ordinarySparseSeries_nonneg h c r u
  have hpu := ordinarySparseSeries_upper h c r u hn
  constructor
  · apply Finset.sum_nonneg
    intro e _
    exact mul_nonneg (hy e).1 (hpn (h-e))
  · have hbnd : (∑e∈Icc 2 h,PowerSeries.coeff e Y*PowerSeries.coeff (h-e) P)≤
        (h : ℤ)*∑e∈Icc 2 h,(ordinaryBeta c (h-e) : ℤ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro e he
      have hp := hpu (h-e)
      rw [coeff_geometricSeries_pow c (h-e) (by omega)] at hp
      have heh : (e : ℤ)≤h := by exact_mod_cast (mem_Icc.mp he).2
      have hm := mul_le_mul ((hy e).2.trans heh) hp (hpn (h-e)) (Int.natCast_nonneg h)
      exact hm
    have ht : (∑e∈Icc 2 h,ordinaryBeta c (h-e))≤2*ordinaryBeta c (h-2) := by
      rw [sum_Icc_ordinaryBeta_sub c h (by omega)]
      have he : h-1=(h-2)+1 := by omega
      rw [he]
      exact ordinaryBeta_partial_sum h c (h-2) (by omega) hc (by omega)
    have ht' : (∑e∈Icc 2 h,(ordinaryBeta c (h-e) : ℤ))≤2*(ordinaryBeta c (h-2) : ℤ) := by exact_mod_cast ht
    have hm := mul_le_mul_of_nonneg_left ht' (Int.natCast_nonneg h)
    nlinarith

end SumsetRanges
