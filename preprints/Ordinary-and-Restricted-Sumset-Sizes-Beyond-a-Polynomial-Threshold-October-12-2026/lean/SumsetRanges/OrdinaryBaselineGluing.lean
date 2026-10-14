import SumsetRanges.OrdinaryBaseline
import SumsetRanges.OrdinaryConvolutionBounds
import SumsetRanges.ParameterValue

open Finset
namespace SumsetRanges

noncomputable def ordinaryBaselineValue (h c b x : ℕ) : ℤ :=
  PowerSeries.coeff h (geometricSeries^c*ordinarySeries (denseSet (b-1) x))

theorem ordinary_dense_endpoint_agree (h L : ℕ) :
    AgreeThrough h (ordinarySeries (denseSet (L+1) (h*L+1)))
      (geometricSeries*ordinarySeries (Icc 0 L)) := by
  intro q hq
  rw [coeff_ordinarySeries,dense_ordinary_endpoint h L q hq,series_coeff_mul_reversed]
  simp [geometricSeries,coeff_ordinarySeries]

theorem denseSet_ordinary_minimum (L : ℕ) : denseSet (L+1) (L+1)=Icc 0 (L+1) := by
  ext a
  simp [denseSet,Finset.mem_Icc,Finset.mem_range]
  omega

theorem ordinary_baseline_adjacent (h c b : ℕ) (hb : 3≤b) :
    ordinaryBaselineValue h c b (denseMaximum h b)=
      ordinaryBaselineValue h (c+1) (b-1) (b-2) := by
  have ha := (show AgreeThrough h (geometricSeries^c) (geometricSeries^c) from fun _ _ => rfl).mul
    (ordinary_dense_endpoint_agree h (b-2))
  have he : b-2+1=b-1 := by omega
  have he' : b-1-1=b-2 := by omega
  have hl : b-2=(b-3)+1 := by omega
  unfold ordinaryBaselineValue denseMaximum
  have hav := ha h le_rfl
  rw [he] at hav
  rw [hav,pow_succ,mul_assoc]
  congr 2
  rw [he',hl,denseSet_ordinary_minimum]

theorem ordinarySeries_interval_one : ordinarySeries (Icc 0 1)=geometricSeries^2 := by
  apply PowerSeries.ext
  intro q
  rw [coeff_ordinarySeries,ordinarySums_nat_Icc,coeff_geometricSeries_pow 2 q (by omega)]
  simp [ordinaryBeta,Nat.add_comm,Nat.choose_succ_self_right]

theorem ordinary_baseline_top (h k : ℕ) (hk : 2≤k) :
    ordinaryBaselineValue h (k-2) 2 (denseMaximum h 2)=(Nat.choose (h+k-1) h : ℤ) := by
  have hd : denseSet 1 1=Icc 0 1 := by simpa using denseSet_ordinary_minimum 0
  simp only [ordinaryBaselineValue,denseMaximum,Nat.sub_self,Nat.mul_zero,zero_add]
  norm_num only [Nat.reduceSub]
  rw [hd,ordinarySeries_interval_one,←pow_add,Nat.sub_add_cancel hk,
    coeff_geometricSeries_pow k h (by omega)]
  simp only [ordinaryBeta,Nat.add_comm k h]

end SumsetRanges
