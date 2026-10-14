import SumsetRanges.OrdinaryBaselineGluing
import SumsetRanges.OrdinaryLargeRealization

open Finset
namespace SumsetRanges

theorem coeff_geometric_pow_one (c : ℕ) : PowerSeries.coeff 1 (geometricSeries^c)=(c:ℤ) := by
  by_cases hc : c=0
  · subst c; simp
  · rw [coeff_geometricSeries_pow c 1 (by omega)]
    simp [ordinaryBeta]

theorem twice_coeff_geometric_pow_two (c : ℕ) :
    2*PowerSeries.coeff 2 (geometricSeries^c)=(c:ℤ)*(c+1) := by
  by_cases hc : c=0
  · subst c; simp
  · rw [coeff_geometricSeries_pow c 2 (by omega)]
    have he := ordinaryBeta_recurrence c 1 (by omega)
    simp [ordinaryBeta] at he
    exact_mod_cast he.symm.trans (Nat.mul_comm _ _)

theorem ordinary_baseline_two (c b x : ℕ) (hb : 2≤b) (hx : b-1≤x) :
    2*ordinaryBaselineValue 2 c b x=(c:ℤ)*(c+1)+2*c*b+
      2*((ordinarySums (denseSet (b-1) x) 2).card:ℤ) := by
  rw [ordinaryBaselineValue,series_coeff_mul_reversed]
  have hcB : (denseSet (b-1) x).card=b := by
    rw [card_denseSet _ _ hx]
    omega
  have he := twice_coeff_geometric_pow_two c
  norm_num [Finset.sum_range_succ,coeff_geometric_pow_one,
    coeff_ordinarySeries,ordinarySums,hcB]
  nlinarith

end SumsetRanges
