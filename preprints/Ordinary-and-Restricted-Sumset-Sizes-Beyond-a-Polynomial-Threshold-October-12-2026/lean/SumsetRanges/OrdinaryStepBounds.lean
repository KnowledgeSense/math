import SumsetRanges.OrdinaryCarryBounds
import SumsetRanges.GeometricSeriesOrder

open Finset
namespace SumsetRanges

theorem series_natCast_nonneg (n : ℕ) : SeriesNonneg (n : PowerSeries ℤ) := by
  intro i
  have he : (n : PowerSeries ℤ)=PowerSeries.C (n : ℤ) := by simp
  rw [he,PowerSeries.coeff_C]
  split_ifs <;> positivity

theorem ordinary_carryH_step_bounds (m u : ℕ) (hm : 2≤m) (hu : 1≤u) :
    SeriesLE ((u : PowerSeries ℤ)*PowerSeries.X^(m+1))
      (geometricSeries^2*ordinarySeries (carryH m u)-ordinarySeries (carryH m (u+1))) ∧
    SeriesLE (geometricSeries^2*ordinarySeries (carryH m u)-ordinarySeries (carryH m (u+1)))
      ((u : PowerSeries ℤ)*PowerSeries.X^(m+1)*geometricSeries^(2*u+2)) := by
  rw [ordinary_carryH_step m u hm]
  have hsum := geometricPolynomial_power_sum_bounds m u (by omega)
  have hgeo : SeriesLE 1 (geometricSeries^(u+3)) := by
    simpa using one_le_geometricSeries.pow SeriesNonneg.one geometricSeries_nonneg (u+3)
  constructor
  · have hh := ((SeriesLE.refl (PowerSeries.X^(m+1))).mul hgeo SeriesNonneg.one (series_X_pow_nonneg _)).mul
      hsum.1 (series_natCast_nonneg _) ((series_X_pow_nonneg _).mul (geometricSeries_nonneg.pow _))
    simpa only [mul_one,mul_comm (PowerSeries.X^(m+1)) (u : PowerSeries ℤ)] using hh
  · have hh := (SeriesLE.refl (PowerSeries.X^(m+1)*geometricSeries^(u+3))).mul hsum.2
      (SeriesNonneg.sum _ _ (fun j _ => (geometricPolynomial_nonneg m).pow j))
      ((series_X_pow_nonneg _).mul (geometricSeries_nonneg.pow _))
    have he : PowerSeries.X^(m+1)*geometricSeries^(u+3)*((u : PowerSeries ℤ)*geometricSeries^(u-1))=
        (u : PowerSeries ℤ)*PowerSeries.X^(m+1)*geometricSeries^(2*u+2) := by
      calc
        _ = (u : PowerSeries ℤ)*PowerSeries.X^(m+1)*(geometricSeries^(u+3)*geometricSeries^(u-1)) := by ring
        _ = _ := by rw [←pow_add]; congr 2; omega
    rw [he] at hh
    exact hh

end SumsetRanges
