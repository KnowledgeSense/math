import SumsetRanges.SeriesOrder

open Finset
namespace SumsetRanges

theorem ordinary_carryG_series_bound (m r : ℕ) (hm : 2≤m) :
    SeriesLE (ordinarySeries (carryG m r)) (geometricSeries^(2*r+1)) := by
  rw [carryG_series_geometric m r hm]
  have hp := ((SeriesLE.refl geometricSeries).mul (geometricPolynomial_le_series m)
    (geometricPolynomial_nonneg m) geometricSeries_nonneg).pow
      (geometricSeries_nonneg.mul (geometricPolynomial_nonneg m))
      (geometricSeries_nonneg.mul geometricSeries_nonneg) r
  have hh := (SeriesLE.refl geometricSeries).mul hp
    ((geometricSeries_nonneg.mul (geometricPolynomial_nonneg m)).pow r) geometricSeries_nonneg
  have he : geometricSeries*(geometricSeries*geometricSeries)^r=geometricSeries^(2*r+1) := by
    rw [←pow_two,←pow_mul,pow_succ']
  rw [he] at hh
  exact hh

theorem ordinarySeries_empty : ordinarySeries (∅ : Finset (Fin 0 → ℕ))=1 := by
  apply PowerSeries.ext
  intro q
  cases q with
  | zero => simp [ordinarySeries,ordinarySums]
  | succ q => simp [ordinarySeries,ordinarySums]

theorem ordinary_carryH_step_nonneg (m u : ℕ) (hm : 2≤m) :
    SeriesNonneg (geometricSeries^2*ordinarySeries (carryH m u)-ordinarySeries (carryH m (u+1))) := by
  rw [ordinary_carryH_step m u hm]
  exact ((series_X_pow_nonneg _).mul (geometricSeries_nonneg.pow _)).mul
    (SeriesNonneg.sum _ _ (fun j _ => (geometricPolynomial_nonneg m).pow j))

theorem ordinary_carryH_series_bound (m u : ℕ) (hm : 2≤m) :
    SeriesLE (ordinarySeries (carryH m u)) (geometricSeries^(2*u)) := by
  induction u with
  | zero =>
      have he : carryH m 0=∅ := by simp [carryH]
      rw [he,ordinarySeries_empty]
      simp only [Nat.mul_zero,pow_zero]
      exact SeriesLE.refl _
  | succ u ih =>
      have hs : SeriesLE (ordinarySeries (carryH m (u+1)))
          (geometricSeries^2*ordinarySeries (carryH m u)) := by
        intro n
        have hn := ordinary_carryH_step_nonneg m u hm n
        rw [map_sub] at hn
        omega
      have hb := (SeriesLE.refl (geometricSeries^2)).mul ih (ordinarySeries_nonneg _) (geometricSeries_nonneg.pow _)
      apply hs.trans
      have he : 2*(u+1)=2+2*u := by omega
      simpa only [he,pow_add] using hb

end SumsetRanges
