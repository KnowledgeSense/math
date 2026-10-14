import SumsetRanges.SeriesOrder

open Finset
namespace SumsetRanges

theorem series_constant_le {A : PowerSeries ℤ} (hA : SeriesNonneg A) :
    SeriesLE (PowerSeries.C (PowerSeries.coeff 0 A)) A := by
  intro n
  by_cases hn : n=0
  · subst n; simp
  · simp only [PowerSeries.coeff_C,ite_eq_right hn]
    exact hA n

theorem one_le_geometricSeries : SeriesLE 1 geometricSeries := by
  have he : PowerSeries.coeff 0 geometricSeries=1 := by simp [geometricSeries]
  simpa only [he,map_one] using series_constant_le geometricSeries_nonneg

theorem one_le_geometricPolynomial (m : ℕ) (hm : 1≤m) :
    SeriesLE 1 (geometricPolynomial m : PowerSeries ℤ) := by
  have he : PowerSeries.coeff 0 (geometricPolynomial m : PowerSeries ℤ)=1 := by
    simp [Polynomial.coeff_coe,geometricPolynomial,Polynomial.finsetSum_coeff,
      Polynomial.coeff_X_pow,show 0<m by omega]
  simpa only [he,map_one] using series_constant_le (geometricPolynomial_nonneg m)

theorem geometricSeries_pow_mono (a b : ℕ) (hab : a≤b) :
    SeriesLE (geometricSeries^a) (geometricSeries^b) := by
  induction b,hab using Nat.le_induction with
  | base => exact SeriesLE.refl _
  | succ b _ ih =>
      apply ih.trans
      have he := (SeriesLE.refl (geometricSeries^b)).mul one_le_geometricSeries SeriesNonneg.one (geometricSeries_nonneg.pow b)
      simpa only [mul_one,pow_succ] using he

theorem SeriesLE.sum {ι : Type*} (s : Finset ι) (A B : ι → PowerSeries ℤ)
    (hAB : ∀i∈s,SeriesLE (A i) (B i)) : SeriesLE (∑i∈s,A i) (∑i∈s,B i) := by
  intro n
  simp only [map_sum]
  exact Finset.sum_le_sum (fun i hi => hAB i hi n)

theorem geometricPolynomial_power_sum_bounds (m u : ℕ) (hm : 1≤m) :
    SeriesLE (u : PowerSeries ℤ) (∑j∈range u,(geometricPolynomial m : PowerSeries ℤ)^j) ∧
    SeriesLE (∑j∈range u,(geometricPolynomial m : PowerSeries ℤ)^j)
      ((u : PowerSeries ℤ)*geometricSeries^(u-1)) := by
  constructor
  · have hh := SeriesLE.sum (range u) (fun _ => (1 : PowerSeries ℤ))
      (fun j => (geometricPolynomial m : PowerSeries ℤ)^j) (fun j _ => by
        simpa using (one_le_geometricPolynomial m hm).pow SeriesNonneg.one (geometricPolynomial_nonneg m) j)
    simpa using hh
  · have hh := SeriesLE.sum (range u) (fun j => (geometricPolynomial m : PowerSeries ℤ)^j)
      (fun _ => geometricSeries^(u-1)) (fun j hj =>
        ((geometricPolynomial_le_series m).pow (geometricPolynomial_nonneg m) geometricSeries_nonneg j).trans
          (geometricSeries_pow_mono j (u-1) (by have := mem_range.mp hj; omega)))
    simpa [nsmul_eq_mul] using hh

end SumsetRanges
