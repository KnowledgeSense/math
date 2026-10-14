import SumsetRanges.OrdinarySparseSteps
import SumsetRanges.OrdinaryBinomialBounds

open Finset
namespace SumsetRanges

theorem ordinaryOther_bound (h m : ℕ) (r u : ℕ → ℕ) :
    SeriesLE (ordinaryOther h m r u)
      (geometricSeries^(∑j∈(Icc 2 (h-1)).erase m,(2*r j+1+2*u j))) := by
  unfold ordinaryOther
  rw [←Finset.prod_pow_eq_pow_sum]
  exact SeriesLE.prod _ _ _ (fun _ _ => (ordinarySeries_nonneg _).mul (ordinarySeries_nonneg _))
    (fun _ _ => geometricSeries_nonneg.pow _)
    (fun j hj => ordinary_block_bound j r u (mem_Icc.mp (mem_erase.mp hj).2).1)

theorem ordinaryNonfreeSize_split (h m : ℕ) (r u : ℕ → ℕ) (hm : m∈Icc 2 (h-1)) :
    ordinaryNonfreeSize h r u=(2*r m+1+2*u m)+∑j∈(Icc 2 (h-1)).erase m,(2*r j+1+2*u j) := by
  unfold ordinaryNonfreeSize
  exact (Finset.add_sum_erase (Icc 2 (h-1)) (fun j => 2*r j+1+2*u j) hm).symm

theorem geometricPolynomial_constant (m : ℕ) (hm : 1≤m) :
    PowerSeries.constantCoeff (geometricPolynomial m : PowerSeries ℤ)=1 := by
  rw [←PowerSeries.coeff_zero_eq_constantCoeff,Polynomial.coeff_coe]
  simp [geometricPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow,show 0<m by omega]

theorem ordinarySharedRemainder_nonneg (h c m : ℕ) (r u : ℕ → ℕ) :
    SeriesNonneg (ordinarySharedRemainder h c m r u) :=
  ((((geometricSeries_nonneg.pow _).mul (geometricSeries_nonneg.pow _)).mul (ordinarySeries_nonneg _)).mul
    (ordinaryOther_nonneg h m r u)).mul
    (SeriesNonneg.sum _ _ (fun j _ => (geometricPolynomial_nonneg m).pow j))

theorem ordinarySharedRemainder_lower (h c m : ℕ) (r u : ℕ → ℕ) (hm : 2≤m) :
    SeriesLE ((u m : PowerSeries ℤ)*geometricSeries^(c-(ordinaryNonfreeSize h r u+2)))
      (ordinarySharedRemainder h c m r u) := by
  let P := geometricSeries^(u m+3)*ordinarySeries (carryG (m+1) (r m))*ordinaryOther h m r u*
    ∑j∈range (u m),(geometricPolynomial m : PowerSeries ℤ)^j
  have hp : SeriesNonneg P :=
    (((geometricSeries_nonneg.pow _).mul (ordinarySeries_nonneg _)).mul (ordinaryOther_nonneg h m r u)).mul
      (SeriesNonneg.sum _ _ (fun j _ => (geometricPolynomial_nonneg m).pow j))
  have h0 : PowerSeries.constantCoeff P=(u m : ℤ) := by
    simp [P,geometricPolynomial_constant m (by omega)]
  have hlow : SeriesLE (u m : PowerSeries ℤ) P := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff,h0,map_natCast] using series_constant_le hp
  have he := (SeriesLE.refl (geometricSeries^(c-(ordinaryNonfreeSize h r u+2)))).mul hlow
    (series_natCast_nonneg _) (geometricSeries_nonneg.pow _)
  simpa only [P,ordinarySharedRemainder,mul_assoc,mul_comm (u m : PowerSeries ℤ)] using he

theorem ordinarySharedRemainder_upper (h c m : ℕ) (r u : ℕ → ℕ)
    (hm : m∈Icc 2 (h-1)) (hu : 1≤u m) (hc : ordinaryNonfreeSize h r u+2≤c) :
    SeriesLE (ordinarySharedRemainder h c m r u) ((u m : PowerSeries ℤ)*geometricSeries^c) := by
  let N := ∑j∈(Icc 2 (h-1)).erase m,(2*r j+1+2*u j)
  have h1 := ((SeriesLE.refl (geometricSeries^(c-(ordinaryNonfreeSize h r u+2)))).mul
    (SeriesLE.refl (geometricSeries^(u m+3))) (geometricSeries_nonneg.pow _) (geometricSeries_nonneg.pow _)).mul
      (ordinary_carryG_series_bound (m+1) (r m) (by have := mem_Icc.mp hm; omega))
      (ordinarySeries_nonneg _) ((geometricSeries_nonneg.pow _).mul (geometricSeries_nonneg.pow _))
  have h2 := h1.mul (ordinaryOther_bound h m r u) (ordinaryOther_nonneg h m r u)
    (((geometricSeries_nonneg.pow _).mul (geometricSeries_nonneg.pow _)).mul (geometricSeries_nonneg.pow _))
  have h3 := h2.mul (geometricPolynomial_power_sum_bounds m (u m) (by have := mem_Icc.mp hm; omega)).2
    (SeriesNonneg.sum _ _ (fun j _ => (geometricPolynomial_nonneg m).pow j))
    ((((geometricSeries_nonneg.pow _).mul (geometricSeries_nonneg.pow _)).mul (geometricSeries_nonneg.pow _)).mul (geometricSeries_nonneg.pow _))
  have hsum := ordinaryNonfreeSize_split h m r u hm
  change ordinaryNonfreeSize h r u=2*r m+1+2*u m+N at hsum
  have hex : c-(ordinaryNonfreeSize h r u+2)+(u m+3)+(2*r m+1)+N+(u m-1)=c := by omega
  have he : geometricSeries^(c-(ordinaryNonfreeSize h r u+2))*geometricSeries^(u m+3)*
      geometricSeries^(2*r m+1)*geometricSeries^N*((u m : PowerSeries ℤ)*geometricSeries^(u m-1))=
      (u m : PowerSeries ℤ)*geometricSeries^c := by
    calc
      _ = (u m : PowerSeries ℤ)*(geometricSeries^(c-(ordinaryNonfreeSize h r u+2))*geometricSeries^(u m+3)*
        geometricSeries^(2*r m+1)*geometricSeries^N*geometricSeries^(u m-1)) := by ring
      _ = _ := by simp only [←pow_add,hex]
  rw [he] at h3
  exact h3

end SumsetRanges
