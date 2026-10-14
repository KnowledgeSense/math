import SumsetRanges.OrdinaryCarrySteps

open Finset
namespace SumsetRanges

def SeriesNonneg (A : PowerSeries ℤ) : Prop := ∀n,0≤PowerSeries.coeff n A

def SeriesLE (A B : PowerSeries ℤ) : Prop := ∀n,PowerSeries.coeff n A≤PowerSeries.coeff n B

theorem SeriesNonneg.one : SeriesNonneg 1 := by intro n; simp [PowerSeries.coeff_one]; split_ifs <;> omega

theorem SeriesNonneg.mul {A B : PowerSeries ℤ} (hA : SeriesNonneg A) (hB : SeriesNonneg B) : SeriesNonneg (A*B) := by
  intro n
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_nonneg (fun p _ => mul_nonneg (hA p.1) (hB p.2))

theorem SeriesNonneg.pow {A : PowerSeries ℤ} (hA : SeriesNonneg A) (r : ℕ) : SeriesNonneg (A^r) := by
  induction r with
  | zero => simpa using SeriesNonneg.one
  | succ r ih => simpa only [pow_succ] using ih.mul hA

theorem SeriesNonneg.sum {ι : Type*} (s : Finset ι) (A : ι → PowerSeries ℤ)
    (hA : ∀i∈s,SeriesNonneg (A i)) : SeriesNonneg (∑i∈s,A i) := by
  intro n
  rw [map_sum]
  exact Finset.sum_nonneg (fun i hi => hA i hi n)

theorem SeriesLE.refl (A : PowerSeries ℤ) : SeriesLE A A := fun _ => le_refl _

theorem SeriesLE.trans {A B C : PowerSeries ℤ} (hAB : SeriesLE A B) (hBC : SeriesLE B C) : SeriesLE A C :=
  fun n => (hAB n).trans (hBC n)

theorem SeriesLE.mul {A B C D : PowerSeries ℤ} (hAB : SeriesLE A B) (hCD : SeriesLE C D)
    (hC : SeriesNonneg C) (hB : SeriesNonneg B) : SeriesLE (A*C) (B*D) := by
  intro n
  simp only [PowerSeries.coeff_mul]
  exact Finset.sum_le_sum (fun p _ => mul_le_mul (hAB p.1) (hCD p.2) (hC p.2) (hB p.1))

theorem SeriesLE.pow {A B : PowerSeries ℤ} (hAB : SeriesLE A B) (hA : SeriesNonneg A)
    (hB : SeriesNonneg B) (r : ℕ) : SeriesLE (A^r) (B^r) := by
  induction r with
  | zero => exact SeriesLE.refl _
  | succ r ih => simpa only [pow_succ] using ih.mul hAB hA (hB.pow r)

theorem geometricSeries_nonneg : SeriesNonneg geometricSeries := by
  intro n; simp [geometricSeries]

theorem ordinarySeries_nonneg {α : Type*} [AddCommMonoid α] [DecidableEq α] (A : Finset α) : SeriesNonneg (ordinarySeries A) := by
  intro n; rw [coeff_ordinarySeries]; positivity

theorem geometricPolynomial_nonneg (m : ℕ) : SeriesNonneg (geometricPolynomial m : PowerSeries ℤ) := by
  intro n
  simp [Polynomial.coeff_coe,geometricPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow]
  split_ifs <;> omega

theorem geometricPolynomial_le_series (m : ℕ) : SeriesLE (geometricPolynomial m : PowerSeries ℤ) geometricSeries := by
  intro n
  simp [Polynomial.coeff_coe,geometricPolynomial,Polynomial.finsetSum_coeff,Polynomial.coeff_X_pow,geometricSeries]
  split_ifs <;> omega

theorem series_X_pow_nonneg (n : ℕ) : SeriesNonneg (PowerSeries.X^n) := by
  intro i
  simp [PowerSeries.coeff_X_pow]
  split_ifs <;> omega

end SumsetRanges
