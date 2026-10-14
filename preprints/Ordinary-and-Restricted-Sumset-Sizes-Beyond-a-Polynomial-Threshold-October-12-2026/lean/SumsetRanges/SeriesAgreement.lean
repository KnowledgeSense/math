import SumsetRanges.CarryEnumeration
import SumsetRanges.OrdinarySeries
import Mathlib.RingTheory.PowerSeries.WellKnown

open Finset
namespace SumsetRanges

/-- Equality of coefficients through a specified degree. -/
def AgreeThrough (q : ℕ) (A B : PowerSeries ℤ) : Prop :=
  ∀i≤q,PowerSeries.coeff i A=PowerSeries.coeff i B

theorem AgreeThrough.mul {q : ℕ} {A B C D : PowerSeries ℤ}
    (hAB : AgreeThrough q A B) (hCD : AgreeThrough q C D) :
    AgreeThrough q (A*C) (B*D) := by
  intro i hi
  simp only [PowerSeries.coeff_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hh := Finset.mem_antidiagonal.mp hp
  rw [hAB p.1 (by omega),hCD p.2 (by omega)]

theorem AgreeThrough.pow {q : ℕ} {A B : PowerSeries ℤ}
    (hAB : AgreeThrough q A B) (r : ℕ) : AgreeThrough q (A^r) (B^r) := by
  induction r with
  | zero => intro i hi; simp
  | succ r ih => simpa only [pow_succ] using ih.mul hAB

noncomputable def geometricSeries : PowerSeries ℤ := PowerSeries.mk (fun _ => 1)

theorem geometric_agree (q : ℕ) :
    AgreeThrough q ((geometricPolynomial (q+1) : Polynomial ℤ) : PowerSeries ℤ) geometricSeries := by
  intro i hi
  simp [Polynomial.coeff_coe,geometricPolynomial,Polynomial.finsetSum_coeff,
    Polynomial.coeff_X_pow,geometricSeries,show i<q+1 by omega]

theorem carryG_series_geometric (m r : ℕ) (hm : 2≤m) :
    ordinarySeries (carryG m r)=
      geometricSeries*(geometricSeries*(geometricPolynomial m : PowerSeries ℤ))^r := by
  apply PowerSeries.ext
  intro q
  rw [coeff_ordinarySeries,←coeff_carryG_geometric m r q hm]
  have hh := (geometric_agree q).mul (((geometric_agree q).mul
    (show AgreeThrough q (geometricPolynomial m : PowerSeries ℤ) (geometricPolynomial m : PowerSeries ℤ) from fun _ _ => rfl)).pow r)
  have he := hh q (le_refl _)
  simpa only [←Polynomial.coe_mul,←Polynomial.coe_pow,Polynomial.coeff_coe] using he

end SumsetRanges
