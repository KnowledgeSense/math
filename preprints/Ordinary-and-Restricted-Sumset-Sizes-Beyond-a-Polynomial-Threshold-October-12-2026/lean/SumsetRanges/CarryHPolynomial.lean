import SumsetRanges.CarryHEnumeration
import SumsetRanges.CarryGSeries
import Mathlib.Algebra.Ring.GeomSum

open Finset Polynomial
namespace SumsetRanges

noncomputable def carryHPolynomial (m r q : ℕ) : Polynomial ℤ :=
  weightPolynomial (@carryHDegree m r q)

theorem carryHPolynomial_agree (m r q : ℕ) (hm : 2≤m) :
    AgreeThrough q (carryHPolynomial m r q : PowerSeries ℤ) (ordinarySeries (carryH m r)) := by
  intro i hi
  rw [Polynomial.coeff_coe,coeff_ordinarySeries,carryHPolynomial,coeff_weightPolynomial,
    card_carryH_normal_bound m r q i hm hi]

theorem carryRowWeight_polynomial (m r q : ℕ) :
    weightPolynomial (@carryRowWeight m r q) =
      (geometricPolynomial (q+1)*geometricPolynomial m)^r := by
  unfold carryRowWeight
  rw [weightPolynomial_pi (fun _ (a : Fin (q+1) × Fin m) => a.1.val+a.2.val)]
  simp only [weightPolynomial_prod,weightPolynomial_fin,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem carryRowMass_polynomial (m r q : ℕ) :
    weightPolynomial (fun a : CarryRows m r q => ∑i,carryRowVector a i) =
      (geometricPolynomial ((q+1)*m))^r := by
  unfold carryRowVector
  rw [weightPolynomial_pi (fun _ (a : Fin (q+1) × Fin m) => m*a.1.val+a.2.val)]
  have he : weightPolynomial (fun a : Fin (q+1) × Fin m => m*a.1.val+a.2.val)=
      geometricPolynomial ((q+1)*m) := by
    calc
      _ = weightPolynomial ((fun i : Fin ((q+1)*m) => i.val) ∘ finProdFinEquiv) := by
        congr 1; funext a; simp [finProdFinEquiv,Nat.add_comm]
      _ = _ := by rw [weightPolynomial_equiv,weightPolynomial_fin]
  simp only [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem carryRow_mass_identity (m r q : ℕ) (hm : 1≤m) (a : CarryRows m r q) :
    carryRowWeight a+(m-1)*carryRowQuotient a=∑i,carryRowVector a i := by
  unfold carryRowWeight carryRowQuotient carryRowVector
  rw [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have he : m-1+1=m := by omega
  calc
    _ = ((m-1)+1)*(a i).1.val+(a i).2.val := by ring
    _ = _ := by rw [he]

theorem carryHPolynomial_identity (m r q : ℕ) (hm : 1≤m) :
    carryHPolynomial m r q*(1-X^(m-1))=
      (geometricPolynomial (q+1)*geometricPolynomial m)^r-
        X^(m-1)*(geometricPolynomial ((q+1)*m))^r := by
  rw [←carryRowWeight_polynomial,←carryRowMass_polynomial]
  unfold carryHPolynomial weightPolynomial carryHDegree
  rw [Fintype.sum_sigma,Finset.sum_mul,Finset.mul_sum,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  simp only [pow_add,pow_mul]
  rw [←Finset.mul_sum,mul_assoc,Fin.sum_univ_eq_sum_range,geom_sum_mul_neg]
  have he := carryRow_mass_identity m r q hm a
  rw [←pow_mul]
  calc
    _ = X^carryRowWeight a-X^(carryRowWeight a+(m-1)*carryRowQuotient a+(m-1)) := by
      rw [mul_sub,mul_one,←pow_add]
      congr 2; ring
    _ = _ := by rw [he,pow_add]; ring

end SumsetRanges
