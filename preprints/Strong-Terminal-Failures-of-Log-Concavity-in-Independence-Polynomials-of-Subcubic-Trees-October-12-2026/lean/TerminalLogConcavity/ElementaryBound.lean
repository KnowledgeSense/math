import TerminalLogConcavity.RealCoefficientOrder
import Mathlib.Algebra.BigOperators.Ring.List

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

noncomputable def elementaryPolynomial : List ℝ[X] → ℕ → ℝ[X]
  | [], 0 => 1
  | [], _ + 1 => 0
  | _ :: _, 0 => 1
  | p :: ps, k + 1 => elementaryPolynomial ps (k + 1) + p * elementaryPolynomial ps k

@[simp] theorem elementaryPolynomial_zero (ps : List ℝ[X]) : elementaryPolynomial ps 0 = 1 := by
  cases ps <;> rfl

theorem elementaryPolynomial_high {ps : List ℝ[X]} {k : ℕ} (hk : ps.length < k) :
    elementaryPolynomial ps k = 0 := by
  induction ps generalizing k with
  | nil => cases k <;> simp_all [elementaryPolynomial]
  | cons p ps ih =>
    cases k with
    | zero => simp at hk
    | succ k =>
      rw [elementaryPolynomial, ih (by simp only [List.length_cons] at hk; omega), ih (by simp only [List.length_cons] at hk; omega)]
      simp

theorem polynomial_list_sum_nonnegative {ps : List ℝ[X]}
    (hp : ∀ p ∈ ps, CoeffNonnegative p) : CoeffNonnegative ps.sum := by
  induction ps with
  | nil => exact CoeffNonnegative.zero
  | cons p ps ih =>
    exact (hp p (by simp)).add (ih (fun p h => hp p (by simp [h])))

theorem elementaryPolynomial_nonnegative {ps : List ℝ[X]}
    (hp : ∀ p ∈ ps, CoeffNonnegative p) (k : ℕ) : CoeffNonnegative (elementaryPolynomial ps k) := by
  induction ps generalizing k with
  | nil => cases k <;> first | exact CoeffNonnegative.one | exact CoeffNonnegative.zero
  | cons p ps ih =>
    cases k with
    | zero => exact CoeffNonnegative.one
    | succ k =>
      have hps := fun p h => hp p (List.mem_cons_of_mem _ h)
      exact (ih hps (k + 1)).add ((hp p (by simp)).mul (ih hps k))

theorem elementaryPolynomial_bound {ps : List ℝ[X]}
    (hp : ∀ p ∈ ps, CoeffNonnegative p) (k : ℕ) :
    RealCoeffLE (elementaryPolynomial ps k) (ps.sum ^ k) := by
  induction ps generalizing k with
  | nil => cases k <;> intro n <;> simp [elementaryPolynomial, coeff_one]
  | cons p ps ih =>
    cases k with
    | zero => exact RealCoeffLE.refl _
    | succ k =>
      have hp0 := hp p (by simp)
      have hps : ∀ r ∈ ps, CoeffNonnegative r := fun r hr => hp r (by simp [hr])
      have hsum := polynomial_list_sum_nonnegative hps
      have he := elementaryPolynomial_nonnegative hps k
      have hfirst := (ih hps (k + 1)).add ((RealCoeffLE.refl p).mul (ih hps k) hp0 he)
      have hbase : RealCoeffLE ps.sum (p + ps.sum) := by
        simpa [add_comm] using RealCoeffLE.le_add_right ps.sum hp0
      have hpow := hbase.pow hsum k
      have hlast := (RealCoeffLE.refl (p + ps.sum)).mul hpow (hp0.add hsum) (hsum.pow k)
      apply hfirst.trans
      convert hlast using 1 <;> simp only [List.sum_cons, pow_succ] <;> ring

theorem product_one_add_eq_elementary (ps : List ℝ[X]) :
    (ps.map (fun p => 1 + p)).prod =
      ∑ k ∈ Finset.range (ps.length + 1), elementaryPolynomial ps k := by
  induction ps with
  | nil => simp [elementaryPolynomial]
  | cons p ps ih =>
    rw [List.map_cons, List.prod_cons, ih, List.length_cons]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [elementaryPolynomial, Finset.sum_add_distrib, ← Finset.mul_sum]
    have hs := Finset.sum_range_succ' (fun k => elementaryPolynomial ps k) (ps.length + 1)
    have hz := elementaryPolynomial_high (ps := ps) (k := ps.length + 1) (by omega)
    rw [Finset.sum_range_succ, hz, add_zero, elementaryPolynomial_zero] at hs
    simp only [hs]
    ring

theorem product_one_add_le_geometric {ps : List ℝ[X]}
    (hp : ∀ p ∈ ps, CoeffNonnegative p) :
    RealCoeffLE (ps.map (fun p => 1 + p)).prod
      (∑ k ∈ Finset.range (ps.length + 1), ps.sum ^ k) := by
  rw [product_one_add_eq_elementary]
  exact RealCoeffLE.sum _ (fun k _ => elementaryPolynomial_bound hp k)

end TerminalLogConcavity
