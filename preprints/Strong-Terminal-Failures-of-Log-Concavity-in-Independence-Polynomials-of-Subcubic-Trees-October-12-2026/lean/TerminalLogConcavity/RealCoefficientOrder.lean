import TerminalLogConcavity.CoefficientOrder
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

def RealCoeffLE (p q : ℝ[X]) : Prop := ∀ n, p.coeff n ≤ q.coeff n
def CoeffNonnegative (p : ℝ[X]) : Prop := ∀ n, 0 ≤ p.coeff n
noncomputable def realPolynomial (p : ℕ[X]) : ℝ[X] := p.map (Nat.castRingHom ℝ)

@[simp] theorem realPolynomial_coeff (p : ℕ[X]) (n : ℕ) :
    (realPolynomial p).coeff n = (p.coeff n : ℝ) := by simp [realPolynomial]

theorem realPolynomial_nonnegative (p : ℕ[X]) : CoeffNonnegative (realPolynomial p) := by
  intro n
  rw [realPolynomial_coeff]
  positivity

theorem realPolynomial_mono {p q : ℕ[X]} (h : CoeffLE p q) :
    RealCoeffLE (realPolynomial p) (realPolynomial q) := by
  intro n
  simp only [realPolynomial_coeff]
  exact_mod_cast h n

namespace CoeffNonnegative

theorem zero : CoeffNonnegative (0 : ℝ[X]) := by intro n; simp
theorem one : CoeffNonnegative (1 : ℝ[X]) := by intro n; simp [coeff_one]; split <;> positivity
theorem C {a : ℝ} (ha : 0 ≤ a) : CoeffNonnegative (Polynomial.C a) := by
  intro n
  simp only [coeff_C]
  split <;> positivity

theorem add {p q : ℝ[X]} (hp : CoeffNonnegative p) (hq : CoeffNonnegative q) :
    CoeffNonnegative (p + q) := by
  intro n
  rw [coeff_add]
  exact add_nonneg (hp n) (hq n)

theorem mul {p q : ℝ[X]} (hp : CoeffNonnegative p) (hq : CoeffNonnegative q) :
    CoeffNonnegative (p * q) := by
  intro n
  rw [coeff_mul]
  exact Finset.sum_nonneg (fun ij _ => mul_nonneg (hp ij.1) (hq ij.2))

theorem pow {p : ℝ[X]} (hp : CoeffNonnegative p) (n : ℕ) : CoeffNonnegative (p ^ n) := by
  induction n with
  | zero => exact one
  | succ n ih => simpa only [pow_succ] using ih.mul hp

theorem prod {ι : Type*} (s : Finset ι) {f : ι → ℝ[X]}
    (h : ∀ i ∈ s, CoeffNonnegative (f i)) : CoeffNonnegative (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (h i (by simp)).mul (ih (fun j hj => h j (by simp [hj])))

end CoeffNonnegative

namespace RealCoeffLE

theorem refl (p : ℝ[X]) : RealCoeffLE p p := fun _ => le_rfl
theorem trans {p q r : ℝ[X]} (hpq : RealCoeffLE p q) (hqr : RealCoeffLE q r) :
    RealCoeffLE p r := fun n => (hpq n).trans (hqr n)
theorem nonnegative {p q : ℝ[X]} (hpq : RealCoeffLE p q) (hp : CoeffNonnegative p) :
    CoeffNonnegative q := fun n => (hp n).trans (hpq n)

theorem add {p q r s : ℝ[X]} (hpq : RealCoeffLE p q) (hrs : RealCoeffLE r s) :
    RealCoeffLE (p + r) (q + s) := by
  intro n
  simpa only [coeff_add] using add_le_add (hpq n) (hrs n)

theorem sum {ι : Type*} (s : Finset ι) {f g : ι → ℝ[X]}
    (h : ∀ i ∈ s, RealCoeffLE (f i) (g i)) :
    RealCoeffLE (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  intro n
  simp only [finsetSum_coeff]
  exact Finset.sum_le_sum (fun i hi => h i hi n)

theorem mul {p q r s : ℝ[X]} (hpq : RealCoeffLE p q) (hrs : RealCoeffLE r s)
    (hp : CoeffNonnegative p) (hr : CoeffNonnegative r) :
    RealCoeffLE (p * r) (q * s) := by
  intro n
  simp only [coeff_mul]
  apply Finset.sum_le_sum
  intro ij _
  exact mul_le_mul (hpq ij.1) (hrs ij.2) (hr ij.2) (hpq.nonnegative hp ij.1)

theorem pow {p q : ℝ[X]} (hpq : RealCoeffLE p q) (hp : CoeffNonnegative p) (n : ℕ) :
    RealCoeffLE (p ^ n) (q ^ n) := by
  induction n with
  | zero => exact refl _
  | succ n ih => simpa only [pow_succ] using ih.mul hpq (hp.pow n) hp

theorem scale {p q : ℝ[X]} (hpq : RealCoeffLE p q) {a : ℝ} (ha : 0 ≤ a) :
    RealCoeffLE (C a * p) (C a * q) := by
  intro n
  simpa only [coeff_C_mul] using mul_le_mul_of_nonneg_left (hpq n) ha

theorem prod {ι : Type*} (s : Finset ι) {f g : ι → ℝ[X]}
    (h : ∀ i ∈ s, RealCoeffLE (f i) (g i))
    (hf : ∀ i ∈ s, CoeffNonnegative (f i)) :
    RealCoeffLE (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using refl 1
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact (h i (by simp)).mul
      (ih (fun j hj => h j (by simp [hj])) (fun j hj => hf j (by simp [hj])))
      (hf i (by simp)) (CoeffNonnegative.prod s (fun j hj => hf j (by simp [hj])))

theorem scale_mono {p : ℝ[X]} (hp : CoeffNonnegative p) {a b : ℝ} (hab : a ≤ b) :
    RealCoeffLE (C a * p) (C b * p) := by
  intro n
  simpa only [coeff_C_mul] using mul_le_mul_of_nonneg_right hab (hp n)

theorem le_add_right (p : ℝ[X]) {q : ℝ[X]} (hq : CoeffNonnegative q) :
    RealCoeffLE p (p + q) := by
  intro n
  simpa only [coeff_add] using le_add_of_nonneg_right (hq n)

end RealCoeffLE
end TerminalLogConcavity
