import R34.SchurIsing
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.LinearCombination

noncomputable section

namespace R34

open MvPolynomial
open scoped BigOperators

theorem h_two_step (n : ℕ) : h (n+2) = U*h (n+1)-V*h n := by
  rw [h_succ (n+1), h_succ n]
  unfold U V
  simp only [pow_succ]
  ring

def homogeneousSeries : PowerSeries Poly :=
  PowerSeries.mk (fun n => C ((2 : ℝ)^n)*h n)

def uniformSeries (f : ℕ → Poly) : PowerSeries Poly :=
  PowerSeries.mk (fun n => if n=0 then 1 else C (2 : ℝ)*f n)

def denominator : PowerSeries Poly :=
  1-PowerSeries.C (C (2 : ℝ)*U)*PowerSeries.X+
    PowerSeries.C (C (4 : ℝ)*V)*PowerSeries.X^2

theorem quadratic_coeff (g : PowerSeries Poly) (a b : Poly) (n : ℕ) :
    PowerSeries.coeff (n+2) (g-(PowerSeries.C a*g)*PowerSeries.X+
      (PowerSeries.C b*g)*PowerSeries.X^2) =
    PowerSeries.coeff (n+2) g-a*PowerSeries.coeff (n+1) g+b*PowerSeries.coeff n g := by
  simp only [map_add, map_sub, PowerSeries.coeff_succ_mul_X,
    PowerSeries.coeff_mul_X_pow, PowerSeries.coeff_C_mul]

theorem denominator_homogeneousSeries : denominator*homogeneousSeries=1 := by
  have he : denominator*homogeneousSeries = homogeneousSeries-
      (PowerSeries.C (C 2*U)*homogeneousSeries)*PowerSeries.X+
      (PowerSeries.C (C 4*V)*homogeneousSeries)*PowerSeries.X^2 := by
    unfold denominator
    ring
  rw [he]
  apply PowerSeries.ext
  intro n
  rcases n with _ | n
  · simp [homogeneousSeries]
  rcases n with _ | n
  · simp [homogeneousSeries, PowerSeries.coeff_mul_X_pow']
  · change PowerSeries.coeff (n+2) _ = _
    rw [quadratic_coeff]
    simp only [homogeneousSeries, PowerSeries.coeff_mk, PowerSeries.coeff_one,
      Nat.add_eq_zero_iff]
    rw [h_two_step]
    simp only [pow_succ, C_mul]
    have h4 : (C (4 : ℝ) : Poly) = C 2*C 2 := by rw [← C_mul]; norm_num
    rw [h4]
    simp only [Nat.one_ne_zero, and_false, ite_false]
    ring

theorem uniformSeries_recurrence (f : ℕ → Poly)
    (hone : f 1=U) (htwo : f 2=C (2 : ℝ)*h 2)
    (hrec : ∀ n, f (n+3)=C (2 : ℝ)*U*f (n+2)-C (3 : ℝ)*V*f (n+1)) :
    (denominator-PowerSeries.C V*PowerSeries.X^2)*uniformSeries f =
      1-PowerSeries.C V*PowerSeries.X^2 := by
  have hconst : (C (4 : ℝ) : Poly)-1=C 3 := by
    rw [← C_1, ← C_sub]
    norm_num
  have he : (denominator-PowerSeries.C V*PowerSeries.X^2)*uniformSeries f =
      uniformSeries f-(PowerSeries.C (C 2*U)*uniformSeries f)*PowerSeries.X+
      (PowerSeries.C (C 3*V)*uniformSeries f)*PowerSeries.X^2 := by
    unfold denominator
    have hc : (C (4 : ℝ) : Poly)*V-V=C 3*V := by linear_combination V*hconst
    have hc' := congrArg PowerSeries.C hc
    simp only [map_sub, map_mul] at hc'
    simp only [map_mul]
    linear_combination uniformSeries f*PowerSeries.X^2*hc'
  rw [he]
  apply PowerSeries.ext
  intro n
  rcases n with _ | n
  · simp [uniformSeries]
  rcases n with _ | n
  · simp [uniformSeries, hone, PowerSeries.coeff_mul_X_pow']
  rcases n with _ | n
  · rw [quadratic_coeff]
    simp [uniformSeries, hone, htwo]
    rw [h_succ 1, h_one]
    unfold U V
    have h4 : (C (4 : ℝ) : Poly) = C 2*C 2 := by rw [← C_mul]; norm_num
    have h3 : (C (3 : ℝ) : Poly) = C 2*C 2-1 := by rw [← h4, ← C_1, ← C_sub]; norm_num
    rw [h3]
    ring
  · change PowerSeries.coeff ((n+1)+2) _ = _
    rw [quadratic_coeff]
    simp only [uniformSeries, PowerSeries.coeff_mk,
      Nat.succ_ne_zero, ite_false]
    rw [hrec]
    simp
    ring

theorem uniformSeries_positive_equation (f : ℕ → Poly)
    (hone : f 1=U) (htwo : f 2=C (2 : ℝ)*h 2)
    (hrec : ∀ n, f (n+3)=C (2 : ℝ)*U*f (n+2)-C (3 : ℝ)*V*f (n+1)) :
    uniformSeries f = homogeneousSeries+
      (PowerSeries.C V*(homogeneousSeries*(uniformSeries f-1)))*PowerSeries.X^2 := by
  have hrec' := uniformSeries_recurrence f hone htwo hrec
  have he : denominator*uniformSeries f = 1-PowerSeries.C V*PowerSeries.X^2+
      PowerSeries.C V*PowerSeries.X^2*uniformSeries f := by linear_combination hrec'
  calc
    uniformSeries f = homogeneousSeries*(denominator*uniformSeries f) := by
      rw [← mul_assoc, mul_comm homogeneousSeries denominator, denominator_homogeneousSeries]
      simp
    _ = homogeneousSeries*(1-PowerSeries.C V*PowerSeries.X^2+
      PowerSeries.C V*PowerSeries.X^2*uniformSeries f) := by rw [he]
    _ = homogeneousSeries+
      (PowerSeries.C V*(homogeneousSeries*(uniformSeries f-1)))*PowerSeries.X^2 := by ring

theorem homogeneousSeries_coeff_schurPositive (n : ℕ) :
    SchurPositive (PowerSeries.coeff n homogeneousSeries) := by
  simp only [homogeneousSeries, PowerSeries.coeff_mk]
  exact schurPositive_scale _ (pow_nonneg (by norm_num) _) (schurPositive_h n)

theorem uniformSeries_coeff_schurPositive (f : ℕ → Poly)
    (hone : f 1=U) (htwo : f 2=C (2 : ℝ)*h 2)
    (hrec : ∀ n, f (n+3)=C (2 : ℝ)*U*f (n+2)-C (3 : ℝ)*V*f (n+1))
    (n : ℕ) : SchurPositive (PowerSeries.coeff n (uniformSeries f)) := by
  have he := uniformSeries_positive_equation f hone htwo hrec
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hn := congrArg (PowerSeries.coeff n) he
    rw [map_add] at hn
    by_cases hsmall : n<2
    · rw [PowerSeries.coeff_mul_X_pow', ite_eq_right (by omega), add_zero] at hn
      rw [hn]
      exact homogeneousSeries_coeff_schurPositive n
    · have hindex : n=(n-2)+2 := by omega
      rw [hindex, PowerSeries.coeff_mul_X_pow, PowerSeries.coeff_C_mul,
        PowerSeries.coeff_mul] at hn
      rw [hindex, hn]
      apply schurPositive_add (homogeneousSeries_coeff_schurPositive _)
      apply schurPositive_mul schurPositive_V
      apply schurPositive_sum
      intro ij hij
      apply schurPositive_mul (homogeneousSeries_coeff_schurPositive _)
      have hsum := Finset.mem_antidiagonal.mp hij
      by_cases hj : ij.2=0
      · simp [hj, uniformSeries]
        exact SchurPositive.zero
      · have hjlt : ij.2<n := by omega
        simpa [map_sub, PowerSeries.coeff_one, hj] using ih ij.2 hjlt

theorem schurPositive_of_uniform_recurrence (f : ℕ → Poly)
    (hone : f 1=U) (htwo : f 2=C (2 : ℝ)*h 2)
    (hrec : ∀ n, f (n+3)=C (2 : ℝ)*U*f (n+2)-C (3 : ℝ)*V*f (n+1))
    (n : ℕ) : SchurPositive (f (n+1)) := by
  have hp := uniformSeries_coeff_schurPositive f hone htwo hrec (n+1)
  simp only [uniformSeries, PowerSeries.coeff_mk, Nat.add_eq_zero_iff,
    Nat.one_ne_zero, and_false, ite_false] at hp
  have hp' := schurPositive_scale (1/2) (by norm_num) hp
  have he : (C (1/2 : ℝ) : Poly)*(C 2*f (n+1))=f (n+1) := by
    rw [← mul_assoc, ← C_mul]
    norm_num
  rwa [he] at hp'

end R34






