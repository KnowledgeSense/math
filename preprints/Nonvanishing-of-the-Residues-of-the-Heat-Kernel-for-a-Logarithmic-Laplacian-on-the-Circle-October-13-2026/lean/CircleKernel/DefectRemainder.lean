import CircleKernel.DefectPolynomial
import CircleKernel.TaylorSeries
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.Asymptotics.Lemmas

noncomputable section
open Filter Asymptotics Finset Polynomial
open scoped Topology
namespace CircleKernel

def harmonicDefect (M : ℕ) (x : ℝ) : ℝ :=
  Real.log (1+x) + ∑ j ∈ range M,
    (-(bernoulli (j+1) : ℝ)/(j+1)) * x^(j+1) * (1/(1+x)^(j+1)-1) - x/(1+x)

@[simp] theorem inverseTaylor_eval (k M : ℕ) (x : ℝ) :
    (inverseTaylor k M).eval₂ (Rat.castHom ℝ) x =
      ∑ j ∈ range M, (-1 : ℝ)^j * ((k+j).choose k : ℝ) * x^j := by
  simp [inverseTaylor, eval₂_finsetSum, Rat.cast_pow, Rat.cast_mul]
@[simp] theorem logTaylor_eval (M : ℕ) (x : ℝ) :
    (logTaylor M).eval₂ (Rat.castHom ℝ) x =
      ∑ j ∈ range M, (-(-1 : ℝ)^j/(j : ℝ)) * x^j := by
  simp [logTaylor, eval₂_finsetSum]

theorem polynomial_divisible_bigO (p : ℚ[X]) (N : ℕ) (hp : X^N ∣ p) :
    (fun x : ℝ => p.eval₂ (Rat.castHom ℝ) x) =O[𝓝 0] (fun x : ℝ => ‖x‖^N) := by
  obtain ⟨q, rfl⟩ := hp
  have hq : (fun x : ℝ => q.eval₂ (Rat.castHom ℝ) x) =O[𝓝 0] (fun _ => (1 : ℝ)) :=
    (q.continuous_eval₂ (Rat.castHom ℝ)).continuousAt.isBigO
  have hx := (isBigO_refl (fun x : ℝ => x^N) (𝓝 0)).mul hq
  simpa only [eval₂_mul, eval₂_pow, eval₂_X, mul_one, ← norm_pow,
    isBigO_norm_right] using hx

theorem harmonicDefect_sub_polynomial (M : ℕ) :
    (fun x : ℝ => harmonicDefect M x -
      (defectPolynomial M).eval₂ (Rat.castHom ℝ) x) =O[𝓝 0]
        (fun x : ℝ => ‖x‖^(M+1)) := by
  have hs : (fun x : ℝ => ∑ j ∈ range M,
      (-(bernoulli (j+1) : ℝ)/(j+1)) * x^(j+1) *
        (1/(1+x)^(j+1) - (inverseTaylor j (M+1)).eval₂ (Rat.castHom ℝ) x))
      =O[𝓝 0] (fun x : ℝ => ‖x‖^(M+1)) := by
    have ht : ∀ j ∈ range M, (fun x : ℝ =>
        (-(bernoulli (j+1) : ℝ)/(j+1)) * x^(j+1) *
          (1/(1+x)^(j+1) - (inverseTaylor j (M+1)).eval₂ (Rat.castHom ℝ) x))
        =O[𝓝 0] (fun x : ℝ => ‖x‖^(M+1)) := by
      intro j hj
      have hb : (fun x : ℝ => (-(bernoulli (j+1) : ℝ)/(j+1)) * x^(j+1))
          =O[𝓝 0] (fun _ => (1 : ℝ)) := by
        apply ContinuousAt.isBigO
        fun_prop
      have he := inverse_power_taylor j (M+1)
      simpa only [one_mul, inverseTaylor_eval] using hb.mul he
    exact (IsBigO.sum ht).congr_left (fun x => by simp)
  have hl := log_one_add_taylor (M+1)
  have hb : (fun x : ℝ => x) =O[𝓝 0] (fun _ => (1 : ℝ)) :=
    continuousAt_id.isBigO
  have he := hb.mul (inverse_power_taylor 0 (M+1))
  simp only [one_mul, Nat.zero_add, pow_one] at he
  have hall := (hl.add hs).sub he
  apply hall.congr_left
  intro x
  simp only [harmonicDefect, defectPolynomial, eval₂_sub, eval₂_add, eval₂_finsetSum,
    eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, eval₂_one, Rat.coe_castHom,
    Rat.cast_div, Rat.cast_neg, Rat.cast_add, Rat.cast_natCast, Rat.cast_one, inverseTaylor_eval, logTaylor_eval,
    Nat.zero_add, Nat.choose_zero_right, Nat.cast_one, mul_one]
  have hsx : (∑ j ∈ range M, (-(bernoulli (j+1) : ℝ)/(j+1)) * x^(j+1) *
      (1/(1+x)^(j+1)-1) -
      (∑ j ∈ range M, (-(bernoulli (j+1) : ℝ)/(j+1)) * x^(j+1) *
        ((∑ i ∈ range (M+1), (-1 : ℝ)^i*((j+i).choose j : ℝ)*x^i)-1))) =
      ∑ j ∈ range M, (-(bernoulli (j+1) : ℝ)/(j+1)) * x^(j+1) *
        (1/(1+x)^(j+1)-(∑ i ∈ range (M+1), (-1 : ℝ)^i*((j+i).choose j : ℝ)*x^i)) := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro j hj
    ring
  linear_combination -hsx

theorem harmonicDefect_bigO (M : ℕ) :
    harmonicDefect M =O[𝓝 0] (fun x : ℝ => ‖x‖^(M+1)) := by
  have h := (harmonicDefect_sub_polynomial M).add
    (polynomial_divisible_bigO _ _ (defectPolynomial_divisible M))
  simpa only [sub_add_cancel] using h

end CircleKernel
