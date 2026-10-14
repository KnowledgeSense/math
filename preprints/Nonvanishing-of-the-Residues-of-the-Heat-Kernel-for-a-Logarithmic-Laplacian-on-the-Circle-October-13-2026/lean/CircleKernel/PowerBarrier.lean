import CircleKernel.DiscreteTail
import Mathlib.Analysis.SpecificLimits.Basic

noncomputable section
open Filter Asymptotics
open scoped Topology
namespace CircleKernel

theorem inverse_power_step_lower (x : ℝ) (hx : 0 < x) (M : ℕ) (hM : 0 < M) :
    1/(x+1)^(M+1) ≤ 1/x^M - 1/(x+1)^M := by
  have hx1 : 0 < x+1 := by linarith
  have hy0 : 0 ≤ x/(x+1) := le_of_lt (div_pos hx hx1)
  have hy1 : x/(x+1) ≤ 1 := (div_le_one hx1).mpr (by linarith)
  have hp := pow_le_of_le_one hy0 hy1 (Nat.ne_of_gt hM)
  rw [div_pow] at hp
  have hpow : x^M*(x+1) ≤ x*(x+1)^M := by
    exact (div_le_div_iff₀ (pow_pos hx1 M) hx1).mp hp
  have hxM := pow_pos hx M
  have hyM := pow_pos hx1 M
  have hstep : 1/(x*(x+1)^M) ≤ 1/x^M-1/(x+1)^M := by
    apply (div_le_iff₀ (mul_pos hx hyM)).mpr
    field_simp
    nlinarith
  calc
    1/(x+1)^(M+1) ≤ 1/(x*(x+1)^M) := by
      apply one_div_le_one_div_of_le (mul_pos hx hyM)
      rw [pow_succ]
      nlinarith
    _ ≤ _ := hstep

theorem inverse_nat_power_limit (M : ℕ) (hM : 0 < M) :
    Tendsto (fun n : ℕ => 1/(n : ℝ)^M) atTop (𝓝 0) := by
  have h := (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop :
    Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (𝓝 0)).pow M
  simpa [one_div, inv_pow, zero_pow (Nat.ne_of_gt hM)] using h

theorem inverse_power_step_scaled (x : ℝ) (hx : 1 ≤ x) (M : ℕ) (hM : 0 < M) :
    1/x^(M+1) ≤ 2^(M+1) * (1/x^M - 1/(x+1)^M) := by
  have hx0 : 0 < x := by linarith
  have hx1 : 0 < x+1 := by linarith
  have hpow : (x+1)^(M+1) ≤ (2*x)^(M+1) := by
    gcongr
    linarith
  have hratio : 1/x^(M+1) ≤ 2^(M+1)/(x+1)^(M+1) := by
    apply (div_le_div_iff₀ (pow_pos hx0 _) (pow_pos hx1 _)).mpr
    simpa only [one_mul, mul_pow] using hpow
  calc
    1/x^(M+1) ≤ 2^(M+1)/(x+1)^(M+1) := hratio
    _ = 2^(M+1) * (1/(x+1)^(M+1)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (inverse_power_step_lower x hx0 M hM) (by positivity)

theorem discrete_tail_power_bound (e : ℕ → ℝ) (M N : ℕ) (hM : 0 < M)
    (C : ℝ) (hC : 0 ≤ C) (he : Tendsto e atTop (𝓝 0))
    (hd : ∀ n, N ≤ n → |e (n+1)-e n| ≤ C/(n : ℝ)^(M+1))
    (n : ℕ) (hn : max N 1 ≤ n) : |e n| ≤ C*2^(M+1)/(n : ℝ)^M := by
  let K : ℝ := C*2^(M+1)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hb : Tendsto (fun n : ℕ => K/(n : ℝ)^M) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using (inverse_nat_power_limit M hM).const_mul K
  apply discrete_tail_barrier e (fun n => K/(n : ℝ)^M) (max N 1) he hb _ n hn
  intro k hk
  have hkN : N ≤ k := le_trans (le_max_left _ _) hk
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast le_trans (le_max_right _ _) hk
  calc
    |e (k+1)-e k| ≤ C/(k : ℝ)^(M+1) := hd k hkN
    _ ≤ C * (2^(M+1) * (1/(k : ℝ)^M - 1/((k : ℝ)+1)^M)) := by
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
        (inverse_power_step_scaled k hk1 M hM) hC
    _ = K/(k : ℝ)^M-K/((k+1 : ℕ) : ℝ)^M := by
      push_cast
      dsimp [K]
      ring

theorem discrete_tail_bigO (e : ℕ → ℝ) (M : ℕ) (hM : 0 < M)
    (he : Tendsto e atTop (𝓝 0))
    (hd : (fun n => e (n+1)-e n) =O[atTop] (fun n : ℕ => 1/(n : ℝ)^(M+1))) :
    e =O[atTop] (fun n : ℕ => 1/(n : ℝ)^M) := by
  obtain ⟨C,hC,hbound⟩ := hd.exists_pos
  obtain ⟨N,hN⟩ := eventually_atTop.mp hbound.bound
  have hd' : ∀ n, N ≤ n → |e (n+1)-e n| ≤ C/(n : ℝ)^(M+1) := by
    intro n hn
    have h := hN n hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ 1/(n : ℝ)^(M+1) by positivity),
      mul_one_div] using h
  apply Asymptotics.IsBigO.of_bound (C*2^(M+1))
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have h := discrete_tail_power_bound e M N hM C (le_of_lt hC) he hd' n hn
  simpa only [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ 1/(n : ℝ)^M by positivity),
    mul_one_div] using h

end CircleKernel
