import SphericalTreeFailures.CharacteristicBounds

namespace SphericalTreeFailures
open Finset Polynomial

theorem weighted_unit_sum_norm_lt {ι : Type*} (s : Finset ι) (a : ι → ℝ) (u : ι → ℂ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hu : ∀ i ∈ s, ‖u i‖ = 1)
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hij : i ≠ j)
    (hai : 0 < a i) (haj : 0 < a j) (hne : u i ≠ u j) :
    ‖∑ k ∈ s, (a k : ℂ) * u k‖ < ∑ k ∈ s, a k := by
  classical
  let t := (s.erase i).erase j
  have hj' : j ∈ s.erase i := mem_erase.mpr ⟨Ne.symm hij, hj⟩
  have hdec (f : ι → ℂ) : ∑ k ∈ s, f k = f i + f j + ∑ k ∈ t, f k := by
    rw [← sum_erase_add s f hi, ← sum_erase_add (s.erase i) f hj']
    dsimp [t]
    abel
  have hdecr : ∑ k ∈ s, a k = a i + a j + ∑ k ∈ t, a k := by
    rw [← sum_erase_add s a hi, ← sum_erase_add (s.erase i) a hj']
    dsimp [t]
    abel
  have hrem : ‖∑ k ∈ t, (a k : ℂ) * u k‖ ≤ ∑ k ∈ t, a k := by
    apply (norm_sum_le _ _).trans
    apply sum_le_sum
    intro k hk
    have hks : k ∈ s := mem_of_mem_erase (mem_of_mem_erase hk)
    simp [hu k hks, abs_of_nonneg (ha k hks)]
  rw [hdec, hdecr]
  exact (norm_add_le _ _).trans_lt
    (add_lt_add_of_lt_of_le (positive_unit_pair_norm_lt hai haj (hu i hi) (hu j hj) hne) hrem)

theorem polynomialCharacteristic_norm_lt_one (p : ℕ[X]) {activity : ℝ}
    (ha : 0 < activity) (hp : 0 < p.eval₂ (Nat.castRingHom ℝ) activity)
    (t : ℝ) {j : ℕ} (hj : 0 < p.coeff j) (hj1 : 0 < p.coeff (j + 1))
    (ht : Complex.exp ((t : ℂ) * Complex.I) ≠ 1) :
    ‖polynomialCharacteristic p activity t‖ < 1 := by
  let u := Complex.exp ((t : ℂ) * Complex.I)
  have hu : ‖u‖ = 1 := unit_exponential_norm t
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hi : j ∈ p.support := mem_support_iff.mpr (ne_of_gt hj)
  have hi1 : j + 1 ∈ p.support := mem_support_iff.mpr (ne_of_gt hj1)
  have hne : u ^ j ≠ u ^ (j + 1) := by
    intro h
    rw [pow_succ] at h
    have he : u ^ j * 1 = u ^ j * u := by simpa using h
    exact ht ((mul_left_cancel₀ (pow_ne_zero _ hu0) he).symm)
  have h := weighted_unit_sum_norm_lt p.support (fun k => (p.coeff k : ℝ) * activity ^ k)
    (fun k => u ^ k) (fun k hk => by positivity)
    (fun k hk => by rw [norm_pow, hu, one_pow]) hi hi1 (by omega)
    (mul_pos (by exact_mod_cast hj) (pow_pos ha _))
    (mul_pos (by exact_mod_cast hj1) (pow_pos ha _)) hne
  unfold polynomialCharacteristic
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  apply (div_lt_one hp).mpr
  rw [eval₂_eq_sum, sum_def, eval₂_eq_sum, sum_def]
  convert h using 1
  congr 1
  apply sum_congr rfl
  intro k hk
  change ((p.coeff k : ℕ) : ℂ) * ((activity : ℂ) * u) ^ k = _
  simp only [mul_pow, Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_natCast]
  ring

theorem unit_exponential_ne_one {t : ℝ} (ht0 : 0 < |t|) (ht : |t| ≤ Real.pi) :
    Complex.exp ((t : ℂ) * Complex.I) ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have he := congrArg Complex.im hn
  simp at he
  have hpi := Real.pi_pos
  have hbounds := abs_le.mp ht
  have hnlo : (-1 : ℝ) < n := by nlinarith
  have hnhi : (n : ℝ) < 1 := by nlinarith
  have hnloZ : (-1 : ℤ) < n := by exact_mod_cast hnlo
  have hnhiZ : n < (1 : ℤ) := by exact_mod_cast hnhi
  have hn0 : n = 0 := by omega
  subst n
  simp at he
  simp [he] at ht0

end SphericalTreeFailures
