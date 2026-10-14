import MainTheorems.Hypercomb.Sector
import MainTheorems.Hypercomb.KernelSequence
import MainTheorems.Hypercomb.PathMoments

namespace ResearchMain.Hypercomb

theorem linear_root_leftCone {b : ℝ} (hb : 0 < b) (z : ℂ)
    (hz : 1 + (b : ℂ) * z = 0) : LeftCone z := by
  have hr := congrArg Complex.re hz
  have hi := congrArg Complex.im hz
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.zero_re, Complex.zero_im, zero_mul, zero_add, add_zero, sub_zero] at hr hi
  have him : z.im = 0 := (mul_eq_zero.mp hi).resolve_left (ne_of_gt hb)
  have hre : z.re < 0 := by nlinarith only [hr, hb]
  exact ⟨hre, by rw [him]; nlinarith [sq_pos_of_neg hre]⟩

theorem combValue_root_arg (a : ℝ) (ha : 2 ≤ a) (n : ℕ) (z : ℂ)
    (hz : combValue (a : ℂ) z n = 0) : 2 * Real.pi / 3 < |z.arg| := by
  have hzne : z ≠ 0 := by intro he; subst z; rw [combValue_zero] at hz; norm_num at hz
  let f : ℂ := 1 + (a : ℂ) * z
  by_cases hf : f = 0
  · exact leftCone_arg (linear_root_leftCone (by linarith : 0 < a) z hf)
  · cases n with
    | zero =>
      have hlin : 1 + ((a + 1 : ℝ) : ℂ) * z = 0 := by
        dsimp [combValue, transfer] at hz
        push_cast
        linear_combination hz
      exact leftCone_arg (linear_root_leftCone (by linarith : 0 < a + 1) z hlin)
    | succ n =>
      have hroot := (mul_eq_zero.mp ((combValue_succ (a : ℂ) z n).symm.trans hz)).resolve_left hf
      let A : ℂ := f * (1 + ((a : ℂ) - 1) * z)
      let B : ℂ := f * z
      change boundaryContinuant A B z (n + 1) + z * boundaryContinuant A B z n = 0 at hroot
      cases n with
      | zero =>
        simp only [boundaryContinuant, mul_one] at hroot
        apply sector_quadratic_arg ha (by norm_num : (0 : ℝ) ≤ 2) z
        push_cast
        change A + (2 : ℂ) * z = 0
        linear_combination hroot
      | succ m =>
        have hB : B ≠ 0 := mul_ne_zero hf hzne
        obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (-B) (by decide : 0 < 2)
        have hcne : c ≠ 0 := by intro he; subst c; simp only [zero_pow (by decide : 2 ≠ 0)] at hc; exact hB (by linear_combination hc)
        obtain ⟨hcq, hBq, hBq'⟩ := kernel_coefficients B c hcne hc
        let v := kernelSequence A B z (-c⁻¹)
        have hfirst := kernelSequence_first (A := A) (B := B) (z := z) hcq
        have hmiddle : ∀ i < m, c * v i + A * v (i + 1) + c * v (i + 2) = 0 :=
          fun i _ => kernelSequence_middle hcq hBq i
        have hlast := kernelSequence_last (A := A) (z := z) hBq' m hroot
        have hv : v 0 ≠ 0 := by simp [v, kernelSequence_zero]
        obtain ⟨σ, t, hσ0, hσ1, ht, heq⟩ := path_normalized_equation A z c v m hv hfirst hmiddle hlast
        have hquartic : (A + (σ : ℂ) * z) ^ 2 + (t : ℂ) ^ 2 * B = 0 := by
          linear_combination (A + (σ : ℂ) * z - c * (t : ℂ)) * heq + (t : ℂ) ^ 2 * hc
        apply sector_quartic_arg ha hσ0 hσ1 (abs_nonneg t) ht z
        dsimp only [sectorQuartic]
        push_cast
        change (A + (σ : ℂ) * z) ^ 2 + ((|t| : ℝ) : ℂ) ^ 2 * z * f = 0
        have habs : ((|t| : ℝ) : ℂ) ^ 2 = (t : ℂ) ^ 2 := by exact_mod_cast sq_abs t
        rw [habs]
        dsimp only [B] at hquartic
        linear_combination hquartic

end ResearchMain.Hypercomb
