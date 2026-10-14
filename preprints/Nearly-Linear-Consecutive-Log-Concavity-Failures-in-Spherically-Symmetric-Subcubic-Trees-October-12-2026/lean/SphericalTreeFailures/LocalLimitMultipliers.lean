import SphericalTreeFailures.DifferenceMultipliers
import SphericalTreeFailures.FourierKernelBounds

namespace SphericalTreeFailures
open Filter
open scoped Topology

inductive DifferenceKind where
  | value | forward | backward | second
  deriving DecidableEq

def DifferenceKind.order : DifferenceKind → ℕ
  | .value => 0
  | .forward | .backward => 1
  | .second => 2

noncomputable def differenceMultiplier (d : DifferenceKind) (H t : ℝ) : ℂ :=
  match d with
  | .value => 1
  | .forward => forwardMultiplier H t
  | .backward => backwardMultiplier H t
  | .second => secondMultiplier H t

noncomputable def limitMultiplier (d : DifferenceKind) (t : ℝ) : ℂ :=
  (-(t : ℂ) * Complex.I) ^ d.order

 theorem limitMultiplier_second (t : ℝ) : limitMultiplier .second t = -(t : ℂ) ^ 2 := by
  unfold limitMultiplier DifferenceKind.order
  rw [mul_pow, neg_sq, Complex.I_sq]
  ring

theorem differenceMultiplier_tendsto {γ : ℝ} (hγ : 1 < γ) (d : DifferenceKind) (t : ℝ) :
    Tendsto (fun m => differenceMultiplier d (γ ^ m) t) atTop (𝓝 (limitMultiplier d t)) := by
  cases d
  · simp [differenceMultiplier, limitMultiplier, DifferenceKind.order]
  · simpa [differenceMultiplier, limitMultiplier, DifferenceKind.order] using forwardMultiplier_tendsto hγ t
  · simpa [differenceMultiplier, limitMultiplier, DifferenceKind.order] using backwardMultiplier_tendsto hγ t
  · rw [limitMultiplier_second]
    exact secondMultiplier_tendsto hγ t

theorem differenceMultiplier_norm_bound (d : DifferenceKind) {H : ℝ} (hH : 0 < H) (t : ℝ) :
    ‖differenceMultiplier d H t‖ ≤ 1 + t ^ 2 := by
  have ht : |t| ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (|t| - 1), sq_abs t]
  cases d
  · simp [differenceMultiplier, sq_nonneg]
  · exact (forwardMultiplier_norm_le hH t).trans ht
  · exact (backwardMultiplier_norm_le hH t).trans ht
  · exact (secondMultiplier_norm_le hH t).trans (by linarith)

theorem limitMultiplier_norm_bound (d : DifferenceKind) (t : ℝ) :
    ‖limitMultiplier d t‖ ≤ 1 + t ^ 2 := by
  have ht : |t| ≤ 1 + t ^ 2 := by nlinarith [sq_nonneg (|t| - 1), sq_abs t]
  cases d <;> simp only [limitMultiplier, DifferenceKind.order, pow_zero, pow_one, norm_one,
    norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one, norm_pow, sq_abs]
  · nlinarith [sq_nonneg t]
  · exact ht
  · exact ht
  · linarith

theorem differenceMultiplier_continuous (d : DifferenceKind) (H : ℝ) :
    Continuous (differenceMultiplier d H) := by
  cases d <;> unfold differenceMultiplier
  · exact continuous_const
  · unfold forwardMultiplier sizeExponential; fun_prop
  · unfold backwardMultiplier sizeExponential; fun_prop
  · unfold secondMultiplier forwardMultiplier backwardMultiplier sizeExponential; fun_prop

theorem multiplier_error_tendsto {a b e : ℕ → ℂ} {l : ℂ}
    (he : Tendsto e atTop (𝓝 l))
    (hab : Tendsto (fun m => ‖a m - b m‖) atTop (𝓝 0))
    (hb : ∀ m, ‖b m‖ ≤ 1) :
    Tendsto (fun m => e m * a m - l * b m) atTop (𝓝 0) := by
  have hbound (m : ℕ) : ‖e m * a m - l * b m‖ ≤
      ‖e m‖ * ‖a m - b m‖ + ‖e m - l‖ := by
    have hx : e m * a m - l * b m = e m * (a m - b m) + (e m - l) * b m := by ring
    rw [hx]
    apply (norm_add_le _ _).trans
    rw [norm_mul, norm_mul]
    exact add_le_add le_rfl (mul_le_of_le_one_right (norm_nonneg (e m - l)) (hb m))
  have ht := (he.norm.mul hab).add ((he.sub (tendsto_const_nhds (x := l))).norm)
  simp only [sub_self, norm_zero, mul_zero, zero_add] at ht
  exact tendsto_zero_iff_norm_tendsto_zero.mpr
    (squeeze_zero (fun _ => norm_nonneg _) hbound ht)

end SphericalTreeFailures
