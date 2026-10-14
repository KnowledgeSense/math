import MainTheorems.EulerianPencil.RealFractions
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Polynomial.Order

namespace ResearchMain.EulerianPencil

open Polynomial

structure InterlacingPair (f g : ℝ[X]) : Prop where
  monic_left : f.Monic
  monic_right : g.Monic
  degree_step : f.natDegree = g.natDegree + 1
  splits_right : g.Splits
  separable_right : g.Separable
  residue_sign : ∀ r : ℝ, g.eval r = 0 → f.eval r * (derivative g).eval r < 0

namespace InterlacingPair

variable {f g : ℝ[X]} (h : InterlacingPair f g)
include h

theorem splits (k : ℝ) : (f + C k * g).Splits :=
  residue_pencil_splits h.monic_left h.monic_right h.degree_step rfl
    h.splits_right h.separable_right h.residue_sign k

theorem simpleRoots (k : ℝ) : SimpleRoots (f + C k * g) :=
  residue_pencil_simpleRoots h.monic_left h.monic_right h.degree_step rfl
    h.splits_right h.separable_right h.residue_sign k

theorem wronskian_positive (x : ℝ) : 0 < (pencilWronskian f g).eval x :=
  residue_wronskian_positive h.monic_left h.monic_right h.degree_step rfl
    h.splits_right h.separable_right h.residue_sign x

theorem monic (k : ℝ) : (f + C k * g).Monic := by
  apply h.monic_left.add_of_left
  apply degree_lt_degree
  have hd := natDegree_C_mul_le k g
  rw [h.degree_step]
  omega

theorem degree (k : ℝ) : (f + C k * g).natDegree = g.natDegree + 1 := by
  rw [natDegree_add_eq_left_of_natDegree_lt, h.degree_step]
  have hd := natDegree_C_mul_le k g
  rw [h.degree_step]
  omega

theorem no_common_root (k : ℝ) {x : ℝ} (hx : g.eval x = 0) : (f + C k * g).eval x ≠ 0 := by
  simp only [eval_add, eval_mul, eval_C, hx, mul_zero, add_zero]
  exact fun he => by simpa [he] using h.residue_sign x hx

theorem denominator_positive {b x : ℝ} (hb : ∀ r : ℝ, g.eval r = 0 → r < b)
    (hx : b ≤ x) : 0 < g.eval x :=
  zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    (fun r hr => (hb r hr).trans_le hx) (by rw [h.monic_right.leadingCoeff]; norm_num)

theorem ratio_strictMonoOn {b : ℝ} (hb : ∀ r : ℝ, g.eval r = 0 → r < b) :
    StrictMonoOn (fun x : ℝ => f.eval x / g.eval x) (Set.Ici b) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici b)
  · apply ContinuousOn.div f.continuous.continuousOn g.continuous.continuousOn
    intro x hx
    exact (h.denominator_positive hb hx).ne'
  · intro x hx
    have hp := h.denominator_positive hb (show b ≤ x from le_of_lt (by simpa using hx))
    exact ((f.hasDerivAt x).fun_div (g.hasDerivAt x) hp.ne').hasDerivWithinAt
  · intro x hx
    exact div_pos (by simpa [pencilWronskian] using h.wronskian_positive x) (sq_pos_of_ne_zero
      (h.denominator_positive hb (show b ≤ x from le_of_lt (by simpa using hx))).ne')

theorem root_bound_iff {b : ℝ} (hb : ∀ r : ℝ, g.eval r = 0 → r < b) (k : ℝ) :
    (∀ x : ℝ, (f + C k * g).eval x = 0 → x ≤ b) ↔ 0 ≤ f.eval b / g.eval b + k := by
  constructor
  · intro hroot
    have hq : 0 ≤ (f + C k * g).eval b :=
      zero_le_eval_of_roots_le_of_leadingCoeff_nonneg hroot
        (by rw [(h.monic k).leadingCoeff]; norm_num)
    have hg := h.denominator_positive hb (le_refl b)
    have he : (f + C k * g).eval b / g.eval b = f.eval b / g.eval b + k := by
      simp only [eval_add, eval_mul, eval_C, add_div, mul_div_cancel_right₀ _ hg.ne']
    rw [← he]
    exact div_nonneg hq hg.le
  · intro hbval x hx
    by_contra hle
    have hbx : b < x := not_le.mp hle
    have hg := h.denominator_positive hb hbx.le
    have hratio : f.eval x / g.eval x + k = 0 := by
      simp only [eval_add, eval_mul, eval_C] at hx
      field_simp
      linear_combination hx
    have hm := h.ratio_strictMonoOn hb (le_refl b) hbx.le hbx
    linarith

theorem strict_root_bound_iff {b : ℝ} (hb : ∀ r : ℝ, g.eval r = 0 → r < b) (k : ℝ) :
    (∀ x : ℝ, (f + C k * g).eval x = 0 → x < b) ↔ 0 < f.eval b / g.eval b + k := by
  constructor
  · intro hroot
    have hq : 0 < (f + C k * g).eval b :=
      zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg hroot
        (by rw [(h.monic k).leadingCoeff]; norm_num)
    have hg := h.denominator_positive hb (le_refl b)
    have he : (f + C k * g).eval b / g.eval b = f.eval b / g.eval b + k := by
      simp only [eval_add, eval_mul, eval_C, add_div, mul_div_cancel_right₀ _ hg.ne']
    rw [← he]
    exact div_pos hq hg
  · intro hbval x hx
    have hle := (h.root_bound_iff hb k).mpr hbval.le x hx
    apply lt_of_le_of_ne hle
    intro he
    subst x
    have hg := h.denominator_positive hb (le_refl b)
    have hz : f.eval b / g.eval b + k = 0 := by
      simp only [eval_add, eval_mul, eval_C] at hx
      field_simp
      linear_combination hx
    linarith

end InterlacingPair

theorem oddH_interlacingPair (m : ℕ) : InterlacingPair (oddH (m + 1)) (oddH m) where
  monic_left := oddH_monic (m + 1)
  monic_right := oddH_monic m
  degree_step := by rw [oddH_natDegree, oddH_natDegree]
  splits_right := oddH_splits m
  separable_right := oddH_separable m
  residue_sign := fun _ => oddH_residue_sign m

theorem evenH_interlacingPair (m : ℕ) : InterlacingPair (evenH (m + 1)) (evenH m) where
  monic_left := evenH_monic (m + 1)
  monic_right := evenH_monic m
  degree_step := by rw [evenH_natDegree, evenH_natDegree]
  splits_right := evenH_splits m
  separable_right := evenH_separable m
  residue_sign := fun _ => evenH_residue_sign m

end ResearchMain.EulerianPencil
