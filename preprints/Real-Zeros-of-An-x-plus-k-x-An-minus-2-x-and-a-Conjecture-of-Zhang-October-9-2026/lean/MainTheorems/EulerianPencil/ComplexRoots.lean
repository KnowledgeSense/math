import MainTheorems.EulerianPencil.Degree
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Basic.Complex.BigOperators

namespace ResearchMain.EulerianPencil

open Polynomial

noncomputable def complexify (f : ℝ[X]) : ℂ[X] := f.map Complex.ofRealHom

theorem complexify_ne_zero {f : ℝ[X]} (hf : f ≠ 0) : complexify f ≠ 0 := by
  exact map_ne_zero hf

theorem splits_iff_complex_roots_real {f : ℝ[X]} (hf : f ≠ 0) :
    f.Splits ↔ ∀ z : ℂ, (complexify f).eval z = 0 → z.im = 0 := by
  constructor
  · intro hs z hz
    obtain ⟨r, hr⟩ := hs.mem_range_of_isRoot hf (show (f.map Complex.ofRealHom).IsRoot z from hz)
    rw [← hr]
    exact Complex.ofReal_im _
  · intro hz
    apply (IsAlgClosed.splits (complexify f)).of_splits_map Complex.ofRealHom
    intro z hm
    have he := (mem_roots (complexify_ne_zero hf)).mp hm
    refine ⟨z.re, ?_⟩
    apply Complex.ext
    · simp
    · simpa using (hz z he).symm

theorem complex_eval_ne_zero {f : ℝ[X]} (hs : f.Splits) (hf : f ≠ 0)
    {z : ℂ} (hz : z.im ≠ 0) : (complexify f).eval z ≠ 0 := by
  exact fun he => hz ((splits_iff_complex_roots_real hf).mp hs z he)

theorem real_pole_ne {z : ℂ} (hz : z.im ≠ 0) (r : ℝ) : z - r ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, sub_zero] at hi
  exact hz hi

theorem inverse_sum_im (r : Multiset ℝ) (z : ℂ) :
    ((r.map (fun (a : ℝ) => 1 / (z - a))).sum).im =
      -z.im * (r.map (fun (a : ℝ) => 1 / Complex.normSq (z - a))).sum := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons a r ih =>
    simp only [one_div] at ih
    simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im, one_div,
      Complex.inv_im, Complex.sub_im, Complex.ofReal_im, sub_zero]
    rw [ih]
    ring

theorem norm_inverse_sum_nonnegative (r : Multiset ℝ) (z : ℂ) :
    0 ≤ (r.map (fun (a : ℝ) => 1 / Complex.normSq (z - a))).sum := by
  induction r using Multiset.induction_on with
  | empty => simp
  | cons a r ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    exact add_nonneg (one_div_nonneg.mpr (Complex.normSq_nonneg _)) ih

theorem logarithmic_derivative_im {f : ℝ[X]} (hs : f.Splits) (hf : f ≠ 0)
    {z : ℂ} (hz : z.im ≠ 0) :
    ((complexify f).derivative.eval z / (complexify f).eval z).im =
      -z.im * (f.roots.map (fun (a : ℝ) => 1 / Complex.normSq (z - a))).sum := by
  have hmap : (complexify f).Splits := hs.map Complex.ofRealHom
  rw [hmap.eval_derivative_div_eval_of_ne_zero (complex_eval_ne_zero hs hf hz)]
  rw [show (complexify f).roots = f.roots.map Complex.ofRealHom from hs.roots_map _]
  simp only [Multiset.map_map, Function.comp_def]
  exact inverse_sum_im _ _

end ResearchMain.EulerianPencil
