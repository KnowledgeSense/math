import MainTheorems.EulerianPencil.PartialFractions

namespace ResearchMain.EulerianPencil

open Polynomial

theorem complex_nodal_erase_eval {g : ℝ[X]} (hs : g.Splits) (hm : g.Monic)
    (hr : g.Separable) {r : ℝ} (hr' : r ∈ rootNodes g) {z : ℂ} (hz : z.im ≠ 0) :
    (complexify (Lagrange.nodal ((rootNodes g).erase r) id)).eval z =
      (complexify g).eval z / (z - r) := by
  apply (eq_div_iff (real_pole_ne hz r)).mpr
  have he := congrArg (fun p : ℝ[X] => (complexify p).eval z)
    (Lagrange.nodal_eq_mul_nodal_erase (v := (id : ℝ → ℝ)) hr')
  rw [nodal_rootNodes hs hm hr] at he
  simpa [complexify, mul_comm] using he.symm

theorem complex_partial_fraction {m : ℕ} {f g : ℝ[X]} (hf : f.Monic) (hg : g.Monic)
    (df : f.natDegree = m + 1) (dg : g.natDegree = m) (hs : g.Splits) (hr : g.Separable)
    {z : ℂ} (hz : z.im ≠ 0) :
    (complexify f).eval z / (complexify g).eval z =
      z + ((f /ₘ g).coeff 0 : ℂ) +
        ∑ r ∈ rootNodes g, (f.eval r / (derivative g).eval r : ℝ) / (z - r) := by
  classical
  have hv := complex_eval_ne_zero hs hg.ne_zero hz
  have he := congrArg (fun p : ℝ[X] => (complexify p).eval z)
    (partial_fraction_polynomial hf hg df dg hs hr)
  simp only [complexify, Polynomial.map_add, Polynomial.map_mul, map_C, map_X,
    Polynomial.map_sum, eval_add, eval_mul, eval_C, eval_X, eval_finsetSum] at he
  change (complexify f).eval z = (z + ((f /ₘ g).coeff 0 : ℂ)) * (complexify g).eval z +
    ∑ r ∈ rootNodes g, (f.eval r / (derivative g).eval r : ℝ) *
      (complexify (Lagrange.nodal ((rootNodes g).erase r) id)).eval z at he
  rw [he, add_div, mul_div_cancel_right₀ _ hv, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro r hr'
  rw [complex_nodal_erase_eval hs hg hr hr' hz]
  field_simp

theorem real_residue_fraction_im (a r : ℝ) (z : ℂ) :
    ((a : ℂ) / (z - r)).im = z.im * (-a / Complex.normSq (z - r)) := by
  rw [div_eq_mul_inv]
  simp [Complex.mul_im, Complex.inv_im]
  ring

theorem complex_ratio_im {m : ℕ} {f g : ℝ[X]} (hf : f.Monic) (hg : g.Monic)
    (df : f.natDegree = m + 1) (dg : g.natDegree = m) (hs : g.Splits) (hr : g.Separable)
    {z : ℂ} (hz : z.im ≠ 0) :
    ((complexify f).eval z / (complexify g).eval z).im = z.im *
      (1 + ∑ r ∈ rootNodes g, -(f.eval r / (derivative g).eval r) / Complex.normSq (z - r)) := by
  rw [complex_partial_fraction hf hg df dg hs hr hz]
  simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.im_sum,
    real_residue_fraction_im]
  rw [← Finset.mul_sum]
  ring

theorem complex_ratio_im_ne_zero {m : ℕ} {f g : ℝ[X]} (hf : f.Monic) (hg : g.Monic)
    (df : f.natDegree = m + 1) (dg : g.natDegree = m) (hs : g.Splits) (hr : g.Separable)
    (hsgn : ∀ r : ℝ, g.eval r = 0 → f.eval r * (derivative g).eval r < 0)
    {z : ℂ} (hz : z.im ≠ 0) :
    ((complexify f).eval z / (complexify g).eval z).im ≠ 0 := by
  rw [complex_ratio_im hf hg df dg hs hr hz]
  apply mul_ne_zero hz
  have hsum : 0 ≤ ∑ r ∈ rootNodes g,
      -(f.eval r / (derivative g).eval r) / Complex.normSq (z - r) := by
    apply Finset.sum_nonneg
    intro r hr'
    apply div_nonneg
    · exact (neg_pos.mpr (residue_negative (hsgn r ((rootNodes_mem hg.ne_zero).mp hr')))).le
    · exact Complex.normSq_nonneg _
  linarith

theorem residue_pencil_splits {m : ℕ} {f g : ℝ[X]} (hf : f.Monic) (hg : g.Monic)
    (df : f.natDegree = m + 1) (dg : g.natDegree = m) (hs : g.Splits) (hr : g.Separable)
    (hsgn : ∀ r : ℝ, g.eval r = 0 → f.eval r * (derivative g).eval r < 0) (k : ℝ) :
    (f + C k * g).Splits := by
  apply splits_of_nonreal_eval_ne_zero
  intro z hz he
  have hv := complex_eval_ne_zero hs hg.ne_zero hz
  have hi := complex_ratio_im_ne_zero hf hg df dg hs hr hsgn hz
  apply hi
  have hratio : (complexify f).eval z / (complexify g).eval z + k = 0 := by
    simp only [complexify, Polynomial.map_add, Polynomial.map_mul, map_C, eval_add,
      eval_mul, eval_C] at he
    change (complexify f).eval z + (k : ℂ) * (complexify g).eval z = 0 at he
    field_simp
    linear_combination he
  have hdim := congrArg Complex.im hratio
  simpa using hdim

theorem oddH_pencil_splits (m : ℕ) (k : ℝ) : (oddH (m + 1) + C k * oddH m).Splits :=
  residue_pencil_splits (oddH_monic (m + 1)) (oddH_monic m) (oddH_natDegree (m + 1))
    (oddH_natDegree m) (oddH_splits m) (oddH_separable m) (fun _ => oddH_residue_sign m) k

theorem evenH_pencil_splits (m : ℕ) (k : ℝ) : (evenH (m + 1) + C k * evenH m).Splits :=
  residue_pencil_splits (evenH_monic (m + 1)) (evenH_monic m) (evenH_natDegree (m + 1))
    (evenH_natDegree m) (evenH_splits m) (evenH_separable m) (fun _ => evenH_residue_sign m) k

end ResearchMain.EulerianPencil
