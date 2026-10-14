import MainTheorems.EulerianPencil.Wronskians
import Mathlib.Algebra.Polynomial.Reverse

namespace ResearchMain.EulerianPencil

open Polynomial

noncomputable def reduction (m : ℕ) (f : ℝ[X]) : ℝ[X] := (f.reflect m).comp (X - C 2)

@[simp] theorem reduction_zero (m : ℕ) : reduction m 0 = 0 := by simp [reduction]

@[simp] theorem reduction_add (m : ℕ) (f g : ℝ[X]) :
    reduction m (f + g) = reduction m f + reduction m g := by simp [reduction, add_comp]

@[simp] theorem reduction_C_mul (m : ℕ) (a : ℝ) (f : ℝ[X]) :
    reduction m (C a * f) = C a * reduction m f := by simp [reduction, mul_comp]

theorem reduction_X_pow {j m : ℕ} (hj : j ≤ m) :
    reduction m (X ^ j) = (X - C 2) ^ (m - j) := by
  simp [reduction, reflect_monomial, revAt_le hj]

theorem reduction_eval {m : ℕ} {f : ℝ[X]} (hf : f.natDegree ≤ m) {x : ℝ} (hx : x ≠ 2) :
    (reduction m f).eval x = (x - 2) ^ m * f.eval (1 / (x - 2)) := by
  have hx0 : x - 2 ≠ 0 := sub_ne_zero.mpr hx
  apply Polynomial.induction_with_natDegree_le
    (fun f => (reduction m f).eval x = (x - 2) ^ m * f.eval (1 / (x - 2))) m
  · simp
  · intro j a _ hj
    rw [reduction_C_mul, reduction_X_pow hj]
    simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, one_div_pow]
    rw [pow_sub₀ (x - 2) hx0 hj]
    ring
  · intro f g _ _ ihf ihg
    rw [reduction_add, eval_add, eval_add, ihf, ihg, mul_add]
  · exact hf

theorem reduction_at_two (m : ℕ) (f : ℝ[X]) : (reduction m f).eval 2 = f.coeff m := by
  simp [reduction, eval_comp, ← coeff_zero_eq_eval_zero, coeff_reflect]

theorem reduction_degree_le {m : ℕ} {f : ℝ[X]} (hf : f.natDegree ≤ m) :
    (reduction m f).natDegree ≤ m := by
  rw [reduction, natDegree_comp, natDegree_X_sub_C, mul_one]
  exact natDegree_reflect_le.trans (max_le (le_refl m) hf)

theorem reduction_monic {m : ℕ} {f : ℝ[X]} (hf : f.natDegree ≤ m) (h0 : f.coeff 0 = 1) :
    (reduction m f).Monic ∧ (reduction m f).natDegree = m := by
  have hdeg : (f.reflect m).natDegree = m := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
      (natDegree_reflect_le.trans (max_le (le_refl m) hf))
    simpa only [coeff_reflect, revAt_le (le_refl m), Nat.sub_self, h0] using
      (one_ne_zero : (1 : ℝ) ≠ 0)
  have hm : (f.reflect m).Monic := by
    rw [Monic, leadingCoeff, hdeg, coeff_reflect, revAt_le (le_refl m), Nat.sub_self, h0]
  refine ⟨hm.comp (monic_X_sub_C 2) (by simp), ?_⟩
  simp [reduction, natDegree_comp, hdeg]

theorem reduction_mul {a b : ℕ} {f g : ℝ[X]} (hf : f.natDegree ≤ a) (hg : g.natDegree ≤ b) :
    reduction (a + b) (f * g) = reduction a f * reduction b g := by
  simp [reduction, reflect_mul f g hf hg, mul_comp]

noncomputable def oddH (m : ℕ) : ℝ[X] := reduction m (oddF m)

noncomputable def evenH (m : ℕ) : ℝ[X] := reduction m (evenF m)

theorem oddH_monic (m : ℕ) : (oddH m).Monic :=
  (reduction_monic (oddF_degree_le m) (oddF_constant m)).1

theorem evenH_monic (m : ℕ) : (evenH m).Monic :=
  (reduction_monic (evenF_degree_le m) (evenF_constant m)).1

theorem oddH_natDegree (m : ℕ) : (oddH m).natDegree = m :=
  (reduction_monic (oddF_degree_le m) (oddF_constant m)).2

theorem evenH_natDegree (m : ℕ) : (evenH m).natDegree = m :=
  (reduction_monic (evenF_degree_le m) (evenF_constant m)).2

end ResearchMain.EulerianPencil
