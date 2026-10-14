import MainTheorems.DominationRoots.RootMoments
import Mathlib.Algebra.Polynomial.RingDivision

namespace ResearchMain.DominationRoots

open Polynomial

noncomputable def reflection (f : ℤ[X]) : ℤ[X] :=
  C ((-1) ^ f.natDegree) * f.comp (-X)

theorem reflection_monic {f : ℤ[X]} (hf : f.Monic) : (reflection f).Monic := by
  simpa [reflection] using hf.neg_one_pow_natDegree_mul_comp_neg_X

theorem reflection_natDegree (f : ℤ[X]) : (reflection f).natDegree = f.natDegree := by
  rw [reflection, natDegree_C_mul (pow_ne_zero _ (by norm_num)), natDegree_comp]
  simp

theorem realPolynomial_reflection (f : ℤ[X]) :
    realPolynomial (reflection f) = C ((-1 : ℝ) ^ f.natDegree) *
      (realPolynomial f).comp (-X) := by
  simp [realPolynomial, reflection, Polynomial.map_comp]

theorem reflection_roots (f : ℤ[X]) :
    realRoots (reflection f) = (realRoots f).map Neg.neg := by
  unfold realRoots
  rw [realPolynomial_reflection, roots_C_mul _ (pow_ne_zero _ (by norm_num)), roots_comp_neg_X]

theorem reflection_trace (f : ℤ[X]) :
    rootTrace (reflection f) = ((realRoots f).map (fun x => x ^ 2)).sum + (realRoots f).sum := by
  rw [rootTrace, reflection_roots, Multiset.map_map]
  have he : (fun x : ℝ => (-x) ^ 2 - -x) = (fun x => x ^ 2 + x) := by
    funext x
    ring
  dsimp only [Function.comp_def]
  rw [he, Multiset.sum_map_add, Multiset.map_id']

theorem realPolynomial_coeff (f : ℤ[X]) (k : ℕ) :
    (realPolynomial f).coeff k = (f.coeff k : ℝ) := by
  exact coeff_map _ _

theorem nonnegative_roots_negative {f : ℤ[X]} (hm : f.Monic)
    (hc : ∀ k, 0 ≤ f.coeff k) (h0 : 0 < f.coeff 0) :
    ∀ x ∈ realRoots f, x < 0 := by
  intro x hx
  by_contra hneg
  have hval : (realPolynomial f).eval x = 0 :=
    (mem_roots (hm.map (Int.castRingHom ℝ)).ne_zero).mp hx
  have hcoeff : ∀ k, 0 ≤ (realPolynomial f).coeff k := by
    intro k
    rw [realPolynomial_coeff]
    exact_mod_cast hc k
  have hconstant : 0 < (realPolynomial f).coeff 0 := by
    rw [realPolynomial_coeff]
    exact_mod_cast h0
  have hpos := nonnegativePolynomial_eval_positive hcoeff hconstant (le_of_not_gt hneg)
  linarith

theorem reflection_totallyPositive {f : ℤ[X]} (hm : f.Monic)
    (hs : (realPolynomial f).Splits) (hc : ∀ k, 0 ≤ f.coeff k) (h0 : 0 < f.coeff 0)
    (h1 : f.eval (-1) ≠ 0) : TotallyPositive (reflection f) := by
  constructor
  · rw [realPolynomial_reflection]
    exact (Splits.C _).mul hs.comp_neg_X
  · intro x hx
    rw [reflection_roots] at hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    refine ⟨neg_pos.mpr (nonnegative_roots_negative hm hc h0 y hy), ?_⟩
    intro he
    have hy1 : y = -1 := by linarith
    have hev := (mem_roots (hm.map (Int.castRingHom ℝ)).ne_zero).mp hy
    rw [hy1] at hev
    have hev' : f.eval₂ (Int.castRingHom ℝ) (-1) = 0 := by
      simpa only [Polynomial.IsRoot, eval_map] using hev
    have hv := eval₂_at_apply (Int.castRingHom ℝ) (-1 : ℤ) (p := f)
    have hφ : (Int.castRingHom ℝ) (-1) = -1 := by rw [map_neg, map_one]
    rw [hφ] at hv
    have hcval : ((f.eval (-1) : ℤ) : ℝ) = 0 := hv.symm.trans hev'
    exact h1 (by exact_mod_cast hcval)

end ResearchMain.DominationRoots
