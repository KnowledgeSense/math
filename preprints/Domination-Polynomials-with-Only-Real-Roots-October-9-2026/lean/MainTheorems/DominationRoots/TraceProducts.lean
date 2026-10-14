import MainTheorems.DominationRoots.ResultantTrace

namespace ResearchMain.DominationRoots

open Polynomial

theorem realPolynomial_mul (f g : ℤ[X]) :
    realPolynomial (f * g) = realPolynomial f * realPolynomial g := by
  exact Polynomial.map_mul _

theorem realRoots_mul {f g : ℤ[X]} (hf : f.Monic) (hg : g.Monic) :
    realRoots (f * g) = realRoots f + realRoots g := by
  unfold realRoots
  rw [realPolynomial_mul]
  exact roots_mul (mul_ne_zero
    (hf.map (Int.castRingHom ℝ)).ne_zero (hg.map (Int.castRingHom ℝ)).ne_zero)

theorem rootTrace_mul {f g : ℤ[X]} (hf : f.Monic) (hg : g.Monic) :
    rootTrace (f * g) = rootTrace f + rootTrace g := by
  simp only [rootTrace, realRoots_mul hf hg, Multiset.map_add, Multiset.sum_add]

theorem totallyPositive_of_dvd {f g : ℤ[X]} (hf : f.Monic) (hg : g.Monic)
    (ht : TotallyPositive f) (hdvd : g ∣ f) : TotallyPositive g := by
  obtain ⟨q, hq⟩ := hdvd
  have hm : q.Monic := hg.of_mul_monic_left (hq ▸ hf)
  have hroot : ∀ x ∈ realRoots g, x ∈ realRoots f := by
    intro x hx
    rw [hq, realRoots_mul hg hm]
    exact Multiset.mem_add.mpr (Or.inl hx)
  constructor
  · apply ht.1.of_dvd (hf.map (Int.castRingHom ℝ)).ne_zero
    exact ⟨realPolynomial q, by rw [hq, realPolynomial_mul]⟩
  · exact fun x hx => ht.2 x (hroot x hx)

noncomputable def linearFactor : ℤ[X] := X - C 2

theorem linearFactor_monic : linearFactor.Monic := monic_X_sub_C 2

theorem linearFactor_natDegree : linearFactor.natDegree = 1 := natDegree_X_sub_C 2

theorem linearFactor_roots : realRoots linearFactor = {2} := by
  unfold realRoots realPolynomial linearFactor
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have h2 : (Int.castRingHom ℝ) 2 = 2 := map_ofNat _ 2
  rw [h2, roots_X_sub_C]

theorem linearFactor_trace : rootTrace linearFactor = 2 := by
  norm_num [rootTrace, linearFactor_roots]

theorem quadraticPolynomial_real_factor :
    realPolynomial quadraticPolynomial = (X - C lowerRoot) * (X - C upperRoot) := by
  apply Polynomial.funext
  intro x
  rw [show (realPolynomial quadraticPolynomial).eval x = quadratic 3 1 x by
    norm_num [realPolynomial, quadraticPolynomial, quadratic, map_ofNat]]
  simpa only [eval_mul, eval_sub, eval_X, eval_C] using quadratic_factor x

theorem quadraticPolynomial_roots : realRoots quadraticPolynomial = {lowerRoot, upperRoot} := by
  unfold realRoots
  rw [quadraticPolynomial_real_factor, roots_mul (mul_ne_zero
    (monic_X_sub_C lowerRoot).ne_zero (monic_X_sub_C upperRoot).ne_zero)]
  simp

theorem quadraticPolynomial_trace : rootTrace quadraticPolynomial = 4 := by
  simp only [rootTrace, quadraticPolynomial_roots, Multiset.insert_eq_cons, Multiset.map_cons,
    Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton]
  unfold lowerRoot upperRoot
  have hsq := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  nlinarith

theorem linearFactor_dvd_of_root {f : ℤ[X]} (hf : (aeval (2 : ℝ)) f = 0) :
    linearFactor ∣ f := by
  apply dvd_iff_isRoot.mpr
  have hval := eval₂_at_apply (Int.castRingHom ℝ) (2 : ℤ) (p := f)
  have h2 : (Int.castRingHom ℝ) 2 = 2 := map_ofNat _ 2
  rw [h2] at hval
  have he : (Int.castRingHom ℝ) (f.eval 2) = 0 := hval.symm.trans hf
  change ((f.eval 2 : ℤ) : ℝ) = 0 at he
  change f.eval 2 = 0
  exact_mod_cast he

end ResearchMain.DominationRoots
