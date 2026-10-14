import MainTheorems.DominationRoots.StarPolynomials

namespace ResearchMain.DominationRoots

open Polynomial

theorem reducedStarFactor_reflected_sum {s : ℕ} (hs : 2 ≤ s)
    (ht : TotallyPositive (reflection (reducedStarFactor s))) :
    (realRoots (reflection (reducedStarFactor s))).sum = (s : ℝ) + 1 := by
  have hm : (realPolynomial (reducedStarFactor s)).Monic :=
    (reducedStarFactor_monic s hs).map (Int.castRingHom ℝ)
  have hsplit := (reflection_splits_iff (reducedStarFactor s)).mp ht.1
  have hd : (realPolynomial (reducedStarFactor s)).natDegree = s := by
    rw [realPolynomial, natDegree_map_eq_of_injective Int.cast_injective,
      reducedStarFactor_natDegree s hs]
  have hsum := split_root_sum hm hsplit (by rw [hd]; omega)
  rw [hd, realPolynomial_coeff, reducedStarFactor_next s (by omega)] at hsum
  push_cast at hsum
  rw [reflection_roots, Multiset.sum_map_neg, Multiset.map_id']
  change -(realPolynomial (reducedStarFactor s)).roots.sum = _
  rw [hsum]
  ring

theorem reducedStarFactor_classification {s : ℕ} (hs : 2 ≤ s)
    (ht : TotallyPositive (reflection (reducedStarFactor s)))
    (ha : AllowedProduct (reflection (reducedStarFactor s))) : s = 2 := by
  obtain ⟨a, b, he⟩ := ha
  have hd := congrArg natDegree he
  rw [reflection_natDegree, reducedStarFactor_natDegree s hs,
    (linearFactor_monic.pow a).natDegree_mul (quadraticPolynomial_monic.pow b),
    natDegree_pow, natDegree_pow, linearFactor_natDegree, quadraticPolynomial_natDegree] at hd
  have hconst : (reducedStarFactor s).eval 0 = 1 := by
    rw [← coeff_zero_eq_eval_zero, reducedStarFactor_constant s hs]
  have hc := congrArg (fun p : ℤ[X] => p.eval 0) he
  simp only [reflection, eval_mul, eval_C, eval_comp, eval_neg, eval_X, neg_zero,
    hconst, mul_one, reducedStarFactor_natDegree s hs, eval_pow] at hc
  have hlin : linearFactor.eval 0 = -2 := by norm_num [linearFactor]
  have hquad : quadraticPolynomial.eval 0 = 1 := by norm_num [quadraticPolynomial]
  rw [hlin, hquad, one_pow, mul_one] at hc
  have habs := congrArg abs hc
  norm_num [abs_pow] at habs
  have ha0 : a = 0 := by
    by_contra hne
    have h := (pow_eq_one_iff_of_ne_zero hne).mp habs.symm
    norm_num at h
  have hsum := allowedProduct_root_sum he
  rw [reducedStarFactor_reflected_sum hs ht, ha0] at hsum
  norm_num at hsum
  have hsumN : s + 1 = 3 * b := by exact_mod_cast hsum
  rw [ha0] at hd
  omega

end ResearchMain.DominationRoots
