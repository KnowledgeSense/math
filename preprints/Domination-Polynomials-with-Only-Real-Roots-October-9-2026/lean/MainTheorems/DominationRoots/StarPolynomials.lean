import MainTheorems.DominationRoots.TraceDivisors

namespace ResearchMain.DominationRoots

open Polynomial

noncomputable def starFactor (s : ℕ) : ℤ[X] := X * (1 + X) ^ s + X ^ s

noncomputable def reducedStarFactor (s : ℕ) : ℤ[X] := (1 + X) ^ s + X ^ (s - 1)

theorem starFactor_eq (s : ℕ) (hs : 1 ≤ s) : starFactor s = X * reducedStarFactor s := by
  unfold starFactor reducedStarFactor
  rw [mul_add, ← pow_succ', Nat.sub_add_cancel hs]

theorem reducedStarFactor_natDegree (s : ℕ) (hs : 2 ≤ s) :
    (reducedStarFactor s).natDegree = s := by
  have hdegree : ((1 + X : ℤ[X]) ^ s).degree = s := by
    rw [add_comm, degree_pow, show (X + 1 : ℤ[X]).degree = 1 from degree_X_add_C 1]
    simp
  have hlt : (X ^ (s - 1) : ℤ[X]).degree < ((1 + X) ^ s : ℤ[X]).degree := by
    rw [degree_X_pow, hdegree]
    exact_mod_cast (show s - 1 < s by omega)
  unfold reducedStarFactor
  exact natDegree_eq_of_degree_eq_some ((degree_add_eq_left_of_degree_lt hlt).trans hdegree)

theorem reducedStarFactor_monic (s : ℕ) (hs : 2 ≤ s) : (reducedStarFactor s).Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one s (reducedStarFactor_natDegree s hs).le
  simp only [reducedStarFactor, coeff_add, coeff_one_add_X_pow, coeff_X_pow]
  have hne : s - 1 ≠ s := by omega
  simp [Ne.symm hne]

theorem reducedStarFactor_constant (s : ℕ) (hs : 2 ≤ s) : (reducedStarFactor s).coeff 0 = 1 := by
  simp only [reducedStarFactor, coeff_add, coeff_one_add_X_pow, coeff_X_pow]
  have hne : s - 1 ≠ 0 := by omega
  simp [Ne.symm hne]

theorem reducedStarFactor_next (s : ℕ) (hs : 1 ≤ s) :
    (reducedStarFactor s).coeff (s - 1) = (s : ℤ) + 1 := by
  have hchoose : s.choose (s - 1) = s := by
    rw [← Nat.choose_symm (Nat.sub_le s 1)]
    simpa only [Nat.sub_sub_self hs] using Nat.choose_one_right s
  simp [reducedStarFactor, coeff_one_add_X_pow, hchoose]

theorem realRoots_pow {f : ℤ[X]} (hf : f.Monic) (n : ℕ) :
    (realRoots (f ^ n)).sum = (n : ℝ) * (realRoots f).sum := by
  induction n with
  | zero => simp [realRoots, realPolynomial]
  | succ n ih =>
    rw [pow_succ, realRoots_mul (hf.pow n) hf, Multiset.sum_add, ih]
    push_cast
    ring

theorem allowedProduct_root_sum {f : ℤ[X]} {a b : ℕ}
    (he : f = linearFactor ^ a * quadraticPolynomial ^ b) :
    (realRoots f).sum = 2 * (a : ℝ) + 3 * (b : ℝ) := by
  rw [he, realRoots_mul (linearFactor_monic.pow a) (quadraticPolynomial_monic.pow b),
    Multiset.sum_add, realRoots_pow linearFactor_monic, realRoots_pow quadraticPolynomial_monic,
    linearFactor_roots, quadraticPolynomial_roots]
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
  unfold lowerRoot upperRoot
  ring

theorem reflection_splits_iff (f : ℤ[X]) :
    (realPolynomial (reflection f)).Splits ↔ (realPolynomial f).Splits := by
  constructor
  · intro hs
    have hcard := hs.natDegree_eq_card_roots
    change (realPolynomial (reflection f)).natDegree = (realRoots (reflection f)).card at hcard
    rw [realPolynomial, natDegree_map_eq_of_injective Int.cast_injective,
      reflection_natDegree, reflection_roots, Multiset.card_map] at hcard
    apply splits_iff_card_roots.mpr
    change (realRoots f).card = (realPolynomial f).natDegree
    rw [realPolynomial, natDegree_map_eq_of_injective Int.cast_injective]
    exact hcard.symm
  · intro hs
    rw [realPolynomial_reflection]
    exact (Splits.C _).mul hs.comp_neg_X

end ResearchMain.DominationRoots
