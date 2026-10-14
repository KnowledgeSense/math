import MainTheorems.DominationRoots.ParityPairs

namespace ResearchMain.DominationRoots

open Classical Polynomial ResearchMain.Domination

variable {V : Type*} [Fintype V]

theorem compatible_row_count (G : SimpleGraph V) (A : Finset V) :
    (∑ B : Finset V, if Compatible G A B then (1 : ℕ) else 0) =
      2 ^ (compatibleVertices G A).card := by
  have hf : Finset.univ.filter (Compatible G A) = (compatibleVertices G A).powerset := by
    ext B
    simp [compatible_iff_subset]
  rw [Finset.sum_boole, hf, Finset.card_powerset]
  norm_cast

theorem compatiblePairs_card (G : SimpleGraph V) :
    (compatiblePairs G).card = ∑ A : Finset V, 2 ^ (compatibleVertices G A).card := by
  unfold compatiblePairs
  rw [Finset.card_filter, Fintype.sum_prod_type]
  simp_rw [compatible_row_count]

theorem power_two_mod_two (k : ℕ) :
    ((2 ^ k : ℕ) : ZMod 2) = if k = 0 then 1 else 0 := by
  rw [Nat.cast_pow, ZMod.natCast_self]
  by_cases hk : k = 0 <;> simp [hk]

theorem dominatingSets_mod_two (G : SimpleGraph V) :
    ((allDominatingSets G).card : ZMod 2) = 1 := by
  have hp := compatiblePairs_mod_two G
  rw [compatiblePairs_card, Nat.cast_sum] at hp
  simp_rw [power_two_mod_two, Finset.card_eq_zero, compatibleVertices_empty_iff] at hp
  have hf : Finset.univ.filter (Dominates G) = allDominatingSets G := by
    ext A
    simp [mem_allDominatingSets]
  rw [Finset.sum_boole, hf] at hp
  exact hp

theorem dominationPolynomial_mod_two (G : SimpleGraph V) :
    (((dominationPolynomial G).eval 1 : ℤ) : ZMod 2) = 1 := by
  rw [dominationPolynomial_eval_one, Int.cast_natCast]
  exact dominatingSets_mod_two G

theorem dominationPolynomial_not_root_minus_one (G : SimpleGraph V) :
    ¬(dominationPolynomial G).IsRoot (-1) := by
  intro hroot
  have hneg : (-1 : ZMod 2) = 1 := by
    have h2 : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    linear_combination -h2
  let φ : ℤ →+* ZMod 2 := Int.castRingHom (ZMod 2)
  have he := congrArg φ hroot
  have hm := dominationPolynomial_mod_two G
  have hv := eval₂_at_apply φ (-1 : ℤ) (p := dominationPolynomial G)
  have hv' := eval₂_at_apply φ (1 : ℤ) (p := dominationPolynomial G)
  have hφneg : φ (-1) = 1 := by rw [map_neg, map_one]; exact hneg
  have hφone : φ 1 = 1 := φ.map_one
  rw [hφneg] at hv
  rw [hφone] at hv'
  have hcast : φ ((dominationPolynomial G).eval 1) = 0 := by
    rw [← hv', hv]
    exact he
  change (((dominationPolynomial G).eval 1 : ℤ) : ZMod 2) = 0 at hcast
  rw [hm] at hcast
  exact one_ne_zero hcast

end ResearchMain.DominationRoots
