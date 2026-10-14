import MainTheorems.DominationRoots.TopCoefficients

namespace ResearchMain.DominationRoots

open Classical Polynomial ResearchMain.Domination

variable {V : Type*} [Fintype V]

theorem exists_domination_size (G : SimpleGraph V) : ∃ k, 0 < dominationCount G k := by
  exact ⟨Fintype.card V, by rw [dominationCount_full]; omega⟩

noncomputable def dominationNumber (G : SimpleGraph V) : ℕ := Nat.find (exists_domination_size G)

theorem dominationNumber_positive_count (G : SimpleGraph V) :
    0 < dominationCount G (dominationNumber G) := Nat.find_spec (exists_domination_size G)

theorem dominationCount_below (G : SimpleGraph V) {k : ℕ} (hk : k < dominationNumber G) :
    dominationCount G k = 0 := by
  have h := Nat.find_min (exists_domination_size G) hk
  omega

theorem dominationNumber_le (G : SimpleGraph V) (S : Finset V) (hS : Dominates G S) :
    dominationNumber G ≤ S.card := by
  apply Nat.find_min'
  apply Finset.card_pos.mpr
  exact ⟨S, (mem_dominatingSets G S.card S).mpr ⟨rfl, hS⟩⟩

theorem dominationNumber_le_order (G : SimpleGraph V) : dominationNumber G ≤ Fintype.card V := by
  simpa using dominationNumber_le G Finset.univ (dominates_univ G)

theorem dominationPolynomial_factor (G : SimpleGraph V) :
    ∃ q : ℤ[X], q.Monic ∧ dominationPolynomial G = X ^ dominationNumber G * q ∧
      0 < q.coeff 0 ∧ (∀ k, 0 ≤ q.coeff k) ∧
      q.natDegree = Fintype.card V - dominationNumber G := by
  have hdvd : X ^ dominationNumber G ∣ dominationPolynomial G := by
    apply X_pow_dvd_iff.mpr
    intro k hk
    rw [dominationPolynomial_coeff, dominationCount_below G hk]
    rfl
  obtain ⟨q, hq⟩ := hdvd
  have hm : q.Monic := (monic_X_pow _).of_mul_monic_left (hq ▸ dominationPolynomial_monic G)
  have hcoeff : ∀ k, q.coeff k =
      (dominationCount G (k + dominationNumber G) : ℤ) := by
    intro k
    have h := congrArg (fun f : ℤ[X] => f.coeff (k + dominationNumber G)) hq
    rw [dominationPolynomial_coeff, coeff_X_pow_mul] at h
    exact h.symm
  refine ⟨q, hm, hq, ?_, ?_, ?_⟩
  · rw [hcoeff, zero_add]
    exact_mod_cast dominationNumber_positive_count G
  · intro k
    rw [hcoeff]
    positivity
  · have hd := congrArg natDegree hq
    rw [dominationPolynomial_natDegree, (monic_X_pow _).natDegree_mul hm, natDegree_X_pow] at hd
    omega

end ResearchMain.DominationRoots
