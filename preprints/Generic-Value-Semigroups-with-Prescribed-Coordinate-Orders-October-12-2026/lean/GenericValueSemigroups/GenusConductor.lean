import GenericValueSemigroups.WeightDeficit

namespace GenericValueSemigroups
open scoped Classical

/-- The maximum deficit with its first attaining index, for the actual weight enumeration. -/
theorem exists_first_weight_deficit_maximum {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (i j : Fin d) (hij : i ≠ j) :
    ∃ D J : ℕ, (∀ k, weightAt r hr hd k ≤ k+D) ∧
      weightAt r hr hd J=J+D ∧ (∀ k, k<J → weightAt r hr hd k<k+D) := by
  obtain ⟨D,J,h,hJ⟩ := exists_weight_deficit_maximum r hr hd i j hij
  have he : ∃ k, weightAt r hr hd k=k+D := ⟨J,hJ⟩
  refine ⟨D,Nat.find he,h,Nat.find_spec he,?_⟩
  intro k hk
  have hne := Nat.find_min he hk
  have hb := h k
  omega

theorem first_count_deficit_maximum {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (D J : ℕ)
    (h : ∀ k, weightAt r hr hd k ≤ k+D) (hJ : weightAt r hr hd J=J+D)
    (hmin : ∀ k, k<J → weightAt r hr hd k<k+D) :
    (J+D-weightCount r (J+D)=D) ∧
      (∀ n, n-weightCount r n≤D) ∧
      (∀ n, n<J+D → n-weightCount r n<D) := by
  have hcount := count_deficit_attained r hr hd D J h hJ
  rw [hJ] at hcount
  refine ⟨by omega, ?_, ?_⟩
  · intro n
    have hb := count_deficit_bound r hr hd D h n
    omega
  · intro n hn
    have hD : 0<D := by
      by_contra hbad
      have hz : D=0 := by omega
      have hj : 0<J := by omega
      have hh := hmin 0 hj
      simp only [weightAt_zero, zero_add, hz] at hh
      omega
    have hb := count_deficit_bound r hr hd D h n
    by_contra hbad
    have heq : n=weightCount r n+D := by omega
    have hidx : weightCount r n<J := by omega
    have hsmall := hmin (weightCount r n) hidx
    have hlarge := weightAt_unbounded r hr hd n (weightCount r n) (le_refl _)
    omega

/-- Genus and conductor of the greedy value set. -/
theorem greedy_genus_conductor {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (i j : Fin d) (hij : i ≠ j) :
    ∃ D C : ℕ, ∃ gaps : Finset ℕ,
      (∀ n, n ∈ gaps ↔ n ∉ Set.range (greedy (weightAt r hr hd))) ∧
      gaps.card=D ∧
      (∀ N, (∀ n, N≤n → n ∈ Set.range (greedy (weightAt r hr hd))) ↔ C≤N) ∧
      C-weightCount r C=D ∧ (∀ n, n-weightCount r n≤D) ∧
      (∀ n, n<C → n-weightCount r n<D) := by
  obtain ⟨D,J,h,hJ,hmin⟩ := exists_first_weight_deficit_maximum r hr hd i j hij
  obtain ⟨gaps,hg,hcard⟩ := greedy_gaps_finite_card (weightAt r hr hd) D J h hJ
  obtain ⟨hat,hbound,hfirst⟩ := first_count_deficit_maximum r hr hd D J h hJ hmin
  refine ⟨D,J+D,gaps,hg,hcard,?_,hat,hbound,hfirst⟩
  intro N
  exact greedy_conductor (weightAt r hr hd) (weightAt_zero r hr hd) D J h hJ hmin N

/-- The exact maximum formula uses signed counting deficits. -/
theorem signed_count_deficit_maximum {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (D J : ℕ)
    (h : ∀ k, weightAt r hr hd k ≤ k+D) (hJ : weightAt r hr hd J=J+D)
    (hmin : ∀ k, k<J → weightAt r hr hd k<k+D) :
    ((J+D : ℕ) : ℤ) - (weightCount r (J+D) : ℤ) = (D : ℤ) ∧
      (∀ n : ℕ, (n : ℤ)-(weightCount r n : ℤ) ≤ (D : ℤ)) ∧
      (∀ n, n<J+D → (n : ℤ)-(weightCount r n : ℤ) < (D : ℤ)) := by
  have hc := count_deficit_attained r hr hd D J h hJ
  rw [hJ] at hc
  refine ⟨by omega, ?_, ?_⟩
  · intro n
    have hb := count_deficit_bound r hr hd D h n
    omega
  · intro n hn
    have hh := (first_count_deficit_maximum r hr hd D J h hJ hmin).2.2 n hn
    omega

/-- The first maximum is below the uniform cutoff given by any two distinct coordinates. -/
theorem conductor_lt_two_coordinate_cutoff {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (D J : ℕ)
    (h : ∀ k, weightAt r hr hd k ≤ k+D) (hJ : weightAt r hr hd J=J+D)
    (hmin : ∀ k, k<J → weightAt r hr hd k<k+D)
    (i j : Fin d) (hij : i ≠ j) : J+D < 4*r i*r j := by
  have hp : 0<4*r i*r j := Nat.mul_pos (Nat.mul_pos (by decide) (hr i)) (hr j)
  by_cases hz : J+D=0
  · omega
  have hD : 0<D := by
    have hh := (first_count_deficit_maximum r hr hd D J h hJ hmin).2.2 0 (by omega)
    omega
  by_contra hn
  have hm := weightCount_ge_above_cutoff r hr i j hij (n := J+D) (by omega)
  have hc := count_deficit_attained r hr hd D J h hJ
  rw [hJ] at hc
  omega

end GenericValueSemigroups
