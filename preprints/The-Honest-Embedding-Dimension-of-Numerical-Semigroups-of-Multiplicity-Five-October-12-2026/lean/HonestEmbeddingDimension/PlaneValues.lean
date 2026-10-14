import HonestEmbeddingDimension.PlaneJets

namespace HonestEmbeddingDimension

/-- Elementary cofinality of a coprime two-generator semigroup, with a cutoff below the first collision. -/
theorem two_generator_representation (m a n : ℕ) (hm : 0 < m) (hcop : m.Coprime a)
    (hn : (m-1)*a ≤ n) : ∃ k j : ℕ, j < m ∧ n = m*k + a*j := by
  let F : Fin m → Fin m := fun j => ⟨j.val*a % m, Nat.mod_lt _ hm⟩
  have hi : Function.Injective F := by
    intro i j he
    apply Fin.ext
    have he' : i.val*a ≡ j.val*a [MOD m] := congrArg Fin.val he
    have h := Nat.ModEq.cancel_right_of_coprime hcop he'
    simpa [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using h
  obtain ⟨j,hj⟩ := Finite.surjective_of_injective hi ⟨n % m,Nat.mod_lt n hm⟩
  have hmod : j.val*a ≡ n [MOD m] := congrArg Fin.val hj
  have hjle : j.val*a ≤ n := le_trans (Nat.mul_le_mul_right a (by omega)) hn
  obtain ⟨k,hk⟩ := (Nat.modEq_iff_dvd' hjle).mp hmod
  refine ⟨k,j.val,j.isLt,?_⟩
  have hsum := Nat.sub_add_cancel hjle
  rw [hk] at hsum
  simpa [Nat.mul_comm a] using hsum.symm

/-- The complete plane lemma: higher terms in a coprime coordinate do not change its value semigroup. -/
theorem polynomial_plane_values (m a : ℕ) (hm : 0 < m) (hcop : m.Coprime a)
    (Y : PowerSeries ℂ) (hY : Y.order = a) :
    polynomialValues (planeCoordinates m Y) = {n | ∃ k j : ℕ, n = m*k + a*j} := by
  ext n
  constructor
  · intro hval
    by_cases hn : n < m*a
    · obtain ⟨k,j,_,he⟩ := plane_value_below_threshold m a (Nat.ne_of_gt hm) hcop Y hY n hn hval
      exact ⟨k,j,he⟩
    · obtain ⟨k,j,_,he⟩ := two_generator_representation m a n hm hcop
        (le_trans (Nat.mul_le_mul_right a (Nat.sub_le m 1)) (Nat.le_of_not_gt hn))
      exact ⟨k,j,he⟩
  · rintro ⟨k,j,rfl⟩
    refine ⟨MvPolynomial.X 0 ^ k * MvPolynomial.X 1 ^ j, ?_⟩
    simp [planeCoordinates, PowerSeries.order_mul, PowerSeries.order_pow, hY, nsmul_eq_mul,
      mul_comm, add_comm]

/-- The formal version of the complete plane lemma, with genuine infinite substitution. -/
theorem formal_plane_values (m a : ℕ) (hm : 0 < m) (ha : 0 < a) (hcop : m.Coprime a)
    (Y : PowerSeries ℂ) (hY : Y.order = a) :
    formalValues (planeCoordinates m Y) = {n | ∃ k j : ℕ, n = m*k + a*j} := by
  have h0 : ∀ i, (planeCoordinates m Y i).constantCoeff = 0 := by
    intro i
    fin_cases i
    · simp [planeCoordinates, Nat.ne_of_gt hm]
    · apply PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
      simpa [planeCoordinates, hY] using (show (1 : ℕ∞) ≤ (a : ℕ∞) by exact_mod_cast ha)
  rw [formalValues_eq_polynomialValues _ h0]
  exact polynomial_plane_values m a hm hcop Y hY

end HonestEmbeddingDimension
