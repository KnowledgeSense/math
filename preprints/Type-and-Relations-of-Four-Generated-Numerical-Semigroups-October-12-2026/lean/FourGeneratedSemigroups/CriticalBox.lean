import FourGeneratedSemigroups.AperyFactorizations
import Mathlib.Tactic.FinCases

noncomputable section
namespace FourGeneratedSemigroups

lemma equal_weight_tsub (d : Fin 4 → ℕ) (a b : Factorization)
    (h : factorizationMap d a=factorizationMap d b) :
    factorizationMap d (a-b)=factorizationMap d (b-a) := by
  have he : a-b+b=a+(b-a) := by ext i; simp only [Finsupp.add_apply,Finsupp.tsub_apply]; omega
  have hh := congrArg (factorizationMap d) he
  simp only [map_add] at hh
  omega

lemma equal_weight_of_le (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (a b : Factorization) (h : factorizationMap d a=factorizationMap d b)
    (hle : a ≤ b) : a=b := by
  obtain ⟨rest,rfl⟩ := le_iff_exists_add.mp hle
  have hz : factorizationMap d rest=0 := by simpa using h.symm
  have hr := (factorizationMap_eq_zero_iff d hd rest).mp hz
  simp [hr]

lemma impossible_single_positive_difference (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (a b : Factorization) (h : factorizationMap d a=factorizationMap d b)
    (i : Fin 4) (hi : b i<a i) (hb : a i<criticalExponent d hd i)
    (hother : ∀ j, j≠i → a j≤b j) : False := by
  have he : a-b=Finsupp.single i (a i-b i) := by
    ext j
    by_cases hji : j=i
    · subst j; simp
    · simp [hji,Nat.sub_eq_zero_of_le (hother j hji)]
  have hw := equal_weight_tsub d a b h
  rw [he,factorizationMap_single] at hw
  have hrel : CriticalRelation d i (a i-b i) :=
    ⟨by omega,b-a,by simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt hi)],hw.symm⟩
  have hmin := criticalExponent_le d hd i (a i-b i) hrel
  omega

/-- Three varying coordinates cannot have an equal-weight collision inside all
three critical bounds. The distinguished coordinate is zero. -/
theorem criticalBox_weight_injective (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (a b : Factorization) (ha0 : a 0=0) (hb0 : b 0=0)
    (ha : ∀ i, i≠0 → a i<criticalExponent d hd i)
    (hb : ∀ i, i≠0 → b i<criticalExponent d hd i)
    (h : factorizationMap d a=factorizationMap d b) : a=b := by
  by_cases h1 : a 1≤b 1 <;> by_cases h2 : a 2≤b 2 <;> by_cases h3 : a 3≤b 3
  · apply equal_weight_of_le d hd a b h
    intro i; fin_cases i <;> simp_all
  · exact False.elim (impossible_single_positive_difference d hd a b h 3
      (by omega) (ha 3 (by decide)) (by intro j hj; fin_cases j <;> simp_all))
  · exact False.elim (impossible_single_positive_difference d hd a b h 2
      (by omega) (ha 2 (by decide)) (by intro j hj; fin_cases j <;> simp_all))
  · by_cases h1' : a 1=b 1
    · have hle : b≤a := by intro i; fin_cases i <;> simp_all <;> omega
      exact (equal_weight_of_le d hd b a h.symm hle).symm
    · exact False.elim (impossible_single_positive_difference d hd b a h.symm 1
        (by omega) (hb 1 (by decide)) (by intro j hj; fin_cases j <;> simp_all <;> omega))
  · exact False.elim (impossible_single_positive_difference d hd a b h 1
      (by omega) (ha 1 (by decide)) (by intro j hj; fin_cases j <;> simp_all))
  · by_cases h2' : a 2=b 2
    · have hle : b≤a := by intro i; fin_cases i <;> simp_all <;> omega
      exact (equal_weight_of_le d hd b a h.symm hle).symm
    · exact False.elim (impossible_single_positive_difference d hd b a h.symm 2
        (by omega) (hb 2 (by decide)) (by intro j hj; fin_cases j <;> simp_all <;> omega))
  · by_cases h3' : a 3=b 3
    · have hle : b≤a := by intro i; fin_cases i <;> simp_all <;> omega
      exact (equal_weight_of_le d hd b a h.symm hle).symm
    · exact False.elim (impossible_single_positive_difference d hd b a h.symm 3
        (by omega) (hb 3 (by decide)) (by intro j hj; fin_cases j <;> simp_all <;> omega))
  · have hle : b≤a := by intro i; fin_cases i <;> simp_all <;> omega
    exact (equal_weight_of_le d hd b a h.symm hle).symm

end FourGeneratedSemigroups
