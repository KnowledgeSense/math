import FourGeneratedSemigroups.PrimaryStaircase

noncomputable section
namespace FourGeneratedSemigroups

/-- The paired critical degrees used by the secondary ordering. -/
def SecondaryCriticalOrdering {S : NumericalSemigroup} (G : FourGenerated S) : Prop :=
  CriticalArc G.generators G.positive 1 0 ∧
  criticalExponent G.generators G.positive 2*G.generators 2=
    criticalExponent G.generators G.positive 3*G.generators 3

lemma impossible_secondary_middle_difference (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (hp : criticalExponent d hd 2*d 2=criticalExponent d hd 3*d 3)
    (a b : Factorization) (ha0 : a 0=0) (hb0 : b 0=0)
    (h : factorizationMap d a=factorizationMap d b)
    (hi : b 2<a 2) (hb1 : b 1<criticalExponent d hd 1)
    (hb3 : b 3<criticalExponent d hd 3)
    (hother : ∀ j, j≠2 → a j≤b j) : False := by
  have he : a-b=Finsupp.single 2 (a 2-b 2) := by
    ext j
    by_cases hj : j=2
    · subst j; simp
    · simp [hj,Nat.sub_eq_zero_of_le (hother j hj)]
  have hw := equal_weight_tsub d a b h
  rw [he,factorizationMap_single] at hw
  have hmin := criticalExponent_le d hd 2 (a 2-b 2)
    ⟨by omega,b-a,by simp [Nat.sub_eq_zero_of_le (Nat.le_of_lt hi)],hw.symm⟩
  have hle : Finsupp.single 2 (criticalExponent d hd 2)≤a :=
    Finsupp.single_le_iff.mpr (by omega)
  obtain ⟨r,hr⟩ := le_iff_exists_add.mp hle
  let c := Finsupp.single 3 (criticalExponent d hd 3)+r
  have hc : factorizationMap d c=factorizationMap d b := by
    have hh := h
    rw [hr,map_add,factorizationMap_single,hp] at hh
    simpa [c] using hh
  have h0 : c 0=0 := by simp [c,hr] at *; assumption
  have h1 : c 1=a 1 := by simp [c,hr]
  have h2 : b 2≤c 2 := by
    have hh : a 2=criticalExponent d hd 2+r 2 := by simp [hr]
    simp only [c,Finsupp.add_apply,Finsupp.single_eq_of_ne (by decide : (2:Fin 4)≠3)]
    omega
  have h3 : b 3<c 3 := by simp only [c,Finsupp.add_apply,Finsupp.single_eq_same]; omega
  have ha1 := hother 1 (by decide)
  by_cases hEq : a 1=b 1
  · have hl : b≤c := by intro i; fin_cases i <;> simp_all ; omega
    have hbc := equal_weight_of_le d hd b c hc.symm hl
    have := congrArg (fun u : Factorization => u 3) hbc
    omega
  · exact impossible_single_positive_difference d hd b c hc.symm 1
      (by omega) hb1 (by intro j hj; fin_cases j <;> simp_all ; omega)

theorem secondaryBox_weight_injective (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (hp : criticalExponent d hd 2*d 2=criticalExponent d hd 3*d 3)
    (a b : Factorization) (ha0 : a 0=0) (hb0 : b 0=0)
    (ha1 : a 1<criticalExponent d hd 1) (ha3 : a 3<criticalExponent d hd 3)
    (hb1 : b 1<criticalExponent d hd 1) (hb3 : b 3<criticalExponent d hd 3)
    (h : factorizationMap d a=factorizationMap d b) : a=b := by
  by_cases h1 : a 1≤b 1 <;> by_cases h2 : a 2≤b 2 <;> by_cases h3 : a 3≤b 3
  · apply equal_weight_of_le d hd a b h
    intro i; fin_cases i <;> simp_all
  · exact False.elim (impossible_single_positive_difference d hd a b h 3
      (by omega) ha3 (by intro j hj; fin_cases j <;> simp_all))
  · exact False.elim (impossible_secondary_middle_difference d hd hp a b ha0 hb0 h
      (by omega) hb1 hb3 (by intro j hj; fin_cases j <;> simp_all))
  · by_cases h1' : a 1=b 1
    · have hle : b≤a := by intro i; fin_cases i <;> simp_all <;> omega
      exact (equal_weight_of_le d hd b a h.symm hle).symm
    · exact False.elim (impossible_single_positive_difference d hd b a h.symm 1
        (by omega) hb1 (by intro j hj; fin_cases j <;> simp_all <;> omega))
  · exact False.elim (impossible_single_positive_difference d hd a b h 1
      (by omega) ha1 (by intro j hj; fin_cases j <;> simp_all))
  · by_cases h2' : a 2=b 2
    · have hle : b≤a := by intro i; fin_cases i <;> simp_all <;> omega
      exact (equal_weight_of_le d hd b a h.symm hle).symm
    · exact False.elim (impossible_secondary_middle_difference d hd hp b a hb0 ha0 h.symm
        (by omega) ha1 ha3 (by intro j hj; fin_cases j <;> simp_all <;> omega))
  · by_cases h3' : a 3=b 3
    · have hle : b≤a := by intro i; fin_cases i <;> simp_all <;> omega
      exact (equal_weight_of_le d hd b a h.symm hle).symm
    · exact False.elim (impossible_single_positive_difference d hd b a h.symm 3
        (by omega) hb3 (by intro j hj; fin_cases j <;> simp_all <;> omega))
  · have hle : b≤a := by intro i; fin_cases i <;> simp_all <;> omega
    exact (equal_weight_of_le d hd b a h.symm hle).symm


/-- Secondary paired critical relations also give uniqueness of staircase degrees. -/
theorem secondary_staircase_weight_injective {S : NumericalSemigroup}
    (G : FourGenerated S) (hG : SecondaryCriticalOrdering G) :
    Set.InjOn (fun c : Factorization => (factorizationMap G.generators c : ℤ)) (staircase G) := by
  intro a ha b hb hab
  exact secondaryBox_weight_injective G.generators G.positive hG.2 a b ha.1 hb.1
    (apery_coordinate_lt_of_criticalArc G 1 hG.1 a ha.2.2) ha.2.1
    (apery_coordinate_lt_of_criticalArc G 1 hG.1 b hb.2.2) hb.2.1
    (Int.ofNat_inj.mp hab)

/-- The actual secondary staircase parametrizes the actual Apéry set. -/
theorem secondary_staircase_bijOn {S : NumericalSemigroup}
    (G : FourGenerated S) (hG : SecondaryCriticalOrdering G) :
    Set.BijOn (fun c : Factorization => (factorizationMap G.generators c : ℤ))
      (staircase G) (S.apery (G.generators 0)) := by
  refine ⟨fun _ h => h.2.2,secondary_staircase_weight_injective G hG,?_⟩
  intro w hw
  obtain ⟨c,hc,hc0,hc3⟩ := apery_has_bounded_factorization G w hw
  exact ⟨c,⟨hc0,hc3,by simpa [hc] using hw⟩,hc⟩

end FourGeneratedSemigroups
