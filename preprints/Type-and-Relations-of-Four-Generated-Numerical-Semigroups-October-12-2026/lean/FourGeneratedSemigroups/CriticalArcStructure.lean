import FourGeneratedSemigroups.SecondaryStaircase

noncomputable section
namespace FourGeneratedSemigroups

/-- Every critical relation has a nonempty support away from its distinguished generator. -/
theorem criticalArc_exists (d : Fin 4 → ℕ) (hd : ∀ i,0<d i) (i : Fin 4) :
    ∃ j, CriticalArc d hd i j := by
  obtain ⟨c,hci,hc⟩ := (criticalExponent_spec d hd i).2
  have hn : c≠0 := by
    intro he
    rw [he,map_zero] at hc
    have := (criticalExponent_spec d hd i).1
    have := hd i
    nlinarith
  have hex : ∃ j,c j≠0 := by
    by_contra hh
    push Not at hh
    exact hn (Finsupp.ext hh)
  obtain ⟨j,hj⟩ := hex
  refine ⟨j,?_,c,hci,by omega,hc⟩
  intro he; subst j; contradiction

/-- If a vertex has a unique outgoing critical arc, its critical relations are pure powers. -/
theorem criticalArc_pure_of_unique (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (hu : ∀ i j k, CriticalArc d hd i j → CriticalArc d hd i k → j=k)
    {i j : Fin 4} (hij : CriticalArc d hd i j) :
    ∃ q : ℕ, 0<q ∧ q*d j=criticalExponent d hd i*d i := by
  obtain ⟨c,hci,hcj,hc⟩ := hij.2
  have he : c=Finsupp.single j (c j) := by
    ext k
    by_cases hkj : k=j
    · subst k; simp
    · have hz : c k=0 := by
        by_contra hk
        have hik : i≠k := by intro he; subst k; contradiction
        have hh := hu i j k hij ⟨hik,c,hci,by omega,hc⟩
        exact hkj hh.symm
      simp [hkj,hz]
  exact ⟨c j,hcj,by rw [he,factorizationMap_single] at hc; exact hc⟩

/-- A critical graph with unique outgoing neighbors consists of reciprocal pairs. -/
theorem criticalArc_reverse_of_unique (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (hu : ∀ i j k, CriticalArc d hd i j → CriticalArc d hd i k → j=k)
    {i j : Fin 4} (hij : CriticalArc d hd i j) : CriticalArc d hd j i := by
  obtain ⟨k,hjk⟩ := criticalArc_exists d hd j
  suffices k=i by simpa [this] using hjk
  by_contra hki
  obtain ⟨q,hq,hqe⟩ := criticalArc_pure_of_unique d hd hu hij
  obtain ⟨r,hr,hre⟩ := criticalArc_pure_of_unique d hd hu hjk
  have hmin : criticalExponent d hd j≤q := criticalExponent_le d hd j q
    ⟨hq,Finsupp.single i (criticalExponent d hd i),by simp [Ne.symm hij.1],
      by simpa using hqe.symm⟩
  let c : Factorization := Finsupp.single j (q-criticalExponent d hd j)+Finsupp.single k r
  have hci : c i=0 := by simp [c,hij.1,Ne.symm hki]
  have hck : 0<c k := by simp [c,hjk.1.symm,hr]
  have hc : factorizationMap d c=criticalExponent d hd i*d i := by
    simp only [c,map_add,factorizationMap_single]
    have hh : q-criticalExponent d hd j+criticalExponent d hd j=q := Nat.sub_add_cancel hmin
    nlinarith
  have hh := hu i j k hij ⟨Ne.symm hki,c,hci,hck,hc⟩
  exact hjk.1 hh

/-- Reciprocal unique critical arcs have equal critical degrees. -/
theorem criticalDegree_eq_of_unique (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (hu : ∀ i j k, CriticalArc d hd i j → CriticalArc d hd i k → j=k)
    {i j : Fin 4} (hij : CriticalArc d hd i j) :
    criticalExponent d hd i*d i=criticalExponent d hd j*d j := by
  obtain ⟨q,hq,hqe⟩ := criticalArc_pure_of_unique d hd hu hij
  have hji := criticalArc_reverse_of_unique d hd hu hij
  obtain ⟨r,hr,hre⟩ := criticalArc_pure_of_unique d hd hu hji
  have hqmin := criticalExponent_le d hd j q
    ⟨hq,Finsupp.single i (criticalExponent d hd i),by simp [Ne.symm hij.1],
      by simpa using hqe.symm⟩
  have hrmin := criticalExponent_le d hd i r
    ⟨hr,Finsupp.single j (criticalExponent d hd j),by simp [hij.1],
      by simpa using hre.symm⟩
  nlinarith [hd i,hd j]


/-- In a unique-neighbor critical graph the entire critical fiber is exactly
the two pure-power factorizations at the paired vertices. -/
theorem critical_fiber_eq_pair (d : Fin 4 → ℕ) (hd : ∀ i,0<d i)
    (hu : ∀ i j k, CriticalArc d hd i j → CriticalArc d hd i k → j=k)
    {i j : Fin 4} (hij : CriticalArc d hd i j) (c : Factorization) :
    factorizationMap d c=criticalExponent d hd i*d i ↔
      c=Finsupp.single i (criticalExponent d hd i) ∨
      c=Finsupp.single j (criticalExponent d hd j) := by
  have hdeg := criticalDegree_eq_of_unique d hd hu hij
  constructor
  · intro hc
    rcases critical_factorization_dichotomy d hd i c hc with he|hci
    · exact Or.inl he
    · right
      have he : c=Finsupp.single j (c j) := by
        ext k
        by_cases hkj : k=j
        · subst k; simp
        · have hz : c k=0 := by
            by_contra hk
            have hik : i≠k := by intro he; subst k; contradiction
            exact hkj (hu i j k hij ⟨hik,c,hci,by omega,hc⟩).symm
          simp [hkj,hz]
      have hw : c j*d j=criticalExponent d hd j*d j := by
        rw [he,factorizationMap_single,hdeg] at hc
        exact hc
      have hj : c j=criticalExponent d hd j := by nlinarith [hd j]
      simpa only [hj] using he
  · rintro (rfl|rfl)
    · exact factorizationMap_single d i _
    · simpa using hdeg.symm

end FourGeneratedSemigroups
