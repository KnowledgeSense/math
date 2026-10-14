import ASR312.SingleMinus

namespace ASR312

noncomputable def plusPositions {n : ℕ} (f : Fin n → Entry) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => f j = .plus)

noncomputable def minusPositions {n : ℕ} (f : Fin n → Entry) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun j => f j = .minus)

 theorem entry_sum_counts {n : ℕ} (f : Fin n → Entry) :
    (∑ j, (f j).value) = (plusPositions f).card - (minusPositions f).card := by
  classical
  have hv (j : Fin n) : (f j).value =
      (if f j = .plus then (1:ℤ) else 0) - (if f j = .minus then (1:ℤ) else 0) := by
    cases f j <;> norm_num [Entry.value]
  simp_rw [hv]
  rw [Finset.sum_sub_distrib]
  simp [plusPositions,minusPositions]

 theorem row_sum_of_plus {r k : ℕ} (A : Rectangle r k) (ha : IsASR A)
    (i : Fin r) {j : Fin k} (hj : A i j = .plus) : (∑ t, (A i t).value) = 1 := by
  rw [← row_entrySum,row_sum_one_or_zero _ (ha.1 i).1 (ha.1 i).2.1 (ha.1 i).2.2]
  apply ite_eq_right
  intro he
  have hh := (row_nonzeroEntries_empty_iff A i).mp he j
  rw [hj] at hh
  cases hh

 theorem minusPositions_eq_singleton {r k : ℕ} (A : Rectangle r k)
    (he : ExtendablyAvoids312 A) (i : Fin r) {z : Fin k} (hz : A i z = .minus) :
    minusPositions (A i) = {z} := by
  classical
  ext t
  simp only [minusPositions,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
  constructor
  · exact fun ht => extendable_row_minus_unique A he i ht hz
  · rintro rfl; exact hz

 theorem row_firstColumn_structure {r k : ℕ} (A : Rectangle r (k+1))
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (i : Fin r) (hi : A i 0 = .plus) :
    (∀ j, j ≠ 0 → A i j = .zero) ∨
    ∃ z u : Fin (k+1), 0 < z ∧ z < u ∧ A i z = .minus ∧ A i u = .plus ∧
      ∀ j, j ≠ 0 → j ≠ z → j ≠ u → A i j = .zero := by
  classical
  have hsum := row_sum_of_plus A ha i hi
  have hc := entry_sum_counts (A i)
  rw [hsum] at hc
  by_cases hm : ∃ z, A i z = .minus
  · obtain ⟨z,hz⟩ := hm
    obtain ⟨u,hzu,hu⟩ := plus_after_minus (A i) (ha.1 i).2.2 z hz
    have hz0 : z ≠ 0 := by intro hh; subst z; rw [hi] at hz; cases hz
    have hzpos : 0 < z := Fin.pos_iff_ne_zero.mpr hz0
    have hu0 : u ≠ 0 := ne_of_gt (lt_trans hzpos hzu)
    rw [minusPositions_eq_singleton A he i hz,Finset.card_singleton] at hc
    have hpCard : (plusPositions (A i)).card = 2 := by omega
    have hsub : ({0,u} : Finset (Fin (k+1))) ⊆ plusPositions (A i) := by
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · simp [plusPositions,hi]
      · have hj' := Finset.mem_singleton.mp hj
        subst j
        simp [plusPositions,hu]
    have hpSet : plusPositions (A i) = {0,u} :=
      (Finset.eq_of_subset_of_card_le hsub (by simp [hpCard,Ne.symm hu0])).symm
    refine Or.inr ⟨z,u,hzpos,hzu,hz,hu,?_⟩
    intro j hj0 hjz hju
    have hn : A i j ≠ .minus := fun hj => hjz (extendable_row_minus_unique A he i hj hz)
    have hp : A i j ≠ .plus := by
      intro hj
      have hjmem : j ∈ plusPositions (A i) := by simp [plusPositions,hj]
      rw [hpSet] at hjmem
      simp [hj0,hju] at hjmem
    cases hx : A i j with
    | minus => exact False.elim (hn hx)
    | zero => rfl
    | plus => exact False.elim (hp hx)
  · have hm' : ∀ j, A i j ≠ .minus := by simpa using hm
    have hminus : minusPositions (A i) = ∅ := by simp [minusPositions,hm']
    rw [hminus,Finset.card_empty] at hc
    have hpCard : (plusPositions (A i)).card = 1 := by omega
    have hsub : ({0} : Finset (Fin (k+1))) ⊆ plusPositions (A i) := by simp [plusPositions,hi]
    have hpSet : plusPositions (A i) = {0} :=
      (Finset.eq_of_subset_of_card_le hsub (by simp [hpCard])).symm
    refine Or.inl ?_
    intro j hj0
    have hn := hm' j
    have hp : A i j ≠ .plus := by
      intro hj
      have hjmem : j ∈ plusPositions (A i) := by simp [plusPositions,hj]
      rw [hpSet] at hjmem
      exact hj0 (Finset.mem_singleton.mp hjmem)
    cases hx : A i j with
    | minus => exact False.elim (hn hx)
    | zero => rfl
    | plus => exact False.elim (hp hx)

end ASR312
