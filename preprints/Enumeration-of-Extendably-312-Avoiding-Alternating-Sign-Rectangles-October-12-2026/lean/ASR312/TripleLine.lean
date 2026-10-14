import ASR312.LowerBlock

namespace ASR312

 theorem line_with_unique_minus {n : ℕ} (f : Fin n → Entry)
    (hs : StartsPositive (List.ofFn f)) (he : EndsPositive (List.ofFn f))
    (hsum : ∑ j, (f j).value = 1) (z : Fin n) (hz : f z = .minus)
    (hunique : ∀ j, f j = .minus → j = z) :
    ∃ a b : Fin n, a < z ∧ z < b ∧ f a = .plus ∧ f b = .plus ∧
      ∀ j, j ≠ a → j ≠ z → j ≠ b → f j = .zero := by
  classical
  obtain ⟨a,haz,ha⟩ := plus_before_minus f hs z hz
  obtain ⟨b,hzb,hb⟩ := plus_after_minus f he z hz
  have hab : a ≠ b := ne_of_lt (lt_trans haz hzb)
  have hm : minusPositions f = {z} := by
    ext j
    simp only [minusPositions,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton]
    exact ⟨hunique j,fun h => h ▸ hz⟩
  have hc := entry_sum_counts f
  rw [hsum,hm,Finset.card_singleton] at hc
  have hpc : (plusPositions f).card = 2 := by omega
  have hsub : ({a,b} : Finset (Fin n)) ⊆ plusPositions f := by
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · simp [plusPositions,ha]
    · have he := Finset.mem_singleton.mp hj
      subst j
      simp [plusPositions,hb]
  have hset : plusPositions f = {a,b} :=
    (Finset.eq_of_subset_of_card_le hsub (by simp [hpc,hab])).symm
  refine ⟨a,b,haz,hzb,ha,hb,?_⟩
  intro j hja hjz hjb
  have hm : f j ≠ .minus := fun h => hjz (hunique j h)
  have hp : f j ≠ .plus := by
    intro h
    have hmem : j ∈ plusPositions f := by simp [plusPositions,h]
    rw [hset] at hmem
    simp [hja,hjb] at hmem
  cases hx : f j with
  | minus => exact False.elim (hm hx)
  | zero => rfl
  | plus => exact False.elim (hp hx)

 theorem asm_pivot_column_triple {n : ℕ} (A : Rectangle n n)
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin n) (hz : A p p = .minus) :
    ∃ a b : Fin n, a < p ∧ p < b ∧ A a p = .plus ∧ A b p = .plus ∧
      ∀ j, j ≠ a → j ≠ p → j ≠ b → A j p = .zero :=
  line_with_unique_minus (fun j => A j p) (ha.1.2 p).2 (ha.2.2 p).2
    (asm_column_sum A ha p) p hz (fun _j hj => asm_col_minus_unique A ha hav p hj hz)

end ASR312
