import ASR312.TopBlock

namespace ASR312

 theorem firstColumn_above_zero {n : ℕ} (A : Rectangle (n+1) (n+1)) (ha : IsASR A)
    (p : Fin (n+1)) (hp : A p 0 = .plus) (q : Fin (n+1)) (hqp : q < p) : A q 0 = .zero := by
  have hm := firstColumn_not_minus A ha q
  have hh : A q 0 ≠ .plus := fun h => (ne_of_lt hqp) (firstColumn_plus_unique A ha h hp)
  cases he : A q 0 with
  | minus => exact False.elim (hm he)
  | zero => rfl
  | plus => exact False.elim (hh he)

 theorem asm_pivot_top_facts {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus) :
    (∀ q b, q < p → p < b → A q b = .zero) ∧
    (∀ b : Fin (n+1), 0 < b → b ≤ p → prefixSum (fun q => A q b) p.val = 1) := by
  have he : ExtendablyAvoids312 A := (asm_extendable_iff A ha).mpr hav
  rcases row_firstColumn_structure A ha.1 he p hp with hpure | ⟨z,u,hz0,hzu,hz,hu,_⟩
  · by_cases hp0 : p = 0
    · subst p
      constructor
      · intro q b hq _
        exact False.elim (not_lt_of_ge (Fin.zero_le q) hq)
      · intro b hb hbp
        exact False.elim (not_lt_of_ge hbp hb)
    · have hpos : 0 < p := Fin.pos_iff_ne_zero.mpr hp0
      let hn := topPlusColumns_nonempty A ha p hpos
      have hm := asm_positive_pivot_cutoff A ha hav p hp hpure hpos
      have hpMem : p ∈ topPlusColumns A p := by
        have hh := Finset.max'_mem (topPlusColumns A p) hn
        rwa [hm] at hh
      obtain ⟨q,hqp,hqpplus⟩ := (Finset.mem_filter.mp hpMem).2
      constructor
      · intro q b hqp hpb
        apply above_max_top_plus_zero A ha p hn q b hqp
        simpa only [hm] using hpb
      · intro b hb0 hbp
        rcases lt_or_eq_of_le hbp with hbp | rfl
        · exact asm_prefix_left_of_top_plus A ha hav p hp hpure hqp hqpplus b hb0 hbp
        · exact asm_prefix_of_top_plus A ha hav b hp hpure hqp hqpplus
  · have hzp := asm_negative_pivot_diagonal A ha hav p z hp hz
    subst z
    constructor
    · intro q b hqp hpb
      exact top_right_of_minus_zero A ha.1 he p hp hz q hqp hpb
    · intro b hb0 hbp
      rcases lt_or_eq_of_le hbp with hbp | rfl
      · exact asm_prefix_left_of_negative A ha hav p p hp hz b hb0 hbp
      · exact asm_prefix_at_negative A ha hav b b hz

 theorem asm_pivot_topBlock {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus) :
    IsASM (topBlock A p) ∧ Avoids312 (topBlock A p) := by
  have hf := asm_pivot_top_facts A ha hav p hp
  exact ⟨topBlock_asm A ha p hf.1 (firstColumn_above_zero A ha.1 p hp) hf.2,
    topBlock_avoids312 A hav p⟩

end ASR312
