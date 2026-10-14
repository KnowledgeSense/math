import ASR312.PivotBlock

namespace ASR312

 theorem prefixSum_succ {n : ℕ} (f : Fin n → Entry) (p : Fin n) :
    prefixSum f (p.val+1) = prefixSum f p.val + (f p).value := by
  have he : Finset.univ.filter (fun j : Fin n => j.val < p.val+1) =
      insert p (Finset.univ.filter (fun j : Fin n => j.val < p.val)) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    constructor
    · intro hj
      by_cases he : j.val = p.val
      · exact Or.inl (Fin.ext he)
      · exact Or.inr (by omega)
    · rintro (rfl | hj) <;> omega
  unfold prefixSum
  rw [he,Finset.sum_insert]
  · exact add_comm _ _
  · simp

 theorem prefixSum_pos_exists_plus {n t : ℕ} (f : Fin n → Entry) (h : 0 < prefixSum f t) :
    ∃ j, j.val < t ∧ f j = .plus := by
  by_contra hh
  have hn : ∀ j, j.val < t → f j ≠ .plus := by simpa using hh
  have hle : prefixSum f t ≤ 0 := by
    apply Finset.sum_nonpos
    intro j hj
    have hnot := hn j (Finset.mem_filter.mp hj).2
    cases he : f j <;> simp_all [Entry.value]
  omega

 theorem asm_top_last_plus {n : ℕ} (A : Rectangle (n+1) (n+1)) (ha : IsASM A)
    (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus) (hp0 : 0 < p) :
    ∃ q, q < p ∧ A q p = .plus := by
  have hh := (asm_pivot_top_facts A ha hav p hp).2 p hp0 le_rfl
  exact prefixSum_pos_exists_plus (fun q => A q p) (by rw [hh]; norm_num)

 theorem asm_below_left_zero {n : ℕ} (A : Rectangle (n+1) (n+1)) (ha : IsASM A)
    (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus)
    (q b : Fin (n+1)) (hpq : p < q) (hbp : b < p) : A q b = .zero := by
  have hp0 : 0 < p := lt_of_le_of_lt (Fin.zero_le b) hbp
  obtain ⟨t,htp,htpplus⟩ := asm_top_last_plus A ha hav p hp hp0
  have hplus (c : Fin (n+1)) (hcp : c < p) : A q c ≠ .plus := by
    intro hqc
    by_cases hc0 : c = 0
    · subst c
      exact (ne_of_gt hpq) (firstColumn_plus_unique A ha.1 hqc hp)
    · exact hav ⟨t,p,q,0,c,p,htp,hpq,Fin.pos_iff_ne_zero.mpr hc0,hcp,htpplus,hp,hqc⟩
  have hminus : A q b ≠ .minus := by
    intro hqb
    obtain ⟨c,hcb,hqc⟩ := plus_before_minus (A q) (ha.1.1 q).2.1 b hqb
    exact hplus c (lt_trans hcb hbp) hqc
  cases he : A q b with
  | minus => exact False.elim (hminus he)
  | zero => rfl
  | plus => exact False.elim (hplus b hbp he)

 theorem suffix_zero_of_prefix_total {n t : ℕ} (f : Fin n → Entry)
    (ht : (∑ j, (f j).value) = prefixSum f t)
    (hn : ∀ j, t ≤ j.val → 0 ≤ (f j).value) (j : Fin n) (hj : t ≤ j.val) : f j = .zero := by
  have he := Finset.sum_filter_add_sum_filter_not (s:=(Finset.univ : Finset (Fin n)))
    (p:=fun j => j.val < t) (f:=fun j => (f j).value)
  change prefixSum f t + _ = _ at he
  rw [ht] at he
  have hz : (∑ j ∈ Finset.univ.filter (fun j : Fin n => ¬j.val < t), (f j).value) = 0 := by omega
  have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => hn k (by have := (Finset.mem_filter.mp hk).2; omega))).mp hz
  have hval := hs j (by simp; omega)
  cases hx : f j <;> simp_all [Entry.value]

 theorem asm_pure_pivot_lower_zero {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus)
    (hpure : ∀ b, b ≠ 0 → A p b = .zero) (q : Fin (n+1)) (hpq : p < q) : A q p = .zero := by
  apply suffix_zero_of_prefix_total (fun q => A q p) (t:=p.val+1)
  · rw [asm_column_sum A ha p,prefixSum_succ]
    by_cases hp0 : p = 0
    · subst p
      simp [prefixSum,hp,Entry.value]
    · rw [(asm_pivot_top_facts A ha hav p hp).2 p (Fin.pos_iff_ne_zero.mpr hp0) le_rfl,hpure p hp0]
      rfl
  · intro t ht
    have hpt : p < t := by exact ht
    have hn : A t p ≠ .minus := by
      intro htp
      obtain ⟨c,hcp,htc⟩ := plus_before_minus (A t) (ha.1.1 t).2.1 p htp
      rw [asm_below_left_zero A ha hav p hp t c hpt hcp] at htc
      cases htc
    cases hx : A t p <;> simp_all [Entry.value]
  · exact hpq

end ASR312
