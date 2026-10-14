import ASR312.NegativePivot

namespace ASR312

 theorem asm_prefix_left_of_top_plus {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus)
    (hpure : ∀ b, b ≠ 0 → A p b = .zero) {q c : Fin (n+1)} (hqp : q < p)
    (hqc : A q c = .plus) (b : Fin (n+1)) (hb0 : 0 < b) (hbc : b < c) :
    prefixSum (fun t => A t b) p.val = 1 := by
  have hb := prefixSum_bounds (fun t => A t b) (le_of_lt p.isLt) (ha.1.2 b).1 (ha.1.2 b).2
  by_contra hneq
  have hzero : prefixSum (fun t => A t b) p.val = 0 := by omega
  obtain ⟨t,hpt,htb⟩ := plus_after_prefix_of_total (fun t => A t b) (asm_column_sum A ha b) hzero
  have hpt' : p < t := by
    have hne : t ≠ p := by
      intro ht
      subst t
      rw [hpure b (ne_of_gt hb0)] at htb
      cases htb
    change p.val < t.val
    have hn : p.val ≠ t.val := fun h => hne (Fin.ext h.symm)
    omega
  exact hav ⟨q,p,t,0,b,c,hqp,hpt',hb0,hbc,hqc,hp,htb⟩

 theorem asm_prefix_of_top_plus {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus)
    (hpure : ∀ b, b ≠ 0 → A p b = .zero) {q c : Fin (n+1)} (hqp : q < p)
    (hqc : A q c = .plus) : prefixSum (fun t => A t c) p.val = 1 := by
  have hb := prefixSum_bounds (fun t => A t c) (le_of_lt p.isLt) (ha.1.2 c).1 (ha.1.2 c).2
  have hc0 : 0 < c := by
    apply Fin.pos_iff_ne_zero.mpr
    intro hh
    subst c
    exact (ne_of_lt hqp) (firstColumn_plus_unique A ha.1 hqc hp)
  by_contra hneq
  have hzero : prefixSum (fun t => A t c) p.val = 0 := by omega
  have hm : ∃ v, v < p ∧ A v c = .minus := by
    by_contra hn
    have hn' : ∀ v, v < p → A v c ≠ .minus := by simpa using hn
    have hpos : ∀ t ∈ Finset.univ.filter (fun t : Fin (n+1) => t.val < p.val), 0 ≤ (A t c).value := by
      intro t ht
      have ht' : t < p := (Finset.mem_filter.mp ht).2
      have hh := hn' t ht'
      cases he : A t c <;> simp_all [Entry.value]
    have hmem : q ∈ Finset.univ.filter (fun t : Fin (n+1) => t.val < p.val) := by
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact hqp
    have hs := Finset.single_le_sum hpos hmem
    rw [hqc] at hs
    change 1 ≤ prefixSum (fun t => A t c) p.val at hs
    omega
  obtain ⟨v,hvp,hvc⟩ := hm
  obtain ⟨b,hcb,hvb⟩ := plus_after_minus (A v) (ha.1.1 v).2.2 c hvc
  have hh := asm_prefix_left_of_top_plus A ha hav p hp hpure hvp hvb c hc0 hcb
  omega

noncomputable def topPlusColumns {n : ℕ} (A : Rectangle n n) (p : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun c => ∃ q, q < p ∧ A q c = .plus)

 theorem topPlusColumns_nonempty {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (p : Fin (n+1)) (hp0 : 0 < p) : (topPlusColumns A p).Nonempty := by
  classical
  obtain ⟨c,hc⟩ := asm_row_exists_plus A ha 0
  refine ⟨c,?_⟩
  simp only [topPlusColumns,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨0,hp0,hc⟩

 theorem above_max_top_plus_zero {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (p : Fin (n+1)) (hne : (topPlusColumns A p).Nonempty)
    (q b : Fin (n+1)) (hqp : q < p) (hmb : (topPlusColumns A p).max' hne < b) : A q b = .zero := by
  classical
  have hp (c : Fin (n+1)) (hmc : (topPlusColumns A p).max' hne < c) : A q c ≠ .plus := by
    intro hqc
    have hc : c ∈ topPlusColumns A p := by
      simp only [topPlusColumns,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨q,hqp,hqc⟩
    exact not_le_of_gt hmc (Finset.le_max' _ _ hc)
  have hm : A q b ≠ .minus := by
    intro hqb
    obtain ⟨c,hbc,hqc⟩ := plus_after_minus (A q) (ha.1.1 q).2.2 b hqb
    exact hp c (lt_trans hmb hbc) hqc
  cases he : A q b with
  | minus => exact False.elim (hm he)
  | zero => rfl
  | plus => exact False.elim (hp b hmb he)

 theorem asm_positive_pivot_cutoff {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus)
    (hpure : ∀ b, b ≠ 0 → A p b = .zero) (hp0 : 0 < p) :
    (topPlusColumns A p).max' (topPlusColumns_nonempty A ha p hp0) = p := by
  classical
  let hn := topPlusColumns_nonempty A ha p hp0
  let m := (topPlusColumns A p).max' hn
  have hm : m ∈ topPlusColumns A p := Finset.max'_mem _ hn
  obtain ⟨q,hqp,hqm⟩ := (Finset.mem_filter.mp hm).2
  have hcol (b : Fin (n+1)) : prefixSum (fun t => A t b) p.val =
      if b ∈ Finset.Ioc 0 m then (1:ℤ) else 0 := by
    by_cases hmem : b ∈ Finset.Ioc 0 m
    · rw [ite_eq_left hmem]
      obtain ⟨hb0,hbm⟩ := Finset.mem_Ioc.mp hmem
      rcases lt_or_eq_of_le hbm with hbm | rfl
      · exact asm_prefix_left_of_top_plus A ha hav p hp hpure hqp hqm b hb0 hbm
      · exact asm_prefix_of_top_plus A ha hav p hp hpure hqp hqm
    · rw [ite_eq_right hmem]
      apply Finset.sum_eq_zero
      intro t ht
      have htp : t < p := (Finset.mem_filter.mp ht).2
      have htzero : A t b = .zero := by
        by_cases hb0 : b = 0
        · subst b
          have hminus := firstColumn_not_minus A ha.1 t
          have hplus : A t 0 ≠ .plus := fun h => (ne_of_lt htp) (firstColumn_plus_unique A ha.1 h hp)
          cases he : A t 0 with
          | minus => exact False.elim (hminus he)
          | zero => rfl
          | plus => exact False.elim (hplus he)
        · have hmb : m < b := lt_of_not_ge (fun hbm => hmem
            (Finset.mem_Ioc.mpr ⟨Fin.pos_iff_ne_zero.mpr hb0,hbm⟩))
          exact above_max_top_plus_zero A ha p hn t b htp hmb
      change (A t b).value = 0
      rw [htzero]
      rfl
  have hrow (q : Fin (n+1)) : (∑ b, (A q b).value) = 1 := by
    obtain ⟨b,hb⟩ := asm_row_exists_plus A ha q
    exact row_sum_of_plus A ha.1 q hb
  have htotal : (∑ b, prefixSum (fun t => A t b) p.val) = (p.val : ℤ) := by
    simp only [prefixSum]
    rw [Finset.sum_comm]
    simp_rw [hrow]
    have he : Finset.univ.filter (fun t : Fin (n+1) => t.val < p.val) = Finset.Iio p := by
      ext t
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
      rfl
    rw [he]
    simp
  simp_rw [hcol] at htotal
  rw [Finset.sum_boole] at htotal
  have he : Finset.univ.filter (fun b : Fin (n+1) => b ∈ Finset.Ioc 0 m) = Finset.Ioc 0 m := by
    ext b
    simp
  rw [he,Fin.card_Ioc] at htotal
  simp only [Fin.val_zero,Nat.sub_zero] at htotal
  apply Fin.ext
  exact_mod_cast htotal

end ASR312
