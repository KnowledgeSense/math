import ASR312.PureSuffix

namespace ASR312

 theorem asm_first_row_no_minus {n : ℕ} [NeZero n] (A : Rectangle n n) (ha : IsASM A)
    (j : Fin n) : A 0 j ≠ .minus := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ n =>
    have hh := (ha.1.2 j).2
    rw [col,List.ofFn_succ] at hh
    exact startsPositive_cons_not_minus hh

 theorem asm_first_row_unique_plus {n : ℕ} [NeZero n] (A : Rectangle n n) (ha : IsASM A)
    (c j : Fin n) (hc : A 0 c = .plus) (hj : j ≠ c) : A 0 j = .zero := by
  have hone : ∀ i : Fin n, A 0 i ≠ .zero → i = c := by
    intro i hi
    have hm := asm_first_row_no_minus A ha
    have hsum := row_sum_of_plus A ha.1 0 hc
    have hcount := entry_sum_counts (A 0)
    have hminus : minusPositions (A 0) = ∅ := by
      ext q
      simp only [minusPositions,Finset.mem_filter,Finset.mem_univ,true_and,Finset.notMem_empty,iff_false]
      exact hm q
    rw [hsum,hminus,Finset.card_empty] at hcount
    have hp : (plusPositions (A 0)).card = 1 := by omega
    obtain ⟨x,hx⟩ := Finset.card_eq_one.mp hp
    have hiplus : A 0 i = .plus := by
      cases he : A 0 i with
      | minus => exact False.elim (hm i he)
      | zero => exact False.elim (hi he)
      | plus => rfl
    have hi_mem : i ∈ plusPositions (A 0) := by simp [plusPositions,hiplus]
    have hc_mem : c ∈ plusPositions (A 0) := by simp [plusPositions,hc]
    rw [hx,Finset.mem_singleton] at hi_mem hc_mem
    exact hi_mem.trans hc_mem.symm
  by_contra hn
  exact hj (hone j hn)

 theorem asm_left_of_first_plus_no_minus {n : ℕ} [NeZero n] (A : Rectangle n n)
    (ha : IsASM A) (hav : Avoids312 A) (c : Fin n) (hc : A 0 c = .plus)
    (i j : Fin n) (hjc : j < c) : A i j ≠ .minus := by
  intro hij
  have hi0 : i ≠ 0 := by intro hi; subst i; exact asm_first_row_no_minus A ha j hij
  obtain ⟨a,haj,hia⟩ := plus_before_minus (A i) (ha.1.1 i).2.1 j hij
  obtain ⟨b,hib,hbj⟩ := plus_after_minus (fun q => A q j) (ha.2.2 j).2 i hij
  exact hav ⟨0,i,b,a,j,c,Fin.pos_iff_ne_zero.mpr hi0,hib,haj,hjc,hc,hia,hbj⟩

 theorem asm_left_of_first_plus_descending {n : ℕ} [NeZero n] (A : Rectangle n n)
    (ha : IsASM A) (hav : Avoids312 A) (c : Fin n) (hc : A 0 c = .plus)
    (i t j u : Fin n) (hit : i < t) (hju : j < u) (huc : u < c)
    (hij : A i j = .plus) (htu : A t u = .plus) : False := by
  have hi0 : i ≠ 0 := by
    intro hi; subst i
    have hz := asm_first_row_unique_plus A ha c j hc (ne_of_lt (lt_trans hju huc))
    rw [hz] at hij; cases hij
  exact hav ⟨0,i,t,j,u,c,Fin.pos_iff_ne_zero.mpr hi0,hit,hju,huc,hc,hij,htu⟩

 theorem emptyFirstRow_extension_witness {r k : ℕ} (A : Rectangle (r+1) k)
    (he : ExtendablyAvoids312 A) (hz : ∀ j, A 0 j = .zero) :
    ∃ (n : ℕ) (hr : r+1 ≤ n+1) (hk : k ≤ n+1) (B : Rectangle (n+1) (n+1))
      (c : Fin (n+1)), IsASM B ∧ Avoids312 B ∧ B 0 c = .plus ∧ k ≤ c.val ∧
      ∀ i j, B (Fin.castLE hr i) (Fin.castLE hk j) = A i j := by
  obtain ⟨n,hr,hk,B,hB,hav,hmatch⟩ := he
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨c,hc⟩ := asm_row_exists_plus B hB 0
    have hkc : k ≤ c.val := by
      by_contra hn
      have hlt : c.val < k := by omega
      have hi : Fin.castLE hr 0 = (0 : Fin (n+1)) := Fin.ext rfl
      have hj : Fin.castLE hk ⟨c.val,hlt⟩ = c := Fin.ext rfl
      have hh := hmatch 0 ⟨c.val,hlt⟩
      rw [hi,hj,hc,hz] at hh
      cases hh
    exact ⟨n,hr,hk,B,c,hB,hav,hc,hkc,hmatch⟩

 theorem emptyFirstRow_no_minus {r k : ℕ} (A : Rectangle (r+1) k)
    (he : ExtendablyAvoids312 A) (hz : ∀ j, A 0 j = .zero) (i : Fin (r+1)) (j : Fin k) :
    A i j ≠ .minus := by
  obtain ⟨n,hr,hk,B,c,hB,hav,hc,hkc,hmatch⟩ := emptyFirstRow_extension_witness A he hz
  rw [← hmatch i j]
  exact asm_left_of_first_plus_no_minus B hB hav c hc _ _ (by change j.val < c.val; omega)

 theorem emptyFirstRow_descending {r k : ℕ} (A : Rectangle (r+1) k)
    (he : ExtendablyAvoids312 A) (hz : ∀ j, A 0 j = .zero)
    (i t : Fin (r+1)) (j u : Fin k) (hit : i < t) (hju : j < u)
    (hij : A i j = .plus) (htu : A t u = .plus) : False := by
  obtain ⟨n,hr,hk,B,c,hB,hav,hc,hkc,hmatch⟩ := emptyFirstRow_extension_witness A he hz
  exact asm_left_of_first_plus_descending B hB hav c hc _ _ _ _ hit hju
    (by change u.val < c.val; omega) ((hmatch i j).trans hij) ((hmatch t u).trans htu)

 theorem noMinus_sum_le_one_unique {n : ℕ} (f : Fin n → Entry)
    (hm : ∀ i, f i ≠ .minus) (hs : (∑ i, (f i).value) ≤ 1)
    {p q : Fin n} (hp : f p = .plus) (hq : f q = .plus) : p = q := by
  classical
  by_contra hn
  have hnonneg (i : Fin n) : 0 ≤ (f i).value := by
    have hh := hm i
    cases he : f i <;> simp_all [Entry.value]
  have hh : (∑ i ∈ ({p,q} : Finset (Fin n)), (f i).value) ≤ ∑ i, (f i).value := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro i _ _; exact hnonneg i
  have he : (∑ i ∈ ({p,q} : Finset (Fin n)), (f i).value) = 2 := by
    simp [hn,hp,hq,Entry.value]
  rw [he] at hh
  omega

 theorem emptyFirstRow_row_plus_unique {r k : ℕ} (A : Rectangle (r+1) k)
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (hz : ∀ j, A 0 j = .zero)
    (i : Fin (r+1)) {j u : Fin k} (hj : A i j = .plus) (hu : A i u = .plus) : j = u := by
  apply noMinus_sum_le_one_unique (A i) (emptyFirstRow_no_minus A he hz i) _ hj hu
  have hs := row_sum_of_plus A ha i hj
  omega

 theorem emptyFirstRow_col_plus_unique {r k : ℕ} (A : Rectangle (r+1) k)
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (hz : ∀ j, A 0 j = .zero)
    {i t : Fin (r+1)} (j : Fin k) (hi : A i j = .plus) (ht : A t j = .plus) : i = t := by
  apply noMinus_sum_le_one_unique (fun i => A i j) (fun i => emptyFirstRow_no_minus A he hz i j) _ hi ht
  have hs := (column_sum_bounds (col A j) (ha.2 j).1 (ha.2 j).2).2
  rwa [col_entrySum] at hs

 theorem emptyFirstRow_plus_upper_closed {r k : ℕ} (A : Rectangle (r+1) k)
    (he : ExtendablyAvoids312 A) (hz : ∀ j, A 0 j = .zero)
    (i : Fin (r+1)) (j u : Fin k) (hju : j < u) (hij : A i j = .plus) :
    ∃ t, A t u = .plus := by
  obtain ⟨n,hr,hk,B,c,hB,hav,hc,hkc,hmatch⟩ := emptyFirstRow_extension_witness A he hz
  obtain ⟨t,ht⟩ := (hB.2.2 (Fin.castLE hk u)).1
  have hm := asm_left_of_first_plus_no_minus B hB hav c hc t (Fin.castLE hk u)
    (by change u.val < c.val; omega)
  have htplus : B t (Fin.castLE hk u) = .plus := by
    cases hx : B t (Fin.castLE hk u) with
    | minus => exact False.elim (hm hx)
    | zero => exact False.elim (ht hx)
    | plus => rfl
  have htr : t.val < r+1 := by
    by_contra hn
    exact asm_left_of_first_plus_descending B hB hav c hc (Fin.castLE hr i) t
      (Fin.castLE hk j) (Fin.castLE hk u) (by change i.val < t.val; omega) hju
      (by change u.val < c.val; omega) ((hmatch i j).trans hij) htplus
  refine ⟨⟨t.val,htr⟩,?_⟩
  have heq : Fin.castLE hr ⟨t.val,htr⟩ = t := Fin.ext rfl
  have hh := hmatch ⟨t.val,htr⟩ u
  rw [heq,htplus] at hh
  exact hh.symm

end ASR312
