import ASR312.EmptyColumnCounting

namespace ASR312

 theorem prefixSum_eq_of_between_zero {n : ℕ} (f : Fin n → Entry) {s t : ℕ} (hst : s ≤ t)
    (hz : ∀ j, s ≤ j.val → j.val < t → f j = .zero) : prefixSum f s = prefixSum f t := by
  unfold prefixSum
  apply Finset.sum_subset
  · intro j hj
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hj ⊢
    omega
  · intro j hj hjs
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hj hjs
    rw [hz j (by omega) hj]
    rfl

 theorem pivot_row_left_zero {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p : Fin (n+1)) (hp : A p 0 = .plus)
    (j : Fin (n+1)) (hj0 : j ≠ 0) (hjp : j < p) : A p j = .zero := by
  rcases asm_pivot_cases ⟨A,ha,hav⟩ p hp with hh | hh
  · exact hh j hj0
  · exact negative_pivot_left_zero A ha hav p hp hh j hj0 hjp

 theorem firstColumn_sum_of_plus {r k : ℕ} (A : Rectangle r (k+1)) (ha : IsASR A)
    (p : Fin r) (hp : A p 0 = .plus) : entrySum (col A 0) = 1 := by
  have he := firstColumn_entries A ha
  rcases he with he | he
  · have hh := (exists_nonzero_iff (fun i => A i 0)).mpr ⟨p,by rw [hp]; decide⟩
    exact False.elim (hh he)
  · rw [← nonzeroEntries_sum,he]
    rfl

 theorem firstColumn_pivot_outside_width {r k : ℕ} (A : Rectangle r (k+1))
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (p : Fin r) (hp : A p 0 = .plus)
    (hkp : k+1 ≤ p.val) : nonemptyRows A = k+1 := by
  obtain ⟨n,hr,hk,B,hB,hav,hmatch⟩ := he
  cases n with
  | zero => omega
  | succ n =>
    let P := Fin.castLE hr p
    have hP : B P 0 = .plus := by
      have hz : Fin.castLE hk 0 = (0 : Fin (n+1)) := Fin.ext rfl
      simpa only [hz,hp] using hmatch p 0
    have hc (j : Fin (k+1)) : entrySum (col A j) = 1 := by
      by_cases hj0 : j = 0
      · subst j; exact firstColumn_sum_of_plus A ha p hp
      · let J := Fin.castLE hk j
        have hJP : J < P := by change j.val < p.val; omega
        have hJ0 : J ≠ 0 := by intro h; apply hj0; apply Fin.ext; exact congrArg (fun t : Fin (n+1) => t.val) h
        have heq : entrySum (col A j) = prefixSum (fun q => B q J) r := by
          rw [prefixSum_eq _ hr,take_ofFn hr]
          unfold col
          congr 1
          congr 1
          funext i
          exact (hmatch i j).symm
        rw [heq]
        have hprefix := (asm_pivot_top_facts B hB hav P hP).2 J (Fin.pos_iff_ne_zero.mpr hJ0) (le_of_lt hJP)
        rw [← prefixSum_eq_of_between_zero (fun q => B q J) (s:=p.val) (t:=r) (Nat.le_of_lt p.isLt)]
        · exact hprefix
        · intro q hq _
          have hPq : P ≤ q := hq
          rcases lt_or_eq_of_le hPq with hPq | rfl
          · exact asm_below_left_zero B hB hav P hP q J hPq hJP
          · exact pivot_row_left_zero B hB hav P hP J hJ0 hJP
    have ht := total_sum_nonemptyRows A ha
    rw [Finset.sum_comm] at ht
    have hv : (∑ j : Fin (k+1), ∑ i : Fin r, (A i j).value) = (k+1 : ℕ) := by
      simp_rw [← col_entrySum,hc]
      simp
    rw [hv] at ht
    exact_mod_cast ht.symm

 theorem firstColumn_pivot_lt_width {r k : ℕ} (A : Rectangle r (k+1))
    (ha : IsASR A) (he : ExtendablyAvoids312 A) (p : Fin r) (hp : A p 0 = .plus)
    (hd : nonemptyRows A < k+1) : p.val < k+1 := by
  by_contra hn
  have hh := firstColumn_pivot_outside_width A ha he p hp (by omega)
  omega

end ASR312
