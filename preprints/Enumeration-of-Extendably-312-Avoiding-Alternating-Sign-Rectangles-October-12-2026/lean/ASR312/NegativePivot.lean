import ASR312.Prefixes
import Mathlib.Order.Interval.Finset.Fin

namespace ASR312

 theorem asm_column_sum {n : ℕ} (A : Rectangle n n) (ha : IsASM A) (j : Fin n) :
    ∑ i, (A i j).value = 1 := by
  rw [← col_entrySum]
  exact balanced_column_sums A ha.1 ((nonemptyRows_eq_rows_iff A).mpr ha.2.1) j

 theorem asm_prefix_at_negative {n : ℕ} (A : Rectangle n n) (ha : IsASM A)
    (hav : Avoids312 A) (p z : Fin n) (hz : A p z = .minus) :
    prefixSum (fun q => A q z) p.val = 1 := by
  have hb := prefixSum_bounds (fun q => A q z) (le_of_lt p.isLt) (ha.1.2 z).1 (ha.1.2 z).2
  obtain ⟨q,hqp,hq⟩ := plus_before_minus (fun q => A q z) (ha.1.2 z).2 p hz
  have hpos : ∀ t ∈ Finset.univ.filter (fun t : Fin n => t.val < p.val), 0 ≤ (A t z).value := by
    intro t ht
    have htp : t < p := (Finset.mem_filter.mp ht).2
    have hm : A t z ≠ .minus := fun h => (ne_of_lt htp) (asm_col_minus_unique A ha hav z h hz)
    cases hx : A t z <;> simp_all [Entry.value]
  have hmem : q ∈ Finset.univ.filter (fun t : Fin n => t.val < p.val) := by
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact hqp
  have hh := Finset.single_le_sum hpos hmem
  rw [hq] at hh
  change 1 ≤ prefixSum (fun q => A q z) p.val at hh
  omega

 theorem asm_prefix_left_of_negative {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p z : Fin (n+1))
    (hp : A p 0 = .plus) (hz : A p z = .minus) (b : Fin (n+1)) (hb0 : 0 < b) (hbz : b < z) :
    prefixSum (fun q => A q b) p.val = 1 := by
  have hb := prefixSum_bounds (fun q => A q b) (le_of_lt p.isLt) (ha.1.2 b).1 (ha.1.2 b).2
  have he : ExtendablyAvoids312 A := (asm_extendable_iff A ha).mpr hav
  have hpb : A p b ≠ .plus := by
    rcases row_firstColumn_structure A ha.1 he p hp with hsingle | ⟨z',u,hz'0,hz'u,hz',hu,hrest⟩
    · rw [hsingle b (ne_of_gt hb0)]
      exact Entry.noConfusion
    · have hzz' : z = z' := asm_row_minus_unique A ha hav p hz hz'
      subst z'
      have hbu : b ≠ u := ne_of_lt (lt_trans hbz hz'u)
      rw [hrest b (ne_of_gt hb0) (ne_of_lt hbz) hbu]
      exact Entry.noConfusion
  by_contra hneq
  have hzero : prefixSum (fun q => A q b) p.val = 0 := by omega
  obtain ⟨t,hpt,htb⟩ := plus_after_prefix_of_total (fun q => A q b) (asm_column_sum A ha b) hzero
  have hpt' : p < t := by
    have hne : t ≠ p := by intro ht; subst t; exact hpb htb
    change p.val < t.val
    have hn : p.val ≠ t.val := fun h => hne (Fin.ext h.symm)
    omega
  obtain ⟨q,hqp,hqz⟩ := plus_before_minus (fun q => A q z) (ha.1.2 z).2 p hz
  exact hav ⟨q,p,t,0,b,z,hqp,hpt',hb0,hbz,hqz,hp,htb⟩

 theorem asm_prefix_outside_negative {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p z : Fin (n+1))
    (hp : A p 0 = .plus) (hz : A p z = .minus) (b : Fin (n+1))
    (hb : b = 0 ∨ z < b) : prefixSum (fun q => A q b) p.val = 0 := by
  apply Finset.sum_eq_zero
  intro q hq
  have hqp : q < p := (Finset.mem_filter.mp hq).2
  have hzero : A q b = .zero := by
    rcases hb with rfl | hzb
    · have hm := firstColumn_not_minus A ha.1 q
      have hh : A q 0 ≠ .plus := fun h => (ne_of_lt hqp) (firstColumn_plus_unique A ha.1 h hp)
      cases hx : A q 0 with
      | minus => exact False.elim (hm hx)
      | zero => rfl
      | plus => exact False.elim (hh hx)
    · exact top_right_of_minus_zero A ha.1 ((asm_extendable_iff A ha).mpr hav) p hp hz q hqp hzb
  change (A q b).value = 0
  rw [hzero]
  rfl

 theorem asm_negative_pivot_diagonal {n : ℕ} (A : Rectangle (n+1) (n+1))
    (ha : IsASM A) (hav : Avoids312 A) (p z : Fin (n+1))
    (hp : A p 0 = .plus) (hz : A p z = .minus) : p = z := by
  classical
  have hrow (q : Fin (n+1)) : (∑ b, (A q b).value) = 1 := by
    obtain ⟨b,hb⟩ := asm_row_exists_plus A ha q
    exact row_sum_of_plus A ha.1 q hb
  have htotal : (∑ b, prefixSum (fun q => A q b) p.val) = (p.val : ℤ) := by
    simp only [prefixSum]
    rw [Finset.sum_comm]
    simp_rw [hrow]
    have he : Finset.univ.filter (fun q : Fin (n+1) => q.val < p.val) = Finset.Iio p := by
      ext q
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iio]
      rfl
    rw [he]
    simp
  have hcol (b : Fin (n+1)) : prefixSum (fun q => A q b) p.val =
      if b ∈ Finset.Ioc 0 z then (1:ℤ) else 0 := by
    by_cases hmem : b ∈ Finset.Ioc 0 z
    · rw [ite_eq_left hmem]
      obtain ⟨hb0,hbz⟩ := Finset.mem_Ioc.mp hmem
      rcases lt_or_eq_of_le hbz with hbz | rfl
      · exact asm_prefix_left_of_negative A ha hav p z hp hz b hb0 hbz
      · exact asm_prefix_at_negative A ha hav p b hz
    · rw [ite_eq_right hmem]
      apply asm_prefix_outside_negative A ha hav p z hp hz b
      by_cases hb0 : b = 0
      · exact Or.inl hb0
      · exact Or.inr (lt_of_not_ge (fun hbz => hmem
          (Finset.mem_Ioc.mpr ⟨Fin.pos_iff_ne_zero.mpr hb0,hbz⟩)))
  simp_rw [hcol] at htotal
  have hsum : (∑ b : Fin (n+1), if b ∈ Finset.Ioc 0 z then (1:ℤ) else 0) = z.val := by
    rw [Finset.sum_boole]
    have he : Finset.univ.filter (fun b : Fin (n+1) => b ∈ Finset.Ioc 0 z) = Finset.Ioc 0 z := by
      ext b
      simp
    rw [he,Fin.card_Ioc]
    simp
  rw [hsum] at htotal
  apply Fin.ext
  exact_mod_cast htotal.symm

end ASR312
