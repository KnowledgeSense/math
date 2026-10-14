import ASR312.BlockDiagonal

namespace ASR312

 theorem suffixRectangle_row {r k : ℕ} (A : Rectangle r k) (s : ℕ) (i : Fin (r-s)) :
    row (suffixRectangle A s) i = (row A ⟨s+i.val,by omega⟩).drop s := by
  simp only [row,drop_ofFn]
  rfl

 theorem suffixRectangle_col {r k : ℕ} (A : Rectangle r k) (s : ℕ) (j : Fin (k-s)) :
    col (suffixRectangle A s) j = (col A ⟨s+j.val,by omega⟩).drop s := by
  simp only [col,drop_ofFn]
  rfl

 theorem suffixRectangle_asr {r k : ℕ} (A : Rectangle r k) (ha : IsASR A) (s : ℕ)
    (hl : ∀ i j, s ≤ i.val → j.val < s → A i j = .zero)
    (hu : ∀ i j, i.val < s → s ≤ j.val → A i j = .zero) : IsASR (suffixRectangle A s) := by
  have hrow (i : Fin (r-s)) : nonzeroEntries (row (suffixRectangle A s) i) =
      nonzeroEntries (row A ⟨s+i.val,by omega⟩) := by
    rw [suffixRectangle_row]
    exact nonzeroEntries_drop_ofFn _ (fun j hj => hl _ j (by simp) hj)
  have hcol (j : Fin (k-s)) : nonzeroEntries (col (suffixRectangle A s) j) =
      nonzeroEntries (col A ⟨s+j.val,by omega⟩) := by
    rw [suffixRectangle_col]
    exact nonzeroEntries_drop_ofFn _ (fun i hi => hu i _ hi (by simp))
  exact ⟨fun i => by simpa only [Alternates,StartsPositive,EndsPositive,hrow] using ha.1 ⟨s+i.val,by omega⟩,
    fun j => by simpa only [Alternates,StartsPositive,hcol] using ha.2 ⟨s+j.val,by omega⟩⟩

 theorem pureSuffix_asr {r k : ℕ} (A : Rectangle r (k+1)) (ha : IsASR A)
    (he : ExtendablyAvoids312 A) (p : Fin r) (hp : A p 0 = .plus)
    (hpk : p.val < k+1) (hpure : ∀ j, j ≠ 0 → A p j = .zero) :
    IsASR (suffixRectangle A (p.val+1)) := by
  apply suffixRectangle_asr A ha
  · intro i j hi hj
    have hpi : p < i := hi
    have hjp : j.val ≤ p.val := by omega
    rcases lt_or_eq_of_le hjp with hjp | hjp
    · exact rectangle_pivot_below_left_zero A he p hp i j hpi hjp
    · have hj : j = ⟨p.val,hpk⟩ := Fin.ext hjp
      subst j
      exact rectangle_pure_below_pivot_zero A he p hp hpk hpure i hpi
  · intro i j hi hj
    have hip : i ≤ p := by change i.val ≤ p.val; omega
    rcases lt_or_eq_of_le hip with hip | rfl
    · exact rectangle_pivot_top_right_zero A he p hp i j hip hj
    · exact hpure j (by apply Fin.ne_of_val_ne; change j.val ≠ 0; omega)

 theorem pureSuffix_extendable {r k : ℕ} (A : Rectangle r (k+1))
    (he : ExtendablyAvoids312 A) (p : Fin r) (hp : A p 0 = .plus)
    (hpk : p.val < k+1) (hpure : ∀ j, j ≠ 0 → A p j = .zero) :
    ExtendablyAvoids312 (suffixRectangle A (p.val+1)) := by
  obtain ⟨n,hr,hk,B,hB,hav,hmatch⟩ := he
  cases n with
  | zero => omega
  | succ n =>
    let P := Fin.castLE hr p
    have hP : B P 0 = .plus := by
      have hz : Fin.castLE hk 0 = (0 : Fin (n+1)) := Fin.ext rfl
      simpa only [hz,hp] using hmatch p 0
    have hBPure : ∀ j, j ≠ 0 → B P j = .zero := by
      rcases asm_pivot_cases ⟨B,hB,hav⟩ P hP with hh | hh
      · exact hh
      · have hj : Fin.castLE hk ⟨p.val,hpk⟩ = P := Fin.ext rfl
        have hx := hmatch p ⟨p.val,hpk⟩
        change B P P = .minus at hh
        change B P (Fin.castLE hk ⟨p.val,hpk⟩) = _ at hx
        rw [hj,hh] at hx
        by_cases hp0 : (⟨p.val,hpk⟩ : Fin (k+1)) = 0
        · rw [hp0,hp] at hx; cases hx
        · rw [hpure _ hp0] at hx; cases hx
    have hlow := asm_pure_lowerBlock B hB hav P hP hBPure
    refine ⟨n+1-(p.val+1),by omega,by omega,lowerBlock B (p.val+1),hlow.1,hlow.2,?_⟩
    intro i j
    exact hmatch ⟨p.val+1+i.val,by omega⟩ ⟨p.val+1+j.val,by omega⟩

end ASR312
