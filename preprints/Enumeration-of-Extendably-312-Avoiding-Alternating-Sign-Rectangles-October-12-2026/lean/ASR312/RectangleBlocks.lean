import ASR312.PivotBounds

namespace ASR312

 def rectangleTopBlock {r k : ℕ} (A : Rectangle r (k+1)) (p : Fin r)
    (hk : p.val < k+1) : Rectangle p.val p.val :=
    fun i j => A ⟨i.val,by omega⟩ ⟨j.val+1,by omega⟩

 def suffixRectangle {r k : ℕ} (A : Rectangle r k) (s : ℕ) : Rectangle (r-s) (k-s) :=
    fun i j => A ⟨s+i.val,by omega⟩ ⟨s+j.val,by omega⟩

 theorem rectangleTopBlock_asm {r k : ℕ} (A : Rectangle r (k+1))
    (he : ExtendablyAvoids312 A) (p : Fin r) (hp : A p 0 = .plus) (hpk : p.val < k+1) :
    IsASM (rectangleTopBlock A p hpk) ∧ Avoids312 (rectangleTopBlock A p hpk) := by
  obtain ⟨n,hr,hk,B,hB,hav,hmatch⟩ := he
  cases n with
  | zero => omega
  | succ n =>
    let P := Fin.castLE hr p
    have hP : B P 0 = .plus := by
      have hz : Fin.castLE hk 0 = (0 : Fin (n+1)) := Fin.ext rfl
      simpa only [hz,hp] using hmatch p 0
    have ht := asm_pivot_topBlock B hB hav P hP
    have hh : topBlock B P = rectangleTopBlock A p hpk := by
      funext i j
      have hi : i.val < p.val := i.isLt
      have hj : j.val < p.val := j.isLt
      exact hmatch ⟨i.val,by omega⟩ ⟨j.val+1,by omega⟩
    exact hh ▸ ht

 theorem rectangle_pivot_top_right_zero {r k : ℕ} (A : Rectangle r (k+1))
    (he : ExtendablyAvoids312 A) (p : Fin r) (hp : A p 0 = .plus)
    (i : Fin r) (j : Fin (k+1)) (hi : i < p) (hj : p.val < j.val) : A i j = .zero := by
  obtain ⟨n,hr,hk,B,hB,hav,hmatch⟩ := he
  cases n with
  | zero => omega
  | succ n =>
    have hP : B (Fin.castLE hr p) 0 = .plus := by
      have hz : Fin.castLE hk 0 = (0 : Fin (n+1)) := Fin.ext rfl
      simpa only [hz,hp] using hmatch p 0
    exact (hmatch i j).symm.trans ((asm_pivot_top_facts B hB hav _ hP).1 _ _ hi hj)

 theorem rectangle_pivot_below_left_zero {r k : ℕ} (A : Rectangle r (k+1))
    (he : ExtendablyAvoids312 A) (p : Fin r) (hp : A p 0 = .plus)
    (i : Fin r) (j : Fin (k+1)) (hi : p < i) (hj : j.val < p.val) : A i j = .zero := by
  obtain ⟨n,hr,hk,B,hB,hav,hmatch⟩ := he
  cases n with
  | zero => omega
  | succ n =>
    have hP : B (Fin.castLE hr p) 0 = .plus := by
      have hz : Fin.castLE hk 0 = (0 : Fin (n+1)) := Fin.ext rfl
      simpa only [hz,hp] using hmatch p 0
    exact (hmatch i j).symm.trans (asm_below_left_zero B hB hav _ hP _ _ hi hj)

 theorem rectangle_negative_pivot_diagonal {r k : ℕ} (A : Rectangle r (k+1))
    (he : ExtendablyAvoids312 A) (p : Fin r) (z : Fin (k+1))
    (hp : A p 0 = .plus) (hz : A p z = .minus) : p.val = z.val := by
  obtain ⟨n,hr,hk,B,hB,hav,hmatch⟩ := he
  cases n with
  | zero => omega
  | succ n =>
    have hP : B (Fin.castLE hr p) 0 = .plus := by
      have he0 : Fin.castLE hk 0 = (0 : Fin (n+1)) := Fin.ext rfl
      simpa only [he0,hp] using hmatch p 0
    have hZ : B (Fin.castLE hr p) (Fin.castLE hk z) = .minus := (hmatch p z).trans hz
    exact congrArg (fun i : Fin (n+1) => i.val) (asm_negative_pivot_diagonal B hB hav _ _ hP hZ)

 theorem rectangle_pure_below_pivot_zero {r k : ℕ} (A : Rectangle r (k+1))
    (he : ExtendablyAvoids312 A) (p : Fin r) (hp : A p 0 = .plus)
    (hpk : p.val < k+1) (hpure : ∀ j, j ≠ 0 → A p j = .zero)
    (i : Fin r) (hi : p < i) : A i ⟨p.val,hpk⟩ = .zero := by
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
    have hj : Fin.castLE hk ⟨p.val,hpk⟩ = P := Fin.ext rfl
    have hh := hmatch i ⟨p.val,hpk⟩
    rw [hj,asm_pure_pivot_lower_zero B hB hav P hP hBPure _ hi] at hh
    exact hh.symm

end ASR312
