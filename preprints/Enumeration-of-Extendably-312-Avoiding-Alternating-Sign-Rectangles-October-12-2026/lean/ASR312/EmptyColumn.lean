import ASR312.SchroderEnumeration

namespace ASR312

 def prependZeroColumn {r k : ℕ} (A : Rectangle r k) : Rectangle r (k+1) :=
   fun i => Fin.cons .zero (A i)

 def dropFirstColumn {r k : ℕ} (A : Rectangle r (k+1)) : Rectangle r k :=
   fun i j => A i j.succ

 theorem prependZeroColumn_row {r k : ℕ} (A : Rectangle r k) (i : Fin r) :
    nonzeroEntries (row (prependZeroColumn A) i) = nonzeroEntries (row A i) := by
  simp [row,prependZeroColumn,List.ofFn_succ,nonzeroEntries]

 theorem prependZeroColumn_col_zero {r k : ℕ} (A : Rectangle r k) :
    nonzeroEntries (col (prependZeroColumn A) 0) = [] := by
  simp [col,prependZeroColumn,nonzeroEntries,List.ofFn_const]

 theorem prependZeroColumn_col_succ {r k : ℕ} (A : Rectangle r k) (j : Fin k) :
    col (prependZeroColumn A) j.succ = col A j := by
  simp [col,prependZeroColumn]

 theorem prependZeroColumn_asr {r k : ℕ} (A : Rectangle r k) :
    IsASR (prependZeroColumn A) ↔ IsASR A := by
  constructor
  · intro h
    exact ⟨fun i => by simpa only [Alternates,StartsPositive,EndsPositive,prependZeroColumn_row] using h.1 i,
      fun j => by simpa only [prependZeroColumn_col_succ] using h.2 j.succ⟩
  · intro h
    refine ⟨fun i => ?_,fun j => ?_⟩
    · simpa only [Alternates,StartsPositive,EndsPositive,prependZeroColumn_row] using h.1 i
    · refine Fin.cases ?_ (fun j => ?_) j
      · simp [Alternates,StartsPositive,prependZeroColumn_col_zero]
      · simpa only [prependZeroColumn_col_succ] using h.2 j

 theorem prepend_drop {r k : ℕ} (A : Rectangle r (k+1)) (hz : ∀ i, A i 0 = .zero) :
    prependZeroColumn (dropFirstColumn A) = A := by
  funext i j
  refine Fin.cases ?_ (fun j => ?_) j
  · exact (hz i).symm
  · rfl

 theorem drop_prepend {r k : ℕ} (A : Rectangle r k) :
    dropFirstColumn (prependZeroColumn A) = A := by
  funext i j; simp [dropFirstColumn,prependZeroColumn]

 theorem prependZeroColumn_nonemptyRows {r k : ℕ} (A : Rectangle r k) :
    nonemptyRows (prependZeroColumn A) = nonemptyRows A := by
  classical
  unfold nonemptyRows
  congr 1
  ext i
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨j,hj⟩
    revert hj
    refine Fin.cases ?_ (fun j => ?_) j
    · simp [prependZeroColumn]
    · intro hj; exact ⟨j,by simpa [prependZeroColumn] using hj⟩
  · rintro ⟨j,hj⟩
    exact ⟨j.succ,by simpa [prependZeroColumn] using hj⟩

 theorem prependZeroColumn_extendable {r k : ℕ} (A : Rectangle r k)
    (he : ExtendablyAvoids312 A) : ExtendablyAvoids312 (prependZeroColumn A) := by
  obtain ⟨n,hr,hk,B,hB,hav,hmatch⟩ := he
  refine ⟨n+1,by omega,by omega,pivotInsert B,pivotInsert_asm B hB,
    pivotInsert_avoids312 B hav,?_⟩
  intro i j
  have ei : Fin.castLE (by omega : r ≤ n+1) i = (Fin.castLE hr i).castSucc := Fin.ext rfl
  rw [ei]
  refine Fin.cases ?_ (fun j => ?_) j
  · have ej : Fin.castLE (by omega : k+1 ≤ n+1) 0 = (0 : Fin (n+1)) := Fin.ext rfl
    rw [ej,pivotInsert_upper_zero]
    rfl
  · have ej : Fin.castLE (by omega : k+1 ≤ n+1) j.succ = (Fin.castLE hk j).succ := Fin.ext rfl
    rw [ej,pivotInsert_upper]
    exact hmatch i j

 theorem dropFirstColumn_extendable {r k : ℕ} (A : Rectangle r (k+1))
    (he : ExtendablyAvoids312 A) (hz : ∀ i, A i 0 = .zero) :
    ExtendablyAvoids312 (dropFirstColumn A) := by
  obtain ⟨n,hr,hk,B,hB,hav,hmatch⟩ := he
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨p,hp⟩ := asm_firstColumn_exists ⟨B,hB,hav⟩
    change B p 0 = .plus at hp
    have hpr : r ≤ p.val := by
      by_contra hn
      have hlt : p.val < r := by omega
      have hh := hmatch ⟨p.val,hlt⟩ 0
      have ei : Fin.castLE hr ⟨p.val,hlt⟩ = p := Fin.ext rfl
      have ej : Fin.castLE hk 0 = (0 : Fin (n+1)) := Fin.ext rfl
      rw [ei,ej,hp,hz] at hh
      cases hh
    have ht := asm_pivot_topBlock B hB hav p hp
    refine ⟨p.val+k,by omega,by omega,directSum (topBlock B p) (reversalMatrix k),
      directSum_asm _ _ ht.1 (reversalMatrix_asm k),
      directSum_avoids312 _ _ ht.2 (reversalMatrix_avoids312 k),?_⟩
    intro i j
    have hi : i.val < p.val := by omega
    by_cases hj : j.val < p.val
    · rw [directSum_of_left _ _ _ _ (by exact hi) (by exact hj)]
      unfold topBlock dropFirstColumn
      have hh := hmatch i j.succ
      exact hh
    · rw [directSum_zero_of_opposite _ _ _ _ (Or.inl ⟨by exact hi,by change p.val ≤ j.val; omega⟩)]
      have hh := hmatch i j.succ
      have hzero := (asm_pivot_top_facts B hB hav p hp).1 (Fin.castLE hr i) (Fin.castLE hk j.succ)
        (by exact hi) (by change p.val < j.val+1; omega)
      exact hzero.symm.trans hh

 theorem prependZeroColumn_extendable_iff {r k : ℕ} (A : Rectangle r k) :
    ExtendablyAvoids312 (prependZeroColumn A) ↔ ExtendablyAvoids312 A := by
  constructor
  · intro he
    simpa only [drop_prepend] using dropFirstColumn_extendable (prependZeroColumn A) he (by simp [prependZeroColumn])
  · exact prependZeroColumn_extendable A

end ASR312
