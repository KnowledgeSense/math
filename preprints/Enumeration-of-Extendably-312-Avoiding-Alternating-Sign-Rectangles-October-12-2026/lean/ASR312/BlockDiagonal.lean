import ASR312.RectangleBlocks

namespace ASR312

 def blockDiagonal {r₁ k₁ r₂ k₂ : ℕ} (A : Rectangle r₁ k₁) (B : Rectangle r₂ k₂) :
    Rectangle (r₁+r₂) (k₁+k₂) :=
  Fin.append (fun i => Fin.append (A i) (fun _ => .zero))
    (fun i => Fin.append (fun _ => .zero) (B i))

 theorem blockDiagonal_row_left {r₁ k₁ r₂ k₂ : ℕ} (A : Rectangle r₁ k₁) (B : Rectangle r₂ k₂) (i : Fin r₁) :
    nonzeroEntries (row (blockDiagonal A B) (i.castAdd r₂)) = nonzeroEntries (row A i) := by
  simp [row,blockDiagonal,nonzeroEntries,List.ofFn_fin_append,List.ofFn_const]

 theorem blockDiagonal_row_right {r₁ k₁ r₂ k₂ : ℕ} (A : Rectangle r₁ k₁) (B : Rectangle r₂ k₂) (i : Fin r₂) :
    nonzeroEntries (row (blockDiagonal A B) (i.natAdd r₁)) = nonzeroEntries (row B i) := by
  simp [row,blockDiagonal,nonzeroEntries,List.ofFn_fin_append,List.ofFn_const]

 theorem blockDiagonal_col_left {r₁ k₁ r₂ k₂ : ℕ} (A : Rectangle r₁ k₁) (B : Rectangle r₂ k₂) (j : Fin k₁) :
    nonzeroEntries (col (blockDiagonal A B) (j.castAdd k₂)) = nonzeroEntries (col A j) := by
  have hf : (fun i => blockDiagonal A B i (j.castAdd k₂)) =
      Fin.append (fun i => A i j) (fun _ : Fin r₂ => Entry.zero) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [blockDiagonal]
  simp [col,hf,nonzeroEntries,List.ofFn_fin_append,List.ofFn_const]

 theorem blockDiagonal_col_right {r₁ k₁ r₂ k₂ : ℕ} (A : Rectangle r₁ k₁) (B : Rectangle r₂ k₂) (j : Fin k₂) :
    nonzeroEntries (col (blockDiagonal A B) (j.natAdd k₁)) = nonzeroEntries (col B j) := by
  have hf : (fun i => blockDiagonal A B i (j.natAdd k₁)) =
      Fin.append (fun _ : Fin r₁ => Entry.zero) (fun i => B i j) := by
    funext i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [blockDiagonal]
  simp [col,hf,nonzeroEntries,List.ofFn_fin_append,List.ofFn_const]

 theorem blockDiagonal_asr {r₁ k₁ r₂ k₂ : ℕ} (A : Rectangle r₁ k₁) (B : Rectangle r₂ k₂)
    (ha : IsASR A) (hb : IsASR B) : IsASR (blockDiagonal A B) := by
  constructor
  · intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa only [Alternates,StartsPositive,EndsPositive,blockDiagonal_row_left] using ha.1 i
    · simpa only [Alternates,StartsPositive,EndsPositive,blockDiagonal_row_right] using hb.1 i
  · intro j
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · simpa only [Alternates,StartsPositive,blockDiagonal_col_left] using ha.2 j
    · simpa only [Alternates,StartsPositive,blockDiagonal_col_right] using hb.2 j

 theorem blockDiagonal_nonemptyRows {r₁ k₁ r₂ k₂ : ℕ} (A : Rectangle r₁ k₁) (B : Rectangle r₂ k₂)
    (ha : IsASR A) (hb : IsASR B) :
    nonemptyRows (blockDiagonal A B) = nonemptyRows A + nonemptyRows B := by
  have hl (i : Fin r₁) : (∑ j, (blockDiagonal A B (i.castAdd r₂) j).value) = ∑ j, (A i j).value := by
    rw [← row_entrySum,← nonzeroEntries_sum,blockDiagonal_row_left,nonzeroEntries_sum,row_entrySum]
  have hr (i : Fin r₂) : (∑ j, (blockDiagonal A B (i.natAdd r₁) j).value) = ∑ j, (B i j).value := by
    rw [← row_entrySum,← nonzeroEntries_sum,blockDiagonal_row_right,nonzeroEntries_sum,row_entrySum]
  have ht := total_sum_nonemptyRows (blockDiagonal A B) (blockDiagonal_asr A B ha hb)
  rw [Fin.sum_univ_add] at ht
  simp_rw [hl,hr] at ht
  rw [total_sum_nonemptyRows A ha,total_sum_nonemptyRows B hb] at ht
  exact_mod_cast ht.symm

 theorem blockDiagonal_extendable {m r k : ℕ} (A : Rectangle m m) (B : Rectangle r k)
    (ha : IsASM A) (hav : Avoids312 A) (hb : ExtendablyAvoids312 B) :
    ExtendablyAvoids312 (blockDiagonal A B) := by
  obtain ⟨n,hr,hk,C,hC,hCv,hmatch⟩ := hb
  refine ⟨m+n,by omega,by omega,directSum A C,directSum_asm A C ha hC,
    directSum_avoids312 A C hav hCv,?_⟩
  intro i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · have hi : Fin.castLE (by omega : m+r ≤ m+n) (i.castAdd r) = i.castAdd n := Fin.ext rfl
    have hj : Fin.castLE (by omega : m+k ≤ m+n) (j.castAdd k) = j.castAdd n := Fin.ext rfl
    rw [hi,hj]; simp [directSum,blockDiagonal]
  · have hi : Fin.castLE (by omega : m+r ≤ m+n) (i.castAdd r) = i.castAdd n := Fin.ext rfl
    have hj : Fin.castLE (by omega : m+k ≤ m+n) (j.natAdd m) = (Fin.castLE hk j).natAdd m := Fin.ext rfl
    rw [hi,hj]; simp [directSum,blockDiagonal]
  · have hi : Fin.castLE (by omega : m+r ≤ m+n) (i.natAdd m) = (Fin.castLE hr i).natAdd m := Fin.ext rfl
    have hj : Fin.castLE (by omega : m+k ≤ m+n) (j.castAdd k) = j.castAdd n := Fin.ext rfl
    rw [hi,hj]; simp [directSum,blockDiagonal]
  · have hi : Fin.castLE (by omega : m+r ≤ m+n) (i.natAdd m) = (Fin.castLE hr i).natAdd m := Fin.ext rfl
    have hj : Fin.castLE (by omega : m+k ≤ m+n) (j.natAdd m) = (Fin.castLE hk j).natAdd m := Fin.ext rfl
    rw [hi,hj]; simpa [directSum,blockDiagonal] using hmatch i j

end ASR312
