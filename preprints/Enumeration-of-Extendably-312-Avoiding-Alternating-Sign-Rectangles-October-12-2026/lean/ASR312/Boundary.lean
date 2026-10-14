import ASR312.Definitions
import Mathlib.Data.Fin.Rev
import Mathlib.Tactic.NormNum

namespace ASR312

 theorem nonzero_ofFn_zero (n : ℕ) :
    nonzeroEntries (List.ofFn (fun _ : Fin n => Entry.zero)) = [] := by
  simp [nonzeroEntries,List.ofFn_const]

 theorem nonzero_ofFn_single {n : ℕ} (t : Fin n) :
    nonzeroEntries (List.ofFn (fun j => if j = t then Entry.plus else .zero)) = [.plus] := by
  induction n with
  | zero => exact Fin.elim0 t
  | succ n ih =>
    refine Fin.cases ?_ (fun t => ?_) t
    · simp [List.ofFn_succ,nonzeroEntries,Fin.succ_ne_zero,List.ofFn_const]
    · simpa [List.ofFn_succ,nonzeroEntries,Fin.succ_ne_zero,Ne.symm (Fin.succ_ne_zero t),Fin.succ_inj] using ih t

 def zeroRectangle (r k : ℕ) : Rectangle r k := fun _ _ => .zero

 theorem zeroRectangle_asr (r k : ℕ) : IsASR (zeroRectangle r k) := by
  constructor
  · intro i
    have hh : nonzeroEntries (row (zeroRectangle r k) i) = [] := nonzero_ofFn_zero k
    simp [Alternates,StartsPositive,EndsPositive,hh]
  · intro j
    have hh : nonzeroEntries (col (zeroRectangle r k) j) = [] := nonzero_ofFn_zero r
    simp [Alternates,StartsPositive,hh]

 def reversalMatrix (n : ℕ) : Rectangle n n := fun i j => if j = i.rev then .plus else .zero

 theorem reversalMatrix_row (n : ℕ) (i : Fin n) :
    nonzeroEntries (row (reversalMatrix n) i) = [.plus] := nonzero_ofFn_single i.rev

 theorem reversalMatrix_col (n : ℕ) (j : Fin n) :
    nonzeroEntries (col (reversalMatrix n) j) = [.plus] := by
  have he : (fun i => reversalMatrix n i j) = (fun i => if i = j.rev then Entry.plus else .zero) := by
    funext i
    unfold reversalMatrix
    by_cases h : i = j.rev
    · subst i
      simp
    · have hh : j ≠ i.rev := fun he => h ((Fin.rev_eq_iff.mp he.symm))
      simp [h,hh]
  rw [col,he]
  exact nonzero_ofFn_single j.rev

 theorem reversalMatrix_asm (n : ℕ) : IsASM (reversalMatrix n) := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro i
    simp [Alternates,StartsPositive,EndsPositive,reversalMatrix_row]
  · intro j
    simp [Alternates,StartsPositive,reversalMatrix_col]
  · intro i
    exact ⟨i.rev,by simp [reversalMatrix]⟩
  · intro j
    exact ⟨⟨j.rev,by simp [reversalMatrix]⟩,by simp [EndsPositive,reversalMatrix_col]⟩

 theorem reversalMatrix_avoids312 (n : ℕ) : Avoids312 (reversalMatrix n) := by
  rintro ⟨i₁,i₂,i₃,j₁,j₂,j₃,_,h23,h12,_,_,h21,h32⟩
  have hj1 : j₁ = i₂.rev := by simpa [reversalMatrix] using h21
  have hj2 : j₂ = i₃.rev := by simpa [reversalMatrix] using h32
  rw [hj1,hj2] at h12
  exact (not_lt_of_gt h23) (Fin.rev_lt_rev.mp h12)

 theorem zeroRectangle_extendable (r k : ℕ) : ExtendablyAvoids312 (zeroRectangle r k) := by
  refine ⟨r+k,by omega,by omega,reversalMatrix (r+k),reversalMatrix_asm _,reversalMatrix_avoids312 _,?_⟩
  intro i j
  have hne : Fin.castLE (by omega : k ≤ r+k) j ≠
      (Fin.castLE (by omega : r ≤ r+k) i).rev := by
    intro he
    have hv := congrArg Fin.val he
    simp only [Fin.val_castLE,Fin.val_rev] at hv
    have hi := i.isLt
    have hj := j.isLt
    omega
  simp [reversalMatrix,hne,zeroRectangle]

 theorem nonemptyRows_zero_iff {r k : ℕ} (A : Rectangle r k) :
    nonemptyRows A = 0 ↔ A = zeroRectangle r k := by
  classical
  simp only [nonemptyRows,Finset.card_eq_zero,Finset.filter_eq_empty_iff,Finset.mem_univ,true_implies]
  constructor
  · intro h
    funext i j
    exact Classical.not_not.mp (fun hn => h ⟨j,hn⟩)
  · rintro rfl i ⟨j,hj⟩
    exact hj rfl

 theorem S_zero (r k : ℕ) : S r k 0 = 1 := by
  classical
  unfold S
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨⟨zeroRectangle r k,zeroRectangle_asr r k,(nonemptyRows_zero_iff _).mpr rfl,
    zeroRectangle_extendable r k⟩,?_⟩
  intro A
  apply Subtype.ext
  exact (nonemptyRows_zero_iff _).mp A.property.2.1

end ASR312
