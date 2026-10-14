import ASR312.BalancedSuffix

namespace ASR312

noncomputable def balancedAssembly {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m) : Rectangle (r+n) (r+m) :=
  Fin.append A (fun i j => if j.val = (gappedColumn A hc s hs i).val then .plus else .zero)

theorem balancedAssembly_prefix {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m) :
    rowPrefix (balancedAssembly A hc s hs) = A := by
  funext i j
  simp [rowPrefix,balancedAssembly]

theorem balancedAssembly_extendable {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (ha : IsASR A) (hn : nonemptyRows A = r) (he : ExtendablyAvoids312 A) :
    ExtendablyAvoids312 (balancedAssembly A hc s hs) := by
  have hm : m ≤ n := by have hh := Finset.card_le_univ s; simpa [hs] using hh
  refine ⟨r+n,le_rfl,by omega,gappedCompletion A hc s hs,
    gappedCompletion_asm A hc s hs ha hn,gappedCompletion_avoids A hc s hs he,?_⟩
  intro i j
  have hi : Fin.castLE le_rfl i = i := Fin.ext rfl
  rw [hi]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp [gappedCompletion,balancedAssembly,j.isLt]
  · simp only [gappedCompletion,balancedAssembly,Fin.append_right]
    congr 1
    exact propext (by simp [Fin.ext_iff])

theorem balancedAssembly_suffix_nonempty {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m) (i : Fin n) :
    (∃ j, rowSuffix (balancedAssembly A hc s hs) i j ≠ .zero) ↔ i ∈ s := by
  constructor
  · rintro ⟨j,hj⟩
    have hf : j.val = (gappedColumn A hc s hs i).val := by
      by_contra hf
      simp [rowSuffix,balancedAssembly,hf] at hj
    apply (gappedColumn_lt_iff A hc s hs i).mp
    rw [← hf]
    exact j.isLt
  · intro hi
    have hlt := (gappedColumn_lt_iff A hc s hs i).mpr hi
    exact ⟨⟨(gappedColumn A hc s hs i).val,hlt⟩,by simp [rowSuffix,balancedAssembly]⟩

theorem balancedAssembly_suffixSupport {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m) :
    rowSupport (rowSuffix (balancedAssembly A hc s hs)) = s := by
  ext i
  rw [mem_rowSupport,balancedAssembly_suffix_nonempty]

theorem balancedAssembly_row_suffix {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m) (i : Fin n) :
    nonzeroEntries (row (balancedAssembly A hc s hs) (i.natAdd r)) = [] ∨
    nonzeroEntries (row (balancedAssembly A hc s hs) (i.natAdd r)) = [.plus] := by
  classical
  by_cases hi : i ∈ s
  · right
    have hlt := (gappedColumn_lt_iff A hc s hs i).mpr hi
    have hf : balancedAssembly A hc s hs (i.natAdd r) =
        fun j => if j = (⟨(gappedColumn A hc s hs i).val,hlt⟩ : Fin (r+m)) then Entry.plus else .zero := by
      funext j
      simp [balancedAssembly,Fin.ext_iff]
    rw [row,hf]
    exact nonzero_ofFn_single _
  · left
    have hf : balancedAssembly A hc s hs (i.natAdd r) = fun _ => Entry.zero := by
      funext j
      by_contra h
      exact hi ((balancedAssembly_suffix_nonempty A hc s hs i).mp ⟨j,h⟩)
    rw [row,hf]
    exact nonzero_ofFn_zero _

theorem balancedAssembly_asr {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (ha : IsASR A) (hn : nonemptyRows A = r) (he : ExtendablyAvoids312 A) :
    IsASR (balancedAssembly A hc s hs) := by
  apply extendable_asr_of_ends _ (balancedAssembly_extendable A hc s hs ha hn he)
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simpa only [row,balancedAssembly,Fin.append_left] using (ha.1 i).2.2
  · rcases balancedAssembly_row_suffix A hc s hs i with h | h <;> simp [EndsPositive,h]

theorem balancedAssembly_nonemptyRows {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin n)) (hs : s.card = m)
    (hn : nonemptyRows A = r) : nonemptyRows (balancedAssembly A hc s hs) = r+m := by
  rw [rowSlices_nonemptyRows,balancedAssembly_prefix,hn,← rowSupport_card,balancedAssembly_suffixSupport,hs]

theorem balancedAssembly_emptyRow {r m n : ℕ} (A : Rectangle r (r+m))
    (hc : (zeroSumColumns A).card = m) (s : Finset (Fin (n+1))) (hs : s.card = m)
    (hz : (0 : Fin (n+1)) ∉ s) (j : Fin (r+m)) :
    balancedAssembly A hc s hs ((0 : Fin (n+1)).natAdd r) j = .zero := by
  by_contra h
  exact hz ((balancedAssembly_suffix_nonempty A hc s hs 0).mp ⟨j,h⟩)

end ASR312
