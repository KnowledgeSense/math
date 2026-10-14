import ASR312.SubsetPermutation

namespace ASR312

def permutationRestriction {r k n : ℕ} (hr : r ≤ n) (hk : k ≤ n)
    (σ : Equiv.Perm (Fin n)) : Rectangle r k :=
  fun i j => permutationMatrix σ (Fin.castLE hr i) (Fin.castLE hk j)

theorem permutationRestriction_row {r k n : ℕ} (hr : r ≤ n) (hk : k ≤ n)
    (σ : Equiv.Perm (Fin n)) (i : Fin r) :
    nonzeroEntries (row (permutationRestriction hr hk σ) i) = [] ∨
    nonzeroEntries (row (permutationRestriction hr hk σ) i) = [.plus] := by
  by_cases h : (σ (Fin.castLE hr i)).val < k
  · right
    have hf : permutationRestriction hr hk σ i =
        fun j => if j = (⟨(σ (Fin.castLE hr i)).val,h⟩ : Fin k) then Entry.plus else .zero := by
      funext j
      simp only [permutationRestriction,permutationMatrix]
      congr 1
      exact propext (by simp [Fin.ext_iff])
    rw [row,hf]
    exact nonzero_ofFn_single _
  · left
    have hf : permutationRestriction hr hk σ i = fun _ => Entry.zero := by
      funext j
      have hn : Fin.castLE hk j ≠ σ (Fin.castLE hr i) := by
        intro he
        have hv := congrArg Fin.val he
        have hj := j.isLt
        simp only [Fin.val_castLE] at hv
        omega
      simp [permutationRestriction,permutationMatrix,hn]
    rw [row,hf]
    exact nonzero_ofFn_zero _

theorem permutationRestriction_col {r k n : ℕ} (hr : r ≤ n) (hk : k ≤ n)
    (σ : Equiv.Perm (Fin n)) (j : Fin k) :
    nonzeroEntries (col (permutationRestriction hr hk σ) j) = [] ∨
    nonzeroEntries (col (permutationRestriction hr hk σ) j) = [.plus] := by
  have he (i : Fin r) : Fin.castLE hk j = σ (Fin.castLE hr i) ↔
      Fin.castLE hr i = σ.symm (Fin.castLE hk j) := by
    constructor
    · intro h; rw [h]; simp
    · intro h; rw [h]; simp
  by_cases h : (σ.symm (Fin.castLE hk j)).val < r
  · right
    have hf : (fun i => permutationRestriction hr hk σ i j) =
        fun i => if i = (⟨(σ.symm (Fin.castLE hk j)).val,h⟩ : Fin r) then Entry.plus else .zero := by
      funext i
      simp only [permutationRestriction,permutationMatrix,he]
      congr 1
      exact propext (by simp [Fin.ext_iff])
    rw [col,hf]
    exact nonzero_ofFn_single _
  · left
    have hf : (fun i => permutationRestriction hr hk σ i j) = fun _ => Entry.zero := by
      funext i
      have hn : Fin.castLE hr i ≠ σ.symm (Fin.castLE hk j) := by
        intro he
        have hv := congrArg Fin.val he
        have hi := i.isLt
        simp only [Fin.val_castLE] at hv
        omega
      simp [permutationRestriction,permutationMatrix,he,hn]
    rw [col,hf]
    exact nonzero_ofFn_zero _

theorem permutationRestriction_asr {r k n : ℕ} (hr : r ≤ n) (hk : k ≤ n)
    (σ : Equiv.Perm (Fin n)) : IsASR (permutationRestriction hr hk σ) := by
  constructor
  · intro i
    rcases permutationRestriction_row hr hk σ i with h | h <;>
      simp [Alternates,StartsPositive,EndsPositive,h]
  · intro j
    rcases permutationRestriction_col hr hk σ j with h | h <;>
      simp [Alternates,StartsPositive,h]

theorem permutationRestriction_extendable {r k n : ℕ} (hr : r ≤ n) (hk : k ≤ n)
    (σ : Equiv.Perm (Fin n)) (ha : Avoids312 (permutationMatrix σ)) :
    ExtendablyAvoids312 (permutationRestriction hr hk σ) :=
  ⟨n,hr,hk,permutationMatrix σ,permutationMatrix_asm σ,ha,fun _ _ => rfl⟩

theorem permutationRestriction_row_nonempty {r k n : ℕ} (hr : r ≤ n) (hk : k ≤ n)
    (σ : Equiv.Perm (Fin n)) (i : Fin r) :
    (∃ j, permutationRestriction hr hk σ i j ≠ .zero) ↔ (σ (Fin.castLE hr i)).val < k := by
  constructor
  · rintro ⟨j,hj⟩
    have he : Fin.castLE hk j = σ (Fin.castLE hr i) := by
      by_contra hn
      simp [permutationRestriction,permutationMatrix,hn] at hj
    have hv := congrArg Fin.val he
    simp only [Fin.val_castLE] at hv
    rw [← hv]
    exact j.isLt
  · intro h
    refine ⟨⟨(σ (Fin.castLE hr i)).val,h⟩,?_⟩
    have he : Fin.castLE hk ⟨(σ (Fin.castLE hr i)).val,h⟩ = σ (Fin.castLE hr i) := Fin.ext rfl
    simp [permutationRestriction,permutationMatrix,he]

end ASR312
