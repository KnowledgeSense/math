import ASR312.EmptyFirstRow
import Mathlib.Data.Finset.Sort

namespace ASR312

 def permutationMatrix {n : ℕ} (σ : Equiv.Perm (Fin n)) : Rectangle n n :=
    fun i j => if j = σ i then .plus else .zero

 theorem permutationMatrix_plus_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permutationMatrix σ i j = .plus ↔ j = σ i := by simp [permutationMatrix]

 theorem permutationMatrix_row {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    nonzeroEntries (row (permutationMatrix σ) i) = [.plus] :=
  nonzero_ofFn_single (σ i)

 theorem permutationMatrix_col {n : ℕ} (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    nonzeroEntries (col (permutationMatrix σ) j) = [.plus] := by
  have hf : (fun i => permutationMatrix σ i j) =
      (fun i => if i = σ.symm j then Entry.plus else .zero) := by
    funext i
    have hh : j = σ i ↔ i = σ.symm j := by
      constructor
      · intro h; subst j; simp
      · intro h; subst i; simp
    simp only [permutationMatrix,hh]
  rw [col,hf]
  exact nonzero_ofFn_single _

 theorem permutationMatrix_asm {n : ℕ} (σ : Equiv.Perm (Fin n)) : IsASM (permutationMatrix σ) := by
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro i; simp [Alternates,StartsPositive,EndsPositive,permutationMatrix_row]
  · intro j; simp [Alternates,StartsPositive,permutationMatrix_col]
  · intro i; exact ⟨σ i,by simp [permutationMatrix]⟩
  · intro j; exact ⟨⟨σ.symm j,by simp [permutationMatrix]⟩,by simp [EndsPositive,permutationMatrix_col]⟩

 theorem permutationMatrix_avoids_of_split {n k : ℕ} (σ : Equiv.Perm (Fin n))
    (hl : ∀ i j, i < j → (σ i).val < k → (σ j).val < k → σ j < σ i)
    (hu : ∀ i j, i < j → k ≤ (σ i).val → k ≤ (σ j).val → σ i < σ j) :
    Avoids312 (permutationMatrix σ) := by
  rintro ⟨i₁,i₂,i₃,j₁,j₂,j₃,h12,h23,hj12,hj23,h13,h21,h32⟩
  rw [permutationMatrix_plus_iff] at h13 h21 h32
  subst j₁; subst j₂; subst j₃
  by_cases hh : (σ i₃).val < k
  · have h2 : (σ i₂).val < k := by change (σ i₂).val < (σ i₃).val at hj12; omega
    exact (not_lt_of_ge (le_of_lt (hl i₂ i₃ h23 h2 hh))) hj12
  · have h1 : k ≤ (σ i₁).val := by change (σ i₃).val < (σ i₁).val at hj23; omega
    exact (not_lt_of_ge (le_of_lt (hu i₁ i₃ (lt_trans h12 h23) h1 (by omega)))) hj23

end ASR312
