import Paving.HyperplanePacking
import Paving.LowFlatMobiusSum
import Paving.ComponentMixtures

noncomputable section
open Finset
namespace Paving
variable {α : Type*} [Fintype α]

abbrev StressedIndex (M : Matroid α) := {H : Set α // H ∈ stressedHyperplanes M}
abbrev MixtureIndex (M : Matroid α) := Option (StressedIndex M)

def normalization (M : Matroid α) : ℝ := (M.E.ncard.choose (rank M-1):ℝ)
def hyperplaneWeight (M : Matroid α) (H : StressedIndex M) : ℝ :=
  (H.val.ncard.choose (rank M-1):ℝ)/normalization M

def actualWeight (M : Matroid α) : MixtureIndex M → ℝ
  | none => 1-∑H:StressedIndex M,hyperplaneWeight M H
  | some H => hyperplaneWeight M H

def actualParameter (M : Matroid α) : MixtureIndex M → Option ℕ
  | none => none
  | some H => some H.val.ncard

theorem normalization_positive (M : Matroid α) : 0 < normalization M := by
  unfold normalization
  exact_mod_cast Nat.choose_pos (show rank M-1 ≤ M.E.ncard by have := rank_le_ground_card M; omega)

theorem actualWeight_sum (M : Matroid α) : ∑j:MixtureIndex M,actualWeight M j=1 := by
  simp [Fintype.sum_option,actualWeight]

theorem IsPaving.actualWeight_nonneg {M : Matroid α} (hM : IsPaving M) (hr : 1 ≤ rank M)
    (j : MixtureIndex M) : 0 ≤ actualWeight M j := by
  classical
  cases j with
  | some H => exact div_nonneg (Nat.cast_nonneg _) (normalization_positive M).le
  | none =>
    change 0 ≤ 1-∑H:StressedIndex M,hyperplaneWeight M H
    rw [sub_nonneg]
    simp only [hyperplaneWeight,← sum_div]
    apply (div_le_one (normalization_positive M)).mpr
    have hp := hM.stressedHyperplane_packing hr
    have he : (∑H:StressedIndex M,H.val.ncard.choose (rank M-1))=
        ∑H∈stressedHyperplanes M,H.ncard.choose (rank M-1) := by
      exact Finset.sum_attach (stressedHyperplanes M) (fun H => H.ncard.choose (rank M-1))
    unfold normalization
    exact_mod_cast (he.symm ▸ hp)

theorem actualParameter_valid (M : Matroid α) (j : MixtureIndex M) :
    ValidParameter (rank M) M.E.ncard (actualParameter M j) := by
  cases j with
  | none => trivial
  | some H =>
    have hh := (mem_stressedHyperplanes M H.val).mp H.property
    exact ⟨hh.2,hyperplane_card_lt hh.1⟩

def actualReflectedMixture (M : Matroid α) (i : ℕ) : ℝ :=
  reflectedMixture univ (actualWeight M) (actualParameter M) (rank M) M.E.ncard i

theorem IsPaving.actual_odd_strict {M : Matroid α} (hM : IsPaving M)
    (m : ℕ) (hm : 1 ≤ m) (hr : rank M=2*m+1) :
    ∀i,1 ≤ i → i < rank M → actualReflectedMixture M (i-1)*
      actualReflectedMixture M (i+1) < actualReflectedMixture M i^2 := by
  have hn : 2*m+1 ≤ M.E.ncard := hr ▸ rank_le_ground_card M
  have hw := hM.actualWeight_nonneg (show 1 ≤ rank M by omega)
  have hv := actualParameter_valid M
  have hh := odd_mixture_strict univ (actualWeight M) (actualParameter M) m M.E.ncard hm hn
    (fun j _ => hw j) (actualWeight_sum M) (fun j _ => hr ▸ hv j)
  simpa only [actualReflectedMixture,hr] using hh

end Paving
