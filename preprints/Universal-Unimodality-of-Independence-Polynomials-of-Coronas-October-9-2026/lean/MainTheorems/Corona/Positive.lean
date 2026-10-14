import MainTheorems.Corona.Counting
import MainTheorems.Corona.SymmetricPowers

namespace ResearchMain.Corona

open Classical Polynomial

theorem UnimodalAt.finset_sum {ι : Type} (S : Finset ι) {f : ι → ℕ → ℝ} {m : ℕ}
    (hf : ∀ i ∈ S, UnimodalAt (f i) m) : UnimodalAt (fun k => ∑ i ∈ S, f i k) m := by
  exact ⟨fun k hk => Finset.sum_le_sum (fun i hi => (hf i hi).1 k hk),
    fun k hk => Finset.sum_le_sum (fun i hi => (hf i hi).2 k hk)⟩

theorem corona_unimodal_of_polynomial {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    {r : ℝ} (hr : 1 ≤ r) (hH : independencePolynomial H = symmetricQuadratic r) :
    UnimodalAt (fun k => (independencePolynomial (corona G H)).coeff k) (Fintype.card V) := by
  have hf : ∀ S ∈ independentSets G,
      UnimodalAt (fun k => (X ^ S.card * symmetricQuadratic r ^
        (Fintype.card V - S.card)).coeff k) (Fintype.card V) := by
    intro S _
    exact symmetricQuadratic_shift_unimodal hr (Finset.card_le_univ S)
  have h := UnimodalAt.finset_sum (independentSets G) hf
  simpa only [independencePolynomial_corona, hH, finsetSum_coeff] using h

theorem corona_counts_unimodal_of_polynomial {V W : Type} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W)
    {r : ℝ} (hr : 1 ≤ r) (hH : independencePolynomial H = symmetricQuadratic r) :
    UnimodalAt (fun k => (independentCount (corona G H) k : ℝ)) (Fintype.card V) := by
  simpa only [independencePolynomial_coeff] using corona_unimodal_of_polynomial G H hr hH

end ResearchMain.Corona
