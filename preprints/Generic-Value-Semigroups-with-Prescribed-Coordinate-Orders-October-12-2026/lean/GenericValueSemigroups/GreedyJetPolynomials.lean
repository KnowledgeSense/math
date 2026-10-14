import GenericValueSemigroups.GenericConditions
import GenericValueSemigroups.GenericJets
import GenericValueSemigroups.OrderedWeights

namespace GenericValueSemigroups

noncomputable def greedyJetPolynomial {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) (N q : ℕ)
    (hq : q ≤ greedyPrefixCount (weightAt r hr hd) (weightCount r N) N) :
    MvPolynomial (JetVariable d N) ℤ :=
  jetMinorPolynomial r N
    (fun j : Fin q => (orderedWeightEquiv r hr N
      ⟨j.val, lt_of_lt_of_le j.isLt (hq.trans (greedyPrefixCount_le _ _ _))⟩).val)
    (fun j : Fin q => ⟨greedy (weightAt r hr hd) j.val,
      greedy_lt_of_lt_prefixCount _ _ _ _ (lt_of_lt_of_le j.isLt hq)⟩)

theorem greedyJetPolynomial_ne_zero {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) (N q : ℕ)
    (hq : q ≤ greedyPrefixCount (weightAt r hr hd) (weightCount r N) N) :
    greedyJetPolynomial r hr hd N q hq ≠ 0 := by
  cases q with
  | zero => simp [greedyJetPolynomial, jetMinorPolynomial]
  | succ q =>
    let w := weightAt r hr hd
    let emb : Fin (q+1) → Fin (weightCount r N) :=
      fun j => ⟨j.val, lt_of_lt_of_le j.isLt (hq.trans (greedyPrefixCount_le _ _ _))⟩
    let α : Fin (q+1) → Fin d → ℕ := fun j => (orderedWeightEquiv r hr N (emb j)).val
    let rows : Fin (q+1) → Fin N := fun j => ⟨greedy w j.val,
      greedy_lt_of_lt_prefixCount _ _ _ _ (lt_of_lt_of_le j.isLt hq)⟩
    let shifts : Fin (q+1) → Fin N := fun j => ⟨w j.val,
      lt_of_le_of_lt (weight_le_greedy w j.val) (rows j).isLt⟩
    have hEmb : StrictMono emb := fun _ _ h => h
    have hw (j : Fin (q+1)) : ∑ i, α j i*r i = (shifts j).val :=
      orderedWeightEquiv_weight r hr hd N (emb j)
    change jetMinorPolynomial r N α rows ≠ 0
    apply jetMinorPolynomial_ne_zero r (orderedWeightCoefficient r N) α shifts rows hw
    · intro i j hij
      exact weightAt_mono r hr hd hij
    · exact (orderedWeightNode_strictMono r hr N).comp hEmb
    · exact orderedWeightNode_zero r hr hd N (emb 0) rfl
    · intro i j hij
      exact greedy_strictMono w hij
    · apply Fin.ext
      rfl
    · intro j
      exact weight_le_greedy w j.val

theorem greedyJetPolynomial_eval {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (hr : ∀ i, 0 < r i) (hd : 0 < d)
    (hf : ∀ i, PowerSeries.order (f i)=r i)
    (hlead : ∀ i, PowerSeries.coeff (r i) (f i)=1) (N q : ℕ)
    (hq : q ≤ greedyPrefixCount (weightAt r hr hd) (weightCount r N) N) :
    jetEvaluation (jetAssignment f r N) (greedyJetPolynomial r hr hd N q hq) =
      (greedyMinor (orderedMonomialFamily f r N (orderedWeightEquiv r hr N))
        (weightAt r hr hd) q (hq.trans (greedyPrefixCount_le _ _ _))).det := by
  unfold greedyJetPolynomial
  rw [jetMinorPolynomial_eval _ r N (fun i n hn => ?_) hlead]
  · rfl
  · apply PowerSeries.coeff_of_lt_order
    rw [hf]
    exact_mod_cast hn

end GenericValueSemigroups
