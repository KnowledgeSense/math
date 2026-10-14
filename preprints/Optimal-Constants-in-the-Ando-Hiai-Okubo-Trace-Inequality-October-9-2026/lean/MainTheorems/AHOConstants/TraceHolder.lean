import MainTheorems.AHOConstants.FactorInterpolation

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]

theorem weighted_positive_trace_bound_aux (n : ℕ) :
    ∀ (fs : List (WeightedFactor I)), fs.length ≤ n →
    (∀ f ∈ fs, 0 < f.weight) → totalWeight fs = 1 →
    ∀ (L : Matrix I I ℂ), L ∈ unitary (Matrix I I ℂ) →
      ‖Matrix.trace (L * weightedProduct fs)‖ ≤ weightedBound fs := by
  induction n with
  | zero =>
    intro fs hlen hpos hsum L hL
    have he : fs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst fs
    norm_num [totalWeight] at hsum
  | succ n ih =>
    intro fs hlen hpos hsum L hL
    cases fs with
    | nil => norm_num [totalWeight] at hsum
    | cons f fs =>
      cases fs with
      | nil =>
        have hw : f.weight = 1 := by simpa only [totalWeight, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, add_zero] using hsum
        have h := unitary_positive_trace_bound
          ((unitary (Matrix I I ℂ)).mul_mem hL f.unitaryMembership)
          f.positiveDefinite.posSemidef
        simpa only [weightedProduct, weightedBound, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, Matrix.mul_one, factorValue, factorBound,
          hw, spectralPower_one _ f.positiveDefinite.posSemidef, Real.rpow_one,
          Matrix.mul_assoc, mul_one] using h
      | cons g fs =>
        let tail := g :: fs
        let θ := totalWeight tail
        have htail : ∀ a ∈ tail, 0 < a.weight := fun a ha => hpos a (by simp [tail, ha])
        have hθ : 0 < θ := totalWeight_pos htail (by simp [tail])
        have hw : f.weight = 1 - θ := by
          rw [totalWeight_cons] at hsum
          dsimp [θ, tail]
          linarith
        have hθ₁ : θ ≤ 1 := by have hf := hpos f (by simp); linarith
        have hweights : ∀ a ∈ tail, 0 ≤ a.weight ∧ a.weight ≤ θ := by
          intro a ha
          exact ⟨(htail a ha).le, weight_le_total (fun b hb => (htail b hb).le) ha⟩
        have htailLen : tail.length ≤ n := by
          simpa only [tail, List.length_cons, Nat.succ_le_succ_iff] using hlen
        let Q := weightedBound (tail.map (normalizedFactor θ 0))
        have hzero : ∀ z : ℂ, z.re = 0 →
            ‖factorInterpolant θ L f tail z‖ ≤ (Matrix.trace f.positiveMatrix).re :=
          fun z hz => factorInterpolant_zero_boundary hL f tail hz
        have hone : ∀ z : ℂ, z.re = 1 →
            ‖factorInterpolant θ L f tail z‖ ≤ Q := by
          intro z hz
          let V := complexPower f.positiveDefinite (1 - z)
          have hr : (1 - z).re = 0 := by simp [hz]
          have hV : V ∈ unitary (Matrix I I ℂ) := by
            dsimp [V]
            rw [complexPower_vertical_line, hr,
              spectralPower_zero _ f.positiveDefinite.posSemidef, Matrix.one_mul]
            exact complexPower_imaginary_unitary f.positiveDefinite _
          have hlead : L * f.unitaryMatrix * V ∈ unitary (Matrix I I ℂ) :=
            (unitary (Matrix I I ℂ)).mul_mem
              ((unitary (Matrix I I ℂ)).mul_mem hL f.unitaryMembership) hV
          have hnormpos : ∀ a ∈ tail.map (normalizedFactor θ z), 0 < a.weight := by
            intro a ha
            obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
            exact div_pos (htail b hb) hθ
          have hnormsum : totalWeight (tail.map (normalizedFactor θ z)) = 1 := by
            rw [normalized_totalWeight]
            exact div_self hθ.ne'
          have h := ih (tail.map (normalizedFactor θ z))
            (by simpa only [List.length_map] using htailLen) hnormpos hnormsum
            (L * f.unitaryMatrix * V) hlead
          have hsame : weightedBound (tail.map (normalizedFactor θ z)) = Q := by
            dsimp [Q]
            rw [normalized_weightedBound, normalized_weightedBound]
          rw [hsame] at h
          unfold factorInterpolant
          rw [interpolationTail_one tail hz]
          exact h
        have h := scalar_three_lines (factorInterpolant_differentiable θ L f tail)
          (factorInterpolant_stripBounded hθ L f tail hweights)
          (t := θ) hθ.le hθ₁ hzero hone
        rw [factorInterpolant_real hθ.ne' L f tail hw] at h
        calc
          ‖Matrix.trace (L * weightedProduct (f :: g :: fs))‖ ≤
              (Matrix.trace f.positiveMatrix).re ^ (1 - θ) * Q ^ θ := h
          _ = factorBound f * weightedBound tail := by
            rw [← hw]
            change factorBound f * weightedBound (tail.map (normalizedFactor θ 0)) ^ θ = _
            rw [normalized_bound_power hθ.ne']
          _ = weightedBound (f :: g :: fs) := rfl

theorem weighted_positive_trace_bound (fs : List (WeightedFactor I))
    (hpos : ∀ f ∈ fs, 0 < f.weight) (hsum : totalWeight fs = 1)
    {L : Matrix I I ℂ} (hL : L ∈ unitary (Matrix I I ℂ)) :
    ‖Matrix.trace (L * weightedProduct fs)‖ ≤ weightedBound fs :=
  weighted_positive_trace_bound_aux fs.length fs le_rfl hpos hsum L hL

end ResearchMain.AHOConstants
