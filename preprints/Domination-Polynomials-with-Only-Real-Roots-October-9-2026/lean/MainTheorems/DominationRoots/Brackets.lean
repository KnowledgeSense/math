import MainTheorems.DominationRoots.AuxiliaryDerivatives

namespace ResearchMain.DominationRoots

open Set

structure BracketCertificate (a b : ℝ) : Prop where
  left_nonnegative : 0 ≤ a
  ordered : a ≤ b
  quadratic_side : 3 ≤ 2 * a ∨ 2 * b ≤ 3
  energy_side : 1 ≤ 2 * a ∨ 2 * b ≤ 1
  exponential_bound : bracketBound a b <
    expPartial 19 (min (quadratic 1 (-2) a) (quadratic 1 (-2) b))
  derivative_left : auxiliaryDerivative a < 0
  derivative_right : 0 < auxiliaryDerivative b

theorem auxiliaryFunction_above_on_bracket {a b x : ℝ}
    (hc : BracketCertificate a b) (hx : x ∈ Icc a b) (hreg : Regular x) :
    2 < auxiliaryFunction x := by
  have hq := auxiliaryQ_bracket_bound hc.left_nonnegative hc.quadratic_side hx
  have he := energy_bracket_bound hc.energy_side hx
  have ht := expPartial_nineteen_le
    (min (quadratic 1 (-2) a) (quadratic 1 (-2) b))
  have hExp : |auxiliaryQ x| < Real.exp (quadratic 1 (-2) x) :=
    hq.trans_lt (hc.exponential_bound.trans_le (ht.trans (Real.exp_le_exp.mpr he)))
  have hlog := (Real.log_lt_iff_lt_exp
    (abs_pos.mpr ((regular_iff_auxiliaryQ_ne_zero x).mp hreg))).mpr hExp
  rw [auxiliaryFunction_eq x hreg]
  unfold quadratic at hlog
  linarith

theorem auxiliaryFunction_above_component {S : Set ℝ} (hS : Convex ℝ S)
    (hreg : ∀ x ∈ S, Regular x) {a b : ℝ} (ha : a ∈ S) (hb : b ∈ S)
    (hc : BracketCertificate a b) : ∀ x ∈ S, 2 < auxiliaryFunction x := by
  have hD := (auxiliaryDerivative_strictMonoOn hS hreg).monotoneOn
  intro x hx
  by_cases hxa : x ≤ a
  · have hf : AntitoneOn auxiliaryFunction (Icc x a) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc x a)
      · intro z hz
        exact (auxiliaryFunction_hasDerivAt z (hreg z
          (hS.ordConnected.out hx ha hz))).continuousAt.continuousWithinAt
      · intro z hz
        have hz' := interior_subset hz
        exact (auxiliaryFunction_hasDerivAt z (hreg z
          (hS.ordConnected.out hx ha hz'))).hasDerivWithinAt
      · intro z hz
        have hz' := interior_subset hz
        exact (hD (hS.ordConnected.out hx ha hz') ha hz'.2).trans
          hc.derivative_left.le
    exact (auxiliaryFunction_above_on_bracket hc ⟨le_rfl, hc.ordered⟩
      (hreg a ha)).trans_le (hf ⟨le_rfl, hxa⟩ ⟨hxa, le_rfl⟩ hxa)
  · by_cases hbx : b ≤ x
    · have hf : MonotoneOn auxiliaryFunction (Icc b x) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc b x)
        · intro z hz
          exact (auxiliaryFunction_hasDerivAt z (hreg z
            (hS.ordConnected.out hb hx hz))).continuousAt.continuousWithinAt
        · intro z hz
          have hz' := interior_subset hz
          exact (auxiliaryFunction_hasDerivAt z (hreg z
            (hS.ordConnected.out hb hx hz'))).hasDerivWithinAt
        · intro z hz
          have hz' := interior_subset hz
          exact hc.derivative_right.le.trans
            (hD hb (hS.ordConnected.out hb hx hz') hz'.1)
      exact (auxiliaryFunction_above_on_bracket hc ⟨hc.ordered, le_rfl⟩
        (hreg b hb)).trans_le (hf ⟨le_rfl, hbx⟩ ⟨hbx, le_rfl⟩ hbx)
    · exact auxiliaryFunction_above_on_bracket hc
        ⟨(not_le.mp hxa).le, (not_le.mp hbx).le⟩ (hreg x hx)

noncomputable def bracketLeft : Fin 5 → ℝ :=
  ![1464 / 10000, 5960 / 10000, 15422 / 10000, 22636 / 10000, 30332 / 10000]

noncomputable def bracketRight (i : Fin 5) : ℝ := bracketLeft i + 1 / 10000

theorem bracket_certificates (i : Fin 5) :
    BracketCertificate (bracketLeft i) (bracketRight i) := by
  fin_cases i <;>
    constructor <;>
    norm_num [bracketLeft, bracketRight, bracketBound, quadratic, expPartial,
      Finset.sum_range_succ, auxiliaryDerivative]

end ResearchMain.DominationRoots
