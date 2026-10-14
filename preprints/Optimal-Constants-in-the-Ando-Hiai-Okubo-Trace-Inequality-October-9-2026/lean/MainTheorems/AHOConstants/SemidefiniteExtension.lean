import MainTheorems.AHOConstants.TraceWords
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed

namespace ResearchMain.AHOConstants

open Filter
open scoped Topology ComplexOrder MatrixOrder Matrix.Norms.L2Operator NNReal

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem spectralPower_continuousOn_nonnegative {r : ℝ} (hr : 0 ≤ r) :
    ContinuousOn (fun A : Matrix I I ℂ => spectralPower A r) {A | A.PosSemidef} := by
  by_cases hz : r = 0
  · subst r
    apply continuousOn_const.congr
    intro A hA
    exact spectralPower_zero A hA
  · let s : ℝ≥0 := ⟨r, hr⟩
    have hs : 0 < s := by exact_mod_cast lt_of_le_of_ne hr (Ne.symm hz)
    have h := CFC.continuousOn_nnrpow (A := Matrix I I ℂ) s
    have h' : ContinuousOn (fun A : Matrix I I ℂ => A ^ s) {A | A.PosSemidef} := by
      simpa only [Matrix.nonneg_iff_posSemidef] using h
    apply h'.congr
    intro A hA
    exact (CFC.nnrpow_eq_rpow (a := A) hs).symm

theorem spectralPower_tendsto_nonnegative {X : Type*} {l : Filter X}
    {As : X → Matrix I I ℂ} {A : Matrix I I ℂ} {r : ℝ}
    (hr : 0 ≤ r) (hA : A.PosSemidef) (hAs : ∀ᶠ x in l, (As x).PosSemidef)
    (hlim : Tendsto As l (𝓝 A)) :
    Tendsto (fun x => spectralPower (As x) r) l (𝓝 (spectralPower A r)) := by
  apply (spectralPower_continuousOn_nonnegative hr).continuousWithinAt hA |>.tendsto.comp
  rw [tendsto_nhdsWithin_iff]
  exact ⟨hlim, hAs⟩

noncomputable def regularized (A : Matrix I I ℂ) (j : ℕ) : Matrix I I ℂ :=
  A + (1 / ((j : ℝ) + 1)) • (1 : Matrix I I ℂ)

omit [Fintype I] in
theorem regularized_posDef {A : Matrix I I ℂ} (hA : A.PosSemidef) (j : ℕ) :
    (regularized A j).PosDef := by
  apply Matrix.PosDef.posSemidef_add hA
  exact (Matrix.PosDef.one (n := I) (R := ℂ)).smul (by positivity)

omit [Fintype I] in
theorem regularized_tendsto (A : Matrix I I ℂ) :
    Tendsto (regularized A) atTop (𝓝 A) := by
  have hρ : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  change Tendsto (fun j : ℕ => A + (1 / ((j : ℝ) + 1)) • (1 : Matrix I I ℂ)) atTop (𝓝 A)
  simpa only [zero_smul, add_zero] using
    (tendsto_const_nhds (x := A)).add (hρ.smul_const (1 : Matrix I I ℂ))

theorem matrixWord_regularized_tendsto {A B : Matrix I I ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (w : TraceWord)
    (hw : ∀ cr ∈ w, 0 ≤ cr.2) :
    Tendsto (fun j => matrixWord (regularized A j) (regularized B j) w) atTop
      (𝓝 (matrixWord A B w)) := by
  revert hw
  induction w with
  | nil => intro _; exact tendsto_const_nhds
  | cons cr w ih =>
    intro hw
    have ht := ih (fun d hd => hw d (by simp [hd]))
    have he : Tendsto (fun j => spectralPower
        (if cr.1 then regularized A j else regularized B j) cr.2) atTop
        (𝓝 (spectralPower (if cr.1 then A else B) cr.2)) := by
      cases hc : cr.1
      · simp only [Bool.false_eq_true, ite_false]
        exact spectralPower_tendsto_nonnegative (hw cr (by simp)) hB
          (Eventually.of_forall (fun j => (regularized_posDef hB j).posSemidef))
          (regularized_tendsto B)
      · simp only [ite_true]
        exact spectralPower_tendsto_nonnegative (hw cr (by simp)) hA
          (Eventually.of_forall (fun j => (regularized_posDef hA j).posSemidef))
          (regularized_tendsto A)
    exact he.mul ht

theorem extend_trace_bound_to_semidefinite {w : TraceWord}
    (hw : ∀ cr ∈ w, 0 ≤ cr.2)
    (hbound : ∀ {A B : Matrix I I ℂ}, A.PosDef → B.PosDef →
      ‖wordTrace A B w‖ ≤ (Matrix.trace (A * B)).re)
    {A B : Matrix I I ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ‖wordTrace A B w‖ ≤ (Matrix.trace (A * B)).re := by
  let T : Matrix I I ℂ →L[ℂ] ℂ :=
    (Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap
  have hleft := (T.continuous.tendsto (matrixWord A B w)).comp
    (matrixWord_regularized_tendsto hA hB w hw)
  have hright := (T.continuous.tendsto (A * B)).comp
    ((regularized_tendsto A).mul (regularized_tendsto B))
  exact le_of_tendsto_of_tendsto hleft.norm
    (Complex.continuous_re.tendsto _ |>.comp hright)
    (Eventually.of_forall (fun j => hbound (regularized_posDef hA j) (regularized_posDef hB j)))

end ResearchMain.AHOConstants
