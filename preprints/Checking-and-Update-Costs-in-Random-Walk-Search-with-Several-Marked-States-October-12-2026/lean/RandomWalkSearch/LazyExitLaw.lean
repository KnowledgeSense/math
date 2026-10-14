import RandomWalkSearch.LazyExit
import RandomWalkSearch.TapeLaw
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Exact expectation and almost-sure finiteness of the genuine lazy exit time. -/
noncomputable section
namespace RandomWalkSearch.LazyWalk
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

/-- The actual stopping time as an extended nonnegative real, obtained from
its genuinely executed truncated counters. -/
def exitENN (r : ℕ) (w : ℕ → Fin 4) : ℝ≥0∞ :=
  ⨆ n, ((exitRun r n (prefixTape n w)).elapsed : ℝ≥0∞)

theorem elapsed_monotone (r : ℕ) (w : ℕ → Fin 4) :
    Monotone (fun n => (exitRun r n (prefixTape n w)).elapsed) := by
  apply monotone_nat_of_le_succ
  intro n
  change (exitRun r n (prefixTape n w)).elapsed ≤
    (exitAdvance r (exitRun r n (prefixTape n w)) (w n)).elapsed
  unfold exitAdvance
  split
  · exact Nat.le_succ _
  · exact le_rfl

theorem exitENN_at_first {r t : ℕ} (w : ℕ → Fin 4)
    (hb : |integerWalk w t| = (r : ℤ))
    (hbefore : ∀ j < t, |integerWalk w j| < (r : ℤ)) : exitENN r w = t := by
  unfold exitENN
  simp only [exitRun_at_first w hb hbefore]
  apply le_antisymm
  · exact iSup_le (fun n => by exact_mod_cast (Nat.min_le_right n t))
  · have h := le_iSup (fun n : ℕ => ((min n t : ℕ) : ℝ≥0∞)) t
    simpa only [min_self] using h

theorem exitENN_of_no_exit (r : ℕ) (w : ℕ → Fin 4)
    (h : ¬∃ n, (r : ℤ) ≤ |integerWalk w n|) : exitENN r w = ⊤ := by
  have hh (j : ℕ) : |integerWalk w j| < (r : ℤ) := lt_of_not_ge (fun hj => h ⟨j, hj⟩)
  unfold exitENN
  simp only [exitRun_before r _ w (fun j _ => hh j), ENNReal.iSup_natCast]

theorem exitENN_lt_top_iff (r : ℕ) (w : ℕ → Fin 4) :
    exitENN r w < ⊤ ↔ ∃ n, |integerWalk w n| = (r : ℤ) := by
  by_cases h : ∃ n, (r : ℤ) ≤ |integerWalk w n|
  · rw [exitENN_at_first w (first_exit_boundary h)
      (fun j hj => lt_of_not_ge (Nat.find_min h hj))]
    exact ⟨fun _ => ⟨Nat.find h, first_exit_boundary h⟩, fun _ => ENNReal.natCast_lt_top _⟩
  · rw [exitENN_of_no_exit r w h]
    constructor
    · intro hn
      exact False.elim (lt_irrefl _ hn)
    · rintro ⟨n, hn⟩
      exact False.elim (h ⟨n, le_of_eq hn.symm⟩)

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The canonical iid law is a statement only about actual finite-prefix cylinders. -/
def IID (μ : Measure Ω) (w : Ω → ℕ → Fin 4) : Prop :=
  ∀ n (t : Tape n), MeasurableSet {ω | prefixTape n (w ω) = t} ∧
    μ {ω | prefixTape n (w ω) = t} = (Fintype.card (Tape n) : ℝ≥0∞)⁻¹

theorem measurable_finite_prefix (μ : Measure Ω) (w : Ω → ℕ → Fin 4)
    (hlaw : IID μ w) (n : ℕ) (g : Tape n → ℝ≥0∞) :
    Measurable (fun ω => g (prefixTape n (w ω))) := by
  classical
  have hrep : (fun ω => g (prefixTape n (w ω))) =
      fun ω => ∑ t : Tape n, Set.indicator {ω | prefixTape n (w ω) = t} (fun _ => g t) ω := by
    funext ω
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [Finset.sum_eq_single (prefixTape n (w ω))]
    · simp
    · intro t _ ht
      simp [Ne.symm ht]
    · simp
  rw [hrep]
  exact Finset.measurable_sum _ (fun t _ => measurable_const.indicator (hlaw n t).1)

theorem measurable_exitENN (μ : Measure Ω) (w : Ω → ℕ → Fin 4) (hlaw : IID μ w) (r : ℕ) :
    Measurable (fun ω => exitENN r (w ω)) := by
  apply Measurable.iSup
  intro n
  exact measurable_finite_prefix μ w hlaw n (fun t => ((exitRun r n t).elapsed : ℝ≥0∞))

theorem lintegral_truncatedExit (μ : Measure Ω) (w : Ω → ℕ → Fin 4)
    (hlaw : IID μ w) (r n : ℕ) :
    (∫⁻ ω, ((exitRun r n (prefixTape n (w ω))).elapsed : ℝ≥0∞) ∂μ) =
      ENNReal.ofReal (truncatedExit r n) :=
  lintegral_uniform_nat μ (fun ω => prefixTape n (w ω))
    (fun t => (hlaw n t).1) (fun t => (hlaw n t).2) (fun t => (exitRun r n t).elapsed)

/-- Exact expectation of the genuine first boundary-hitting time. -/
theorem lintegral_exitENN (μ : Measure Ω) (w : Ω → ℕ → Fin 4)
    (hlaw : IID μ w) (r : ℕ) :
    (∫⁻ ω, exitENN r (w ω) ∂μ) = ENNReal.ofReal (2 * (r : ℝ) ^ 2) := by
  have hm : Monotone (fun n ω => ((exitRun r n (prefixTape n (w ω))).elapsed : ℝ≥0∞)) := by
    intro n m hnm ω
    change ((exitRun r n (prefixTape n (w ω))).elapsed : ℝ≥0∞) ≤
      ((exitRun r m (prefixTape m (w ω))).elapsed : ℝ≥0∞)
    exact_mod_cast elapsed_monotone r (w ω) hnm
  unfold exitENN
  rw [lintegral_iSup (fun n => measurable_finite_prefix μ w hlaw n
    (fun t => ((exitRun r n t).elapsed : ℝ≥0∞))) hm]
  simp_rw [lintegral_truncatedExit μ w hlaw r]
  have hmono : Monotone (fun n => ENNReal.ofReal (truncatedExit r n)) := by
    intro n m hnm
    change ENNReal.ofReal (truncatedExit r n) ≤ ENNReal.ofReal (truncatedExit r m)
    rw [← lintegral_truncatedExit μ w hlaw r n, ← lintegral_truncatedExit μ w hlaw r m]
    exact lintegral_mono (hm hnm)
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono)
    (ENNReal.tendsto_ofReal (truncatedExit_tendsto r))

/-- An actual finite boundary hit occurs almost surely; finiteness is derived
from the expectation calculation rather than assumed as a Markov-chain premise. -/
theorem ae_exit_finite (μ : Measure Ω) (w : Ω → ℕ → Fin 4)
    (hlaw : IID μ w) (r : ℕ) : ∀ᵐ ω ∂μ, ∃ n, |integerWalk (w ω) n| = (r : ℤ) := by
  have h := ae_lt_top (measurable_exitENN μ w hlaw r)
    (show (∫⁻ ω, exitENN r (w ω) ∂μ) ≠ ⊤ by rw [lintegral_exitENN μ w hlaw r]; exact ENNReal.ofReal_ne_top)
  exact h.mono (fun ω hω => (exitENN_lt_top_iff r (w ω)).mp hω)

end RandomWalkSearch.LazyWalk
