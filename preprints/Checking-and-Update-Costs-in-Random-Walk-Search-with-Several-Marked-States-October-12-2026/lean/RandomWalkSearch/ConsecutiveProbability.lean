import RandomWalkSearch.TapeLaw
import RandomWalkSearch.Restoration

/-! # Integration of the actual consecutive-trajectory lower bound -/
namespace RandomWalkSearch.Cycle
open MeasureTheory
open scoped ENNReal BigOperators
variable {k : ℕ} [NeZero (N k)]
variable {Ω : Type*} [MeasurableSpace Ω]

def Randomized.Consecutive (A : Randomized k Ω) (b : ℕ) : Prop :=
  ∀ ω, RandomWalkSearch.Consecutive oracle b (A.policy ω) (A.tapes ω)

omit [NeZero (N k)] [MeasurableSpace Ω] in
theorem Randomized.Consecutive.restoration {A : Randomized k Ω} {b : ℕ}
    (hA : A.Consecutive b) : A.Restoration b := fun ω => (hA ω).1

omit [NeZero (N k)] [MeasurableSpace Ω] in
theorem Randomized.consecutive_truncate (A : Randomized k Ω) (b : ℕ)
    (hA : A.Consecutive b) (T Q : ℕ∞) : (A.truncate T Q).Consecutive b := by
  intro ω
  refine ⟨A.restoration_truncate b hA.restoration T Q ω, ?_⟩
  intro a n hn
  exact truncate_operation_safe T Q (A.policy ω) (A.tapes ω) (oracle a)
    Extends (fun _ => trivial) ((hA ω).2 a) n hn

omit [MeasurableSpace Ω] in
theorem genuine_hard_consecutive_count (b T Q : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4)
    (hp : RandomWalkSearch.Consecutive oracle b p (lazyTapes z w))
    (hbud : ∀ a n, Within (T : ℕ∞) (Q : ℕ∞) (run p (lazyTapes z w) (oracle a) n)) :
    (successfulTranslates p (lazyTapes z w)).card ≤
      (Q + 1) * k ^ 6 + (b + 1) * D k + rangeSum b T w := by
  have heq : successfulTranslates p (lazyTapes z w) =
      successfulTranslates (complete oracle p) (lazyTapes z w) := by
    ext a
    simp only [mem_successfulTranslates, complete_succeeds_iff]
  rw [heq]
  apply hard_consecutive_count b T Q (complete oracle p) z w
  · exact complete_local oracle b p (lazyTapes z w) hp.1 negativeOracle
  · exact complete_extends oracle b p (lazyTapes z w) hp negativeOracle
  · exact run_setup_le b _ _ negativeOracle
      (complete_setupBound oracle b p (lazyTapes z w) hp.1 negativeOracle)
  · intro n
    have h := (complete_within oracle T Q p (lazyTapes z w) hbud negativeOracle n).1
    exact_mod_cast h
  · intro n
    have h := (complete_within oracle T Q p (lazyTapes z w) hbud negativeOracle n).2
    exact_mod_cast h

omit [MeasurableSpace Ω] in
theorem Randomized.truncated_consecutive_score_bound (A : Randomized k Ω) (b T Q : ℕ)
    (hA : A.Consecutive b) (ω : Ω) :
    (∑ a : Vertex k, successScore ((A.truncate T Q).policy ω) (A.tapes ω) (oracle a)) ≤
      (((Q + 1) * k ^ 6 + (b + 1) * D k : ℕ) : ℝ≥0∞) + rangeSum b T (A.increments ω) := by
  rw [sum_successScore_eq_card]
  exact_mod_cast genuine_hard_consecutive_count b T Q
    ((A.truncate T Q).policy ω) (A.setups ω) (A.increments ω)
    (A.consecutive_truncate b hA T Q ω)
    (fun a n => truncate_within T Q (A.policy ω) (A.tapes ω) (oracle a) n)

/-- The consecutive hard-to-expected budget transition, with the range estimate
proved from the iid increment law rather than supplied as a hypothesis. -/
theorem Randomized.expected_consecutive_budget (A : Randomized k Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hobs : A.Observable) (hlaw : A.LazyLaw μ)
    (b T Q : ℕ) (hA : A.Consecutive b) (hT : 0 < T) (hQ : 0 < Q) :
    A.averageSuccess μ ≤
      (((Q + 1) * k ^ 6 + (b + 1) * D k : ℕ) : ℝ≥0∞) / N k +
      (b : ℝ≥0∞) * ENNReal.ofReal (2 * Real.sqrt (2 * (T : ℝ))) / N k +
      A.averageUpdates μ / T + A.averageChecks μ / Q := by
  classical
  let H : ℝ≥0∞ := ((Q + 1) * k ^ 6 + (b + 1) * D k : ℕ)
  have hpoint (ω : Ω) :
      (∑ a : Vertex k, successScore (A.policy ω) (A.tapes ω) (oracle a)) ≤
        H + rangeSum b T (A.increments ω) +
        (∑ a : Vertex k, updatesENN (A.policy ω) (A.tapes ω) (oracle a)) / T +
        (∑ a : Vertex k, checksENN (A.policy ω) (A.tapes ω) (oracle a)) / Q := by
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Vertex k)))
      (fun a _ => successScore_truncate_le T Q hT hQ (A.policy ω) (A.tapes ω) (oracle a))
    simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul] at hs ⊢
    exact hs.trans (add_le_add (add_le_add
      (A.truncated_consecutive_score_bound b T Q hA ω) le_rfl) le_rfl)
  have hi := lintegral_mono hpoint (μ := μ)
  have hmu : Measurable fun ω => ∑ a : Vertex k, updatesENN (A.policy ω) (A.tapes ω) (oracle a) :=
    Finset.measurable_sum _ (fun a _ => hobs.updates a)
  have hmc : Measurable fun ω => ∑ a : Vertex k, checksENN (A.policy ω) (A.tapes ω) (oracle a) :=
    Finset.measurable_sum _ (fun a _ => hobs.checks a)
  simp only [div_eq_mul_inv] at hi
  rw [lintegral_finsetSum _ (fun a _ => hobs.success a),
    lintegral_add_right _ (hmc.mul_const _), lintegral_add_right _ (hmu.mul_const _),
    lintegral_add_right _ (A.measurable_rangeSum μ hlaw b T), lintegral_const,
    measure_univ, mul_one,
    lintegral_mul_const _ hmu, lintegral_mul_const _ hmc,
    lintegral_finsetSum _ (fun a _ => hobs.updates a),
    lintegral_finsetSum _ (fun a _ => hobs.checks a)] at hi
  have hi' := hi.trans (add_le_add (add_le_add
    (add_le_add le_rfl (A.lintegral_rangeSum μ hlaw b T)) le_rfl) le_rfl)
  have hr := mul_le_mul hi' (le_rfl : (N k : ℝ≥0∞)⁻¹ ≤ (N k : ℝ≥0∞)⁻¹)
  simpa [Randomized.averageSuccess, Randomized.success, Randomized.averageUpdates,
    Randomized.averageChecks, H, div_eq_mul_inv, add_mul, mul_add, mul_assoc,
    mul_left_comm, mul_comm] using hr

end RandomWalkSearch.Cycle
