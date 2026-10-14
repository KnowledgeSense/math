import RandomWalkSearch.Counting
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-! # Actual expectations and integration of the transcript bounds

Randomness is an arbitrary probability space. A point chooses a private policy
and its setup/update tapes, all independently of the hidden translate. The
restoration bound is pointwise in these choices; no independence assumption
among their coordinates is needed for this stronger lower bound. Expectations
are of the supremum of actual finite-prefix operation counts, and can be infinite.
-/

namespace RandomWalkSearch

open MeasureTheory
open scoped ENNReal BigOperators

variable {X : Type*}

noncomputable def updatesENN (p : Policy X) (r : Tapes X) (o : Oracle X) : ℝ≥0∞ :=
  ⨆ n, ((run p r o n).updates : ℝ≥0∞)

noncomputable def checksENN (p : Policy X) (r : Tapes X) (o : Oracle X) : ℝ≥0∞ :=
  ⨆ n, ((run p r o n).checks : ℝ≥0∞)

@[simp] theorem updatesENN_le_nat (p : Policy X) (r : Tapes X) (o : Oracle X) (T : ℕ) :
    updatesENN p r o ≤ T ↔ updateCost p r o ≤ T := by
  simp only [updatesENN, updateCost, iSup_le_iff, Nat.cast_le]

@[simp] theorem checksENN_le_nat (p : Policy X) (r : Tapes X) (o : Oracle X) (Q : ℕ) :
    checksENN p r o ≤ Q ↔ checkCost p r o ≤ Q := by
  simp only [checksENN, checkCost, iSup_le_iff, Nat.cast_le]

noncomputable def successScore (p : Policy X) (r : Tapes X) (o : Oracle X) : ℝ≥0∞ := by
  classical
  exact if Succeeds p r o then 1 else 0

theorem successScore_le_one (p : Policy X) (r : Tapes X) (o : Oracle X) :
    successScore p r o ≤ 1 := by
  classical
  unfold successScore
  split <;> simp

/-- Pointwise Markov/truncation inequality on the actual execution. Integrating
it gives the expected-cost truncation lemma, including infinite expectations. -/
theorem successScore_truncate_le (T Q : ℕ) (hT : 0 < T) (hQ : 0 < Q)
    (p : Policy X) (r : Tapes X) (o : Oracle X) :
    successScore p r o ≤ successScore (truncate T Q p) r o +
      updatesENN p r o / T + checksENN p r o / Q := by
  classical
  by_cases hu : updatesENN p r o ≤ T
  · by_cases hc : checksENN p r o ≤ Q
    · have hs : successScore p r o ≤ successScore (truncate T Q p) r o := by
        unfold successScore
        split_ifs with hs ht
        · exact le_rfl
        · exact False.elim (ht (succeeds_truncate_of_cost_le T Q p r o
            ((updatesENN_le_nat ..).mp hu) ((checksENN_le_nat ..).mp hc) hs))
        · exact zero_le
        · exact le_rfl
      exact hs.trans (le_add_of_nonneg_right (by positivity) |>.trans
        (le_add_of_nonneg_right (by positivity)))
    · have h1 : (1 : ℝ≥0∞) ≤ checksENN p r o / Q := by
        apply (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hQ.ne'))
          (Or.inl (ENNReal.natCast_ne_top Q))).mpr
        simpa using (le_of_not_ge hc)
      exact (successScore_le_one ..).trans
        (h1.trans (le_add_of_nonneg_left (by positivity)))
  · have h1 : (1 : ℝ≥0∞) ≤ updatesENN p r o / T := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hT.ne'))
        (Or.inl (ENNReal.natCast_ne_top T))).mpr
      simpa using (le_of_not_ge hu)
    exact (successScore_le_one ..).trans
      (h1.trans ((le_add_of_nonneg_left (by positivity)).trans
        (le_add_of_nonneg_right (by positivity))))

namespace Cycle

variable {k : ℕ} [NeZero (N k)]

theorem sum_successScore_eq_card (p : Policy (Vertex k)) (r : Tapes (Vertex k)) :
    ∑ a : Vertex k, successScore p r (oracle a) = (successfulTranslates p r).card := by
  classical
  simp [successScore, successfulTranslates, Finset.sum_boole]

variable {Ω : Type*} [MeasurableSpace Ω]

/-- An arbitrary randomized history policy with the actual tapes supplied at
that sample point. There is no finite support or finite policy restriction. -/
structure Randomized (k : ℕ) (Ω : Type*) where
  policy : Ω → Policy (Vertex k)
  setups : Ω → ℕ → Vertex k
  increments : Ω → ℕ → ℕ → Fin 4

def Randomized.tapes (A : Randomized k Ω) (ω : Ω) : Tapes (Vertex k) :=
  lazyTapes (A.setups ω) (A.increments ω)

noncomputable def Randomized.success (A : Randomized k Ω) (μ : Measure Ω)
    (a : Vertex k) : ℝ≥0∞ :=
  ∫⁻ ω, successScore (A.policy ω) (A.tapes ω) (oracle a) ∂μ

noncomputable def Randomized.averageSuccess (A : Randomized k Ω) (μ : Measure Ω) : ℝ≥0∞ :=
  (∑ a : Vertex k, A.success μ a) / N k

noncomputable def Randomized.averageUpdates (A : Randomized k Ω) (μ : Measure Ω) : ℝ≥0∞ :=
  (∑ a : Vertex k, ∫⁻ ω, updatesENN (A.policy ω) (A.tapes ω) (oracle a) ∂μ) / N k

noncomputable def Randomized.averageChecks (A : Randomized k Ω) (μ : Measure Ω) : ℝ≥0∞ :=
  (∑ a : Vertex k, ∫⁻ ω, checksENN (A.policy ω) (A.tapes ω) (oracle a) ∂μ) / N k

/-- Measurability concerns only the actual random outcomes, not any inequality
or conclusion of the lower-bound theorem. -/
structure Randomized.Observable (A : Randomized k Ω) : Prop where
  success : ∀ a, Measurable fun ω => successScore (A.policy ω) (A.tapes ω) (oracle a)
  updates : ∀ a, Measurable fun ω => updatesENN (A.policy ω) (A.tapes ω) (oracle a)
  checks : ∀ a, Measurable fun ω => checksENN (A.policy ω) (A.tapes ω) (oracle a)

/-- The access conditions quantify over every translate and every outcome,
including measure-zero tapes and executions that do not halt. -/
def Randomized.Restoration (A : Randomized k Ω) (b : ℕ) : Prop :=
  ∀ ω, RandomWalkSearch.Restoration oracle b (A.policy ω) (A.tapes ω)

/-- Truncation is an actual policy transformation preserving the model. -/
noncomputable def Randomized.truncate (A : Randomized k Ω) (T Q : ℕ∞) : Randomized k Ω where
  policy := fun ω => RandomWalkSearch.truncate T Q (A.policy ω)
  setups := A.setups
  increments := A.increments

omit [NeZero (N k)] [MeasurableSpace Ω] in
theorem Randomized.restoration_truncate (A : Randomized k Ω) (b : ℕ)
    (hA : A.Restoration b) (T Q : ℕ∞) : (A.truncate T Q).Restoration b := by
  intro ω a n hn
  constructor
  · exact truncate_operation_safe T Q (A.policy ω) (A.tapes ω) (oracle a)
      Local (fun _ => trivial) (fun n hn => (hA ω a n hn).1) n hn
  · exact truncate_operation_safe T Q (A.policy ω) (A.tapes ω) (oracle a)
      (SetupBound b) (fun _ => trivial) (fun n hn => (hA ω a n hn).2) n hn

omit [MeasurableSpace Ω] in
/-- The scalar hard budget bound is derived, not a hypothesis on algorithms. -/
theorem Randomized.truncated_score_bound (A : Randomized k Ω) (b T Q : ℕ)
    (hA : A.Restoration b) (ω : Ω) :
    (∑ a : Vertex k, successScore ((A.truncate T Q).policy ω)
      (A.tapes ω) (oracle a)) ≤
      (((Q + 1) * k ^ 6 + (b + 1) * D k + T : ℕ) : ℝ≥0∞) := by
  rw [sum_successScore_eq_card]
  exact_mod_cast genuine_hard_restoration_count b T Q
    ((A.truncate T Q).policy ω) (A.setups ω) (A.increments ω)
    (A.restoration_truncate b hA T Q ω)
    (fun a n => truncate_within T Q (A.policy ω) (A.tapes ω) (oracle a) n)

/-- Integrating genuine costs and the pathwise all-negative coupling gives the
hard-to-expected budget transition for every randomized adaptive policy. -/
theorem Randomized.expected_restoration_budget (A : Randomized k Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hobs : A.Observable)
    (b T Q : ℕ) (hA : A.Restoration b) (hT : 0 < T) (hQ : 0 < Q) :
    A.averageSuccess μ ≤
      (((Q + 1) * k ^ 6 + (b + 1) * D k + T : ℕ) : ℝ≥0∞) / N k +
      A.averageUpdates μ / T + A.averageChecks μ / Q := by
  classical
  let H : ℝ≥0∞ := ((Q + 1) * k ^ 6 + (b + 1) * D k + T : ℕ)
  have hpoint (ω : Ω) :
      (∑ a : Vertex k, successScore (A.policy ω) (A.tapes ω) (oracle a)) ≤
        H + (∑ a : Vertex k, updatesENN (A.policy ω) (A.tapes ω) (oracle a)) / T +
        (∑ a : Vertex k, checksENN (A.policy ω) (A.tapes ω) (oracle a)) / Q := by
    have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Vertex k)))
      (fun a _ => successScore_truncate_le T Q hT hQ (A.policy ω) (A.tapes ω) (oracle a))
    simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul] at hs ⊢
    exact hs.trans (add_le_add (add_le_add
      (A.truncated_score_bound b T Q hA ω) le_rfl) le_rfl)
  have hi := lintegral_mono hpoint (μ := μ)
  have hmu : Measurable fun ω => ∑ a : Vertex k, updatesENN (A.policy ω) (A.tapes ω) (oracle a) :=
    Finset.measurable_sum _ (fun a _ => hobs.updates a)
  have hmc : Measurable fun ω => ∑ a : Vertex k, checksENN (A.policy ω) (A.tapes ω) (oracle a) :=
    Finset.measurable_sum _ (fun a _ => hobs.checks a)
  simp only [div_eq_mul_inv] at hi
  rw [lintegral_finsetSum _ (fun a _ => hobs.success a),
    lintegral_add_right _ (hmc.mul_const _),
    lintegral_add_right _ (hmu.mul_const _), lintegral_const,
    measure_univ, mul_one,
    lintegral_mul_const _ hmu, lintegral_mul_const _ hmc,
    lintegral_finsetSum _ (fun a _ => hobs.updates a),
    lintegral_finsetSum _ (fun a _ => hobs.checks a)] at hi
  have hr := mul_le_mul hi (le_rfl : (N k : ℝ≥0∞)⁻¹ ≤ (N k : ℝ≥0∞)⁻¹)
  simpa [Randomized.averageSuccess, Randomized.success, Randomized.averageUpdates,
    Randomized.averageChecks, H, div_eq_mul_inv, add_mul, mul_add, mul_assoc,
    mul_left_comm, mul_comm] using hr

end Cycle
end RandomWalkSearch
