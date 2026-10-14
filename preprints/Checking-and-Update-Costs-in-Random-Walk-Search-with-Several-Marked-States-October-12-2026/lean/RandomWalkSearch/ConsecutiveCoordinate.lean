import RandomWalkSearch.CoordinateBounds
import RandomWalkSearch.ConsecutiveProbability
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Update coordinate of the consecutive-trajectory endpoint lower bound -/

namespace RandomWalkSearch.Cycle
open MeasureTheory
open scoped ENNReal BigOperators
variable {k : ℕ} [NeZero (N k)]

/-- Distinct checked vertices fit in the full-tape trajectory ranges even if
the number of actual checking operations is infinite. -/
theorem hard_consecutive_updates_count (b T : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4)
    (hl : ∀ n, (run p (lazyTapes z w) negativeOracle n).halted = false →
      Local (run p (lazyTapes z w) negativeOracle n) (p (run p (lazyTapes z w) negativeOracle n)))
    (he : ∀ n, (run p (lazyTapes z w) negativeOracle n).halted = false →
      Extends (run p (lazyTapes z w) negativeOracle n) (p (run p (lazyTapes z w) negativeOracle n)))
    (hb : ∀ n, (run p (lazyTapes z w) negativeOracle n).setups ≤ b)
    (hT : ∀ n, (run p (lazyTapes z w) negativeOracle n).updates ≤ T) :
    (successfulTranslates p (lazyTapes z w)).card ≤
      (b + rangeSum b T w + 1) * k ^ 6 + (b + 1) * D k + rangeSum b T w := by
  have hI := visitedEver_exposure_le_ranges (D k) b T p z w negativeOracle he hb hT
  have hG := Finset.card_biUnion_le_card_mul (checkedEver p (lazyTapes z w) negativeOracle)
    progressionStarts (k ^ 6) (fun x _ => card_progressionStarts_le x)
  have hO := Finset.card_biUnion_le_card_mul (outputsEver p (lazyTapes z w) negativeOracle)
    markedStarts (D k + k ^ 6) (fun x _ => card_markedStarts_le x)
  have hQ : (checkedEver p (lazyTapes z w) negativeOracle).card ≤ b + rangeSum b T w :=
    (Finset.card_le_card (checkedEver_subset_visitedEver p (lazyTapes z w) negativeOracle hl)).trans
      (visitedEver_card_le_ranges b T p z w negativeOracle he hb hT)
  have hG' := Nat.mul_le_mul_right (k ^ 6) hQ
  have hO' := Nat.mul_le_mul_right (D k + k ^ 6)
    (outputsEver_card_le p (lazyTapes z w) negativeOracle)
  have hu := (Finset.card_le_card (successfulTranslates_local_subset p (lazyTapes z w) hl)).trans
    (Finset.card_union_le ..)
  have hu' := Finset.card_union_le
    (exposure (D k) (visitedEver p (lazyTapes z w) negativeOracle))
    ((checkedEver p (lazyTapes z w) negativeOracle).biUnion progressionStarts)
  nlinarith

/-- The model and budget hypotheses concern actual executions only. -/
theorem genuine_hard_consecutive_updates_count (b T : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4)
    (hp : Consecutive oracle b p (lazyTapes z w))
    (hbud : ∀ a n, Within (T : ℕ∞) ⊤ (run p (lazyTapes z w) (oracle a) n)) :
    (successfulTranslates p (lazyTapes z w)).card ≤
      (b + rangeSum b T w + 1) * k ^ 6 + (b + 1) * D k + rangeSum b T w := by
  have heq : successfulTranslates p (lazyTapes z w) =
      successfulTranslates (complete oracle p) (lazyTapes z w) := by
    ext a
    simp only [mem_successfulTranslates, complete_succeeds_iff]
  rw [heq]
  apply hard_consecutive_updates_count b T (complete oracle p) z w
  · exact complete_local oracle b p (lazyTapes z w) hp.1 negativeOracle
  · exact complete_extends oracle b p (lazyTapes z w) hp negativeOracle
  · exact run_setup_le b _ _ negativeOracle
      (complete_setupBound oracle b p (lazyTapes z w) hp.1 negativeOracle)
  · intro n
    have h := (complete_within oracle T ⊤ p (lazyTapes z w) hbud negativeOracle n).1
    exact_mod_cast h

omit [NeZero (N k)] in
/-- Real arithmetic used after integrating the actual trajectory-range bound. -/
theorem consecutive_updates_budget_arithmetic (b : ℕ) (hb : 1 ≤ b)
    (hk : 16*(b+1) ≤ k) (a : ℝ) (ha : 0 ≤ a)
    (T : ℕ) (hT : 4*a+1 ≤ (T : ℝ)) (hT' : (T : ℝ) ≤ 4*a+2)
    (h : (1 : ℝ)/2 ≤
      (((b : ℝ)+2*b*Real.sqrt (2*T)+1)*(k : ℝ)^6+
        ((b : ℝ)+1)*D k+2*b*Real.sqrt (2*T))/N k+a/T) :
    (L k : ℝ)^2/(8192*(b : ℝ)^2) ≤ a := by
  have hk32 : (32 : ℝ) ≤ k := by exact_mod_cast (by omega : 32 ≤ k)
  have hkp : (0 : ℝ) < k := by linarith
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkp
  have hTp : (0 : ℝ) < T := by linarith
  have hau : a/(T : ℝ) ≤ 1/4 := (div_le_iff₀ hTp).mpr (by linarith)
  have hkr : 16*((b : ℝ)+1) ≤ k := by exact_mod_cast hk
  have hbr : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbpos : (0 : ℝ) < b := by linarith
  have hsqa := Real.sq_sqrt ha
  have hsqrt2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrtT := Real.sq_sqrt (show (0 : ℝ) ≤ 2*T by positivity)
  have hsqrtab := Real.sqrt_nonneg a
  have hsqrt2b := Real.sqrt_nonneg (2 : ℝ)
  have hsqrtTb := Real.sqrt_nonneg (2*(T : ℝ))
  have hsqrt : Real.sqrt (2*(T : ℝ)) ≤ 2*Real.sqrt 2*Real.sqrt a+2 := by
    have hprod : 0 ≤ Real.sqrt 2*Real.sqrt a := mul_nonneg hsqrt2b hsqrtab
    have hprodsq : (Real.sqrt 2*Real.sqrt a)^2 = 2*a := by
      rw [mul_pow, hsqrt2, hsqa]
    nlinarith
  have hrange : 2*(b : ℝ)*Real.sqrt (2*T) ≤
      4*Real.sqrt 2*b*Real.sqrt a+4*b := by
    have hm := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 2*(b : ℝ) by positivity)
    nlinarith
  let r := 4*Real.sqrt 2*(b : ℝ)*Real.sqrt a
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have heq : (((b : ℝ)+2*b*Real.sqrt (2*T)+1)*(k : ℝ)^6+
        ((b : ℝ)+1)*D k+2*b*Real.sqrt (2*T))/N k =
      ((b : ℝ)+2*b*Real.sqrt (2*T)+1)/(k : ℝ)^2+
        ((b : ℝ)+1)/k+(2*b*Real.sqrt (2*T))/(k : ℝ)^8 := by
    simp only [N, D, Nat.cast_pow]
    field_simp
  rw [heq] at h
  have hRu : ((b : ℝ)+2*b*Real.sqrt (2*T)+1)/(k : ℝ)^2 ≤
      (r+5*b+1)/(k : ℝ)^2 :=
    div_le_div_of_nonneg_right (by dsimp [r]; linarith) (by positivity)
  have hRu' : (2*(b : ℝ)*Real.sqrt (2*T))/(k : ℝ)^8 ≤ (r+4*b)/(k : ℝ)^8 :=
    div_le_div_of_nonneg_right hrange (by positivity)
  have hbsmall : ((b : ℝ)+1)/k ≤ 1/16 := (div_le_iff₀ hkp).mpr (by linarith)
  have hbsmall2 : (5*(b : ℝ)+1)/(k : ℝ)^2 ≤ 1/32 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hbk : 5*(b : ℝ)+1 ≤ k := by linarith
    have hkquad : 32*(k : ℝ) ≤ (k : ℝ)^2 := by nlinarith
    linarith
  have hNL : (k : ℝ)^2 ≤ (k : ℝ)^8 :=
    pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ k) (by omega : 2 ≤ 8)
  have hsmall8 : 4*(b : ℝ)/(k : ℝ)^8 ≤ 1/32 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hkquad : 32*(k : ℝ) ≤ (k : ℝ)^2 := by nlinarith
    linarith
  have hrn : r/(k : ℝ)^8 ≤ r/(k : ℝ)^2 :=
    div_le_div_of_nonneg_left hr (by positivity) hNL
  have hsplit1 : (r+5*(b : ℝ)+1)/(k : ℝ)^2 =
      r/(k : ℝ)^2+(5*(b : ℝ)+1)/(k : ℝ)^2 := by ring
  have hsplit2 : (r+4*(b : ℝ))/(k : ℝ)^8 =
      r/(k : ℝ)^8+4*(b : ℝ)/(k : ℝ)^8 := by ring
  rw [hsplit1] at hRu
  rw [hsplit2] at hRu'
  have hz : (1 : ℝ)/16 ≤ r/(k : ℝ)^2 := by linarith
  have hm := (le_div_iff₀ (show (0 : ℝ) < (k : ℝ)^2 by positivity)).mp hz
  have hroot : (k : ℝ)^2 ≤ 64*Real.sqrt 2*b*Real.sqrt a := by dsimp [r] at hm; linarith
  have hsq := sq_le_sq₀ (show (0 : ℝ) ≤ (k : ℝ)^2 by positivity)
    (show (0 : ℝ) ≤ 64*Real.sqrt 2*b*Real.sqrt a by positivity) |>.mpr hroot
  have hsq' : (k : ℝ)^4 ≤ 8192*(b : ℝ)^2*a := by
    calc
      _ = ((k : ℝ)^2)^2 := by ring
      _ ≤ (64*Real.sqrt 2*b*Real.sqrt a)^2 := hsq
      _ = 8192*(b : ℝ)^2*a := by simp only [mul_pow, hsqrt2, hsqa]; ring
  apply (div_le_iff₀ (by positivity)).mpr
  simpa [L, mul_comm, Nat.cast_pow, ← pow_mul] using hsq'

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem Randomized.truncated_consecutive_updates_score_bound (A : Randomized k Ω)
    (b T : ℕ) (hA : A.Consecutive b) (ω : Ω) :
    (∑ a : Vertex k, successScore ((A.truncate T ⊤).policy ω) (A.tapes ω) (oracle a)) ≤
      (((b+1)*k^6+(b+1)*D k : ℕ) : ℝ≥0∞)+
        (rangeSum b T (A.increments ω) : ℝ≥0∞)*((k : ℝ≥0∞)^6+1) := by
  rw [sum_successScore_eq_card]
  have h := genuine_hard_consecutive_updates_count b T
    ((A.truncate T ⊤).policy ω) (A.setups ω) (A.increments ω)
    (A.consecutive_truncate b hA T ⊤ ω)
    (fun a n => truncate_within T ⊤ (A.policy ω) (A.tapes ω) (oracle a) n)
  have hn : (successfulTranslates ((A.truncate T ⊤).policy ω) (A.tapes ω)).card ≤
      ((b+1)*k^6+(b+1)*D k)+rangeSum b T (A.increments ω)*(k^6+1) := by
    dsimp [Randomized.tapes]
    nlinarith
  exact_mod_cast hn

/-- One-cap expected consecutive bound, derived from the actual iid tape law.
The average number of checks is entirely unrestricted. -/
theorem Randomized.expected_consecutive_updates_budget (A : Randomized k Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hobsS : ∀ a, Measurable fun ω => successScore (A.policy ω) (A.tapes ω) (oracle a))
    (hobsU : ∀ a, Measurable fun ω => updatesENN (A.policy ω) (A.tapes ω) (oracle a))
    (hlaw : A.LazyLaw μ) (b T : ℕ) (hA : A.Consecutive b) (hT : 0 < T) :
    A.averageSuccess μ ≤
      ((((b+1)*k^6+(b+1)*D k : ℕ) : ℝ≥0∞)+
        ((b : ℝ≥0∞)*ENNReal.ofReal (2*Real.sqrt (2*(T : ℝ))))*((k : ℝ≥0∞)^6+1))/N k+
      A.averageUpdates μ/T := by
  classical
  let H : ℝ≥0∞ := ((b+1)*k^6+(b+1)*D k : ℕ)
  have hpoint (ω : Ω) :
      (∑ a : Vertex k, successScore (A.policy ω) (A.tapes ω) (oracle a)) ≤
        H+(rangeSum b T (A.increments ω) : ℝ≥0∞)*((k : ℝ≥0∞)^6+1)+
        (∑ a : Vertex k, updatesENN (A.policy ω) (A.tapes ω) (oracle a))/T := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Vertex k)))
      (fun a _ => successScore_truncate_updates_le T hT (A.policy ω) (A.tapes ω) (oracle a))
    simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul] at h ⊢
    exact h.trans (add_le_add (A.truncated_consecutive_updates_score_bound b T hA ω) le_rfl)
  have hi := lintegral_mono hpoint (μ := μ)
  have hmu : Measurable fun ω => ∑ a : Vertex k, updatesENN (A.policy ω) (A.tapes ω) (oracle a) :=
    Finset.measurable_sum _ (fun a _ => hobsU a)
  have hmr := A.measurable_rangeSum μ hlaw b T
  simp only [div_eq_mul_inv] at hi
  rw [lintegral_finsetSum _ (fun a _ => hobsS a), lintegral_add_right _ (hmu.mul_const _),
    lintegral_add_right _ (hmr.mul_const _), lintegral_const, measure_univ, mul_one,
    lintegral_mul_const _ hmr, lintegral_mul_const _ hmu,
    lintegral_finsetSum _ (fun a _ => hobsU a)] at hi
  have hi' := hi.trans (add_le_add
    (add_le_add le_rfl (mul_le_mul (A.lintegral_rangeSum μ hlaw b T) le_rfl (by positivity) (by positivity))) le_rfl)
  have hr := mul_le_mul hi' (le_rfl : (N k : ℝ≥0∞)⁻¹ ≤ (N k : ℝ≥0∞)⁻¹)
  simpa [Randomized.averageSuccess, Randomized.success, Randomized.averageUpdates,
    H, div_eq_mul_inv, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using hr

/-- Exact consecutive update coordinate from operational trajectories and iid
lazy increments, even if the checking expectation is infinite. -/
theorem Randomized.consecutive_updates_lower_bound (A : Randomized k Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hobsS : ∀ a, Measurable fun ω => successScore (A.policy ω) (A.tapes ω) (oracle a))
    (hobsU : ∀ a, Measurable fun ω => updatesENN (A.policy ω) (A.tapes ω) (oracle a))
    (hlaw : A.LazyLaw μ) (b : ℕ) (hb : 1 ≤ b) (hk : 16*(b+1) ≤ k)
    (hA : A.Consecutive b) (hs : ∀ a, (1 : ℝ≥0∞)/2 ≤ A.success μ a) :
    (L k : ℝ≥0∞)^2/(8192*(b : ℝ≥0∞)^2) ≤ A.averageUpdates μ := by
  by_cases ha : A.averageUpdates μ = ∞
  · simp [ha]
  have hkpos : 0 < k := by omega
  have hN : (N k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (N_pos hkpos).ne'
  have hb0 : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
  let a := (A.averageUpdates μ).toReal
  let T : ℕ := ⌈4*a+1⌉₊
  have han : 0 ≤ a := ENNReal.toReal_nonneg
  have hT : 4*a+1 ≤ (T : ℝ) := Nat.le_ceil _
  have hT' : (T : ℝ) ≤ 4*a+2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 4*a+1 by linarith)
    dsimp [T]
    linarith
  have hTp : 0 < T := by exact_mod_cast (show (0 : ℝ) < T by linarith)
  have hT0 : (T : ℝ≥0∞) ≠ 0 := by exact_mod_cast hTp.ne'
  have hbud := (A.averageSuccess_ge_half μ hs).trans
    (A.expected_consecutive_updates_budget μ hobsS hobsU hlaw b T hA hTp)
  have hRfin : ((b : ℝ≥0∞)*ENNReal.ofReal (2*Real.sqrt (2*(T : ℝ)))) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have hKfin : ((k : ℝ≥0∞)^6+1) ≠ ∞ := by simp
  have hHfin :
      (((((b+1)*k^6+(b+1)*D k : ℕ) : ℝ≥0∞)+
        ((b : ℝ≥0∞)*ENNReal.ofReal (2*Real.sqrt (2*(T : ℝ))))*((k : ℝ≥0∞)^6+1))/N k) ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.add_ne_top.mpr
      ⟨ENNReal.natCast_ne_top _, ENNReal.mul_ne_top hRfin hKfin⟩) hN
  have hUfin := ENNReal.div_ne_top ha hT0
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hHfin, hUfin⟩) hbud
  simp only [ENNReal.toReal_add hHfin hUfin, ENNReal.toReal_div,
    ENNReal.toReal_add (ENNReal.natCast_ne_top _) (ENNReal.mul_ne_top hRfin hKfin),
    ENNReal.toReal_add (by simp : (k : ℝ≥0∞)^6 ≠ ∞) (by norm_num : (1 : ℝ≥0∞) ≠ ∞),
    ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity :
      (0 : ℝ) ≤ 2*Real.sqrt (2*(T : ℝ))), ENNReal.toReal_natCast, ENNReal.toReal_one] at hreal
  change (1 : ℝ)/2 ≤ _ at hreal
  have harith := consecutive_updates_budget_arithmetic b hb hk a han T hT hT' (by
    convert hreal using 1
    push_cast
    dsimp [a]
    ring)
  apply (ENNReal.toReal_le_toReal
    (ENNReal.div_ne_top (by simp) (by simp [hb0])) ha).mp
  simpa [a, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_natCast] using harith

end RandomWalkSearch.Cycle

