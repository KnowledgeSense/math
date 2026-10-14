import RandomWalkSearch.Restoration

/-! # Coordinate lower bounds with the other coordinate unlimited

Each truncation is an actual policy, and each finite budget is imposed on
actual executions. No finiteness assumption is placed on the unused cost.
-/

namespace RandomWalkSearch
open MeasureTheory
open scoped ENNReal BigOperators

variable {X : Type*}

/-- Check-only truncation preserves success unless the genuine check count
exceeds its cap; updates may diverge. -/
theorem successScore_truncate_checks_le (Q : ℕ) (hQ : 0 < Q)
    (p : Policy X) (r : Tapes X) (o : Oracle X) :
    successScore p r o ≤ successScore (truncate ⊤ Q p) r o + checksENN p r o / Q := by
  classical
  by_cases hc : checksENN p r o ≤ Q
  · have hs : successScore p r o ≤ successScore (truncate ⊤ Q p) r o := by
      unfold successScore
      split_ifs with hs ht
      · exact le_rfl
      · exact False.elim (ht (succeeds_truncate_of_cost_le ⊤ Q p r o le_top
          ((checksENN_le_nat ..).mp hc) hs))
      · exact zero_le
      · exact le_rfl
    exact hs.trans (le_add_of_nonneg_right (by positivity))
  · have h1 : (1 : ℝ≥0∞) ≤ checksENN p r o / Q := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hQ.ne'))
        (Or.inl (ENNReal.natCast_ne_top Q))).mpr
      simpa using (le_of_not_ge hc)
    exact (successScore_le_one ..).trans (h1.trans (le_add_of_nonneg_left (by positivity)))

/-- Update-only truncation, with arbitrarily many checks. -/
theorem successScore_truncate_updates_le (T : ℕ) (hT : 0 < T)
    (p : Policy X) (r : Tapes X) (o : Oracle X) :
    successScore p r o ≤ successScore (truncate T ⊤ p) r o + updatesENN p r o / T := by
  classical
  by_cases hu : updatesENN p r o ≤ T
  · have hs : successScore p r o ≤ successScore (truncate T ⊤ p) r o := by
      unfold successScore
      split_ifs with hs ht
      · exact le_rfl
      · exact False.elim (ht (succeeds_truncate_of_cost_le T ⊤ p r o
          ((updatesENN_le_nat ..).mp hu) le_top hs))
      · exact zero_le
      · exact le_rfl
    exact hs.trans (le_add_of_nonneg_right (by positivity))
  · have h1 : (1 : ℝ≥0∞) ≤ updatesENN p r o / T := by
      apply (ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hT.ne'))
        (Or.inl (ENNReal.natCast_ne_top T))).mpr
      simpa using (le_of_not_ge hu)
    exact (successScore_le_one ..).trans (h1.trans (le_add_of_nonneg_left (by positivity)))

namespace Cycle
variable {k : ℕ} [NeZero (N k)]

/-- The visited-set budget bounds distinct checked vertices, even if checks
are repeated infinitely often. -/
theorem hard_updates_count (b T : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4)
    (hl : ∀ n, (run p (lazyTapes z w) negativeOracle n).halted = false →
      Local (run p (lazyTapes z w) negativeOracle n)
        (p (run p (lazyTapes z w) negativeOracle n)))
    (hb : ∀ n, (run p (lazyTapes z w) negativeOracle n).setups ≤ b)
    (hT : ∀ n, (run p (lazyTapes z w) negativeOracle n).updates ≤ T) :
    (successfulTranslates p (lazyTapes z w)).card ≤
      (T + b + 1) * k ^ 6 + (b + 1) * D k + T := by
  have hI := visitedEver_exposure_le (D k) b T p z w negativeOracle hl hb hT
  have hG := Finset.card_biUnion_le_card_mul (checkedEver p (lazyTapes z w) negativeOracle)
    progressionStarts (k ^ 6) (fun x _ => card_progressionStarts_le x)
  have hO := Finset.card_biUnion_le_card_mul (outputsEver p (lazyTapes z w) negativeOracle)
    markedStarts (D k + k ^ 6) (fun x _ => card_markedStarts_le x)
  have hQ : (checkedEver p (lazyTapes z w) negativeOracle).card ≤ b + T :=
    (Finset.card_le_card (checkedEver_subset_visitedEver p (lazyTapes z w) negativeOracle hl)).trans
      (visitedEver_card_le b T p (lazyTapes z w) negativeOracle hb hT)
  have hG' := Nat.mul_le_mul_right (k ^ 6) hQ
  have hO' := Nat.mul_le_mul_right (D k + k ^ 6)
    (outputsEver_card_le p (lazyTapes z w) negativeOracle)
  have hu := (Finset.card_le_card (successfulTranslates_local_subset p (lazyTapes z w) hl)).trans
    (Finset.card_union_le ..)
  have hu' := Finset.card_union_le
    (exposure (D k) (visitedEver p (lazyTapes z w) negativeOracle))
    ((checkedEver p (lazyTapes z w) negativeOracle).biUnion progressionStarts)
  nlinarith

/-- Completion transfers a genuine update budget and locality to the fictitious
run without imposing any bound on checks. -/
theorem genuine_hard_updates_count (b T : ℕ) (p : Policy (Vertex k))
    (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4)
    (hp : Restoration oracle b p (lazyTapes z w))
    (hbud : ∀ a n, Within (T : ℕ∞) ⊤ (run p (lazyTapes z w) (oracle a) n)) :
    (successfulTranslates p (lazyTapes z w)).card ≤
      (T + b + 1) * k ^ 6 + (b + 1) * D k + T := by
  have heq : successfulTranslates p (lazyTapes z w) =
      successfulTranslates (complete oracle p) (lazyTapes z w) := by
    ext a
    simp only [mem_successfulTranslates, complete_succeeds_iff]
  rw [heq]
  apply hard_updates_count b T (complete oracle p) z w
  · exact complete_local oracle b p (lazyTapes z w) hp negativeOracle
  · exact run_setup_le b _ _ negativeOracle
      (complete_setupBound oracle b p (lazyTapes z w) hp negativeOracle)
  · intro n
    have h := (complete_within oracle T ⊤ p (lazyTapes z w) hbud negativeOracle n).1
    exact_mod_cast h

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
theorem Randomized.truncated_checks_score_bound (A : Randomized k Ω) (Q : ℕ) (ω : Ω) :
    (∑ a : Vertex k, successScore ((A.truncate ⊤ Q).policy ω)
      (A.tapes ω) (oracle a)) ≤ (((Q + 1) * (D k + k ^ 6) : ℕ) : ℝ≥0∞) := by
  rw [sum_successScore_eq_card]
  exact_mod_cast hard_checks_count Q ((A.truncate ⊤ Q).policy ω) (A.tapes ω)
    (fun n => by
      have h := (truncate_within ⊤ Q (A.policy ω) (A.tapes ω) negativeOracle n).2
      exact_mod_cast h)

omit [MeasurableSpace Ω] in
theorem Randomized.truncated_updates_score_bound (A : Randomized k Ω) (b T : ℕ)
    (hA : A.Restoration b) (ω : Ω) :
    (∑ a : Vertex k, successScore ((A.truncate T ⊤).policy ω)
      (A.tapes ω) (oracle a)) ≤
      (((T + b + 1) * k ^ 6 + (b + 1) * D k + T : ℕ) : ℝ≥0∞) := by
  rw [sum_successScore_eq_card]
  exact_mod_cast genuine_hard_updates_count b T
    ((A.truncate T ⊤).policy ω) (A.setups ω) (A.increments ω)
    (A.restoration_truncate b hA T ⊤ ω)
    (fun a n => truncate_within T ⊤ (A.policy ω) (A.tapes ω) (oracle a) n)

/-- Integration of check-only truncation uses no update measurability or bound. -/
theorem Randomized.expected_checks_budget (A : Randomized k Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hs : ∀ a, Measurable fun ω => successScore (A.policy ω) (A.tapes ω) (oracle a))
    (hc : ∀ a, Measurable fun ω => checksENN (A.policy ω) (A.tapes ω) (oracle a))
    (Q : ℕ) (hQ : 0 < Q) :
    A.averageSuccess μ ≤ (((Q + 1) * (D k + k ^ 6) : ℕ) : ℝ≥0∞) / N k +
      A.averageChecks μ / Q := by
  classical
  let H : ℝ≥0∞ := ((Q + 1) * (D k + k ^ 6) : ℕ)
  have hpoint (ω : Ω) :
      (∑ a : Vertex k, successScore (A.policy ω) (A.tapes ω) (oracle a)) ≤
        H + (∑ a : Vertex k, checksENN (A.policy ω) (A.tapes ω) (oracle a)) / Q := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Vertex k)))
      (fun a _ => successScore_truncate_checks_le Q hQ (A.policy ω) (A.tapes ω) (oracle a))
    simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul] at h ⊢
    exact h.trans (add_le_add (A.truncated_checks_score_bound Q ω) le_rfl)
  have hi := lintegral_mono hpoint (μ := μ)
  have hmc : Measurable fun ω => ∑ a : Vertex k, checksENN (A.policy ω) (A.tapes ω) (oracle a) :=
    Finset.measurable_sum _ (fun a _ => hc a)
  simp only [div_eq_mul_inv] at hi
  rw [lintegral_finsetSum _ (fun a _ => hs a), lintegral_add_right _ (hmc.mul_const _),
    lintegral_const, measure_univ, mul_one, lintegral_mul_const _ hmc,
    lintegral_finsetSum _ (fun a _ => hc a)] at hi
  have hr := mul_le_mul hi (le_rfl : (N k : ℝ≥0∞)⁻¹ ≤ (N k : ℝ≥0∞)⁻¹)
  simpa [Randomized.averageSuccess, Randomized.success, Randomized.averageChecks,
    H, div_eq_mul_inv, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using hr

/-- Integration of update-only truncation uses no check measurability or bound. -/
theorem Randomized.expected_updates_budget (A : Randomized k Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hs : ∀ a, Measurable fun ω => successScore (A.policy ω) (A.tapes ω) (oracle a))
    (hu : ∀ a, Measurable fun ω => updatesENN (A.policy ω) (A.tapes ω) (oracle a))
    (b T : ℕ) (hA : A.Restoration b) (hT : 0 < T) :
    A.averageSuccess μ ≤
      (((T + b + 1) * k ^ 6 + (b + 1) * D k + T : ℕ) : ℝ≥0∞) / N k +
      A.averageUpdates μ / T := by
  classical
  let H : ℝ≥0∞ := ((T + b + 1) * k ^ 6 + (b + 1) * D k + T : ℕ)
  have hpoint (ω : Ω) :
      (∑ a : Vertex k, successScore (A.policy ω) (A.tapes ω) (oracle a)) ≤
        H + (∑ a : Vertex k, updatesENN (A.policy ω) (A.tapes ω) (oracle a)) / T := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Vertex k)))
      (fun a _ => successScore_truncate_updates_le T hT (A.policy ω) (A.tapes ω) (oracle a))
    simp only [Finset.sum_add_distrib, div_eq_mul_inv, ← Finset.sum_mul] at h ⊢
    exact h.trans (add_le_add (A.truncated_updates_score_bound b T hA ω) le_rfl)
  have hi := lintegral_mono hpoint (μ := μ)
  have hmu : Measurable fun ω => ∑ a : Vertex k, updatesENN (A.policy ω) (A.tapes ω) (oracle a) :=
    Finset.measurable_sum _ (fun a _ => hu a)
  simp only [div_eq_mul_inv] at hi
  rw [lintegral_finsetSum _ (fun a _ => hs a), lintegral_add_right _ (hmu.mul_const _),
    lintegral_const, measure_univ, mul_one, lintegral_mul_const _ hmu,
    lintegral_finsetSum _ (fun a _ => hu a)] at hi
  have hr := mul_le_mul hi (le_rfl : (N k : ℝ≥0∞)⁻¹ ≤ (N k : ℝ≥0∞)⁻¹)
  simpa [Randomized.averageSuccess, Randomized.success, Randomized.averageUpdates,
    H, div_eq_mul_inv, add_mul, mul_add, mul_assoc, mul_left_comm, mul_comm] using hr

omit [NeZero (N k)] in
/-- Arithmetic with the exact single-vertex upper mass bound `(k+1)/k²`. -/
theorem checks_budget_arithmetic (hk : 32 ≤ k) (c : ℝ) (hc : 0 ≤ c)
    (Q : ℕ) (hQ : 4*c+1 ≤ (Q : ℝ)) (hQ' : (Q : ℝ) ≤ 4*c+2)
    (h : (1 : ℝ)/2 ≤ (((Q+1)*(D k+k^6) : ℕ) : ℝ)/N k + c/Q) :
    (k : ℝ)/32 ≤ c := by
  have hk32 : (32 : ℝ) ≤ k := by exact_mod_cast hk
  have hkp : (0 : ℝ) < k := by linarith
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkp
  have hQp : (0 : ℝ) < Q := by linarith
  have hcu : c/(Q : ℝ) ≤ 1/4 := (div_le_iff₀ hQp).mpr (by linarith)
  have heq : (((Q+1)*(D k+k^6) : ℕ) : ℝ)/N k =
      ((Q : ℝ)+1)*((k : ℝ)+1)/(k : ℝ)^2 := by
    simp only [N, D, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
    field_simp
  rw [heq] at h
  have hQu : ((Q : ℝ)+1)*((k : ℝ)+1)/(k : ℝ)^2 ≤
      (4*c+3)*((k : ℝ)+1)/(k : ℝ)^2 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hh : (1 : ℝ)/4 ≤ (4*c+3)*((k : ℝ)+1)/(k : ℝ)^2 := by linarith
  have hm := (le_div_iff₀ (show (0 : ℝ) < (k : ℝ)^2 by positivity)).mp hh
  have hkquad : 32*(k : ℝ) ≤ (k : ℝ)^2 := by nlinarith
  by_contra hn
  have hcn : c < (k : ℝ)/32 := lt_of_not_ge hn
  have hmul := mul_lt_mul_of_pos_right hcn (show (0 : ℝ) < (k : ℝ)+1 by positivity)
  nlinarith

omit [NeZero (N k)] in
/-- The update-only arithmetic does not mention the expected checking cost. -/
theorem updates_budget_arithmetic (b : ℕ) (hb : 1 ≤ b)
    (hk : 16*(b+1) ≤ k) (a : ℝ) (ha : 0 ≤ a)
    (T : ℕ) (hT : 4*a+1 ≤ (T : ℝ)) (hT' : (T : ℝ) ≤ 4*a+2)
    (h : (1 : ℝ)/2 ≤
      (((T+b+1)*k^6+(b+1)*D k+T : ℕ) : ℝ)/N k+a/T) :
    (L k : ℝ)/64 ≤ a := by
  have hk32 : (32 : ℝ) ≤ k := by exact_mod_cast (by omega : 32 ≤ k)
  have hkp : (0 : ℝ) < k := by linarith
  have hk0 : (k : ℝ) ≠ 0 := ne_of_gt hkp
  have hTp : (0 : ℝ) < T := by linarith
  have hau : a/(T : ℝ) ≤ 1/4 := (div_le_iff₀ hTp).mpr (by linarith)
  have hkr : 16*((b : ℝ)+1) ≤ k := by exact_mod_cast hk
  have hbr : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have heq : (((T+b+1)*k^6+(b+1)*D k+T : ℕ) : ℝ)/N k =
      ((T : ℝ)+(b : ℝ)+1)/(k : ℝ)^2+((b : ℝ)+1)/k+T/(k : ℝ)^8 := by
    simp only [N, D, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_one]
    field_simp
  rw [heq] at h
  have hTu : ((T : ℝ)+(b : ℝ)+1)/(k : ℝ)^2 ≤ (4*a+(b : ℝ)+3)/(k : ℝ)^2 :=
    div_le_div_of_nonneg_right (by linarith) (by positivity)
  have hTu' : (T : ℝ)/(k : ℝ)^8 ≤ (4*a+2)/(k : ℝ)^8 :=
    div_le_div_of_nonneg_right hT' (by positivity)
  have hbsmall : ((b : ℝ)+1)/k ≤ 1/16 := (div_le_iff₀ hkp).mpr (by linarith)
  have hbsmall2 : ((b : ℝ)+3)/(k : ℝ)^2 ≤ 1/32 := by
    apply (div_le_iff₀ (by positivity)).mpr
    have hbk : (b : ℝ)+3 ≤ k := by linarith
    have hkquad : 32*(k : ℝ) ≤ (k : ℝ)^2 := by nlinarith
    linarith
  have hk8 : (64 : ℝ) ≤ (k : ℝ)^8 := by
    nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 32) hk32 8]
  have hsmall8 : 2/(k : ℝ)^8 ≤ 1/32 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hNL : (k : ℝ)^2 ≤ (k : ℝ)^8 := by
    exact pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ k) (by omega : 2 ≤ 8)
  have han : a/(k : ℝ)^8 ≤ a/(k : ℝ)^2 :=
    div_le_div_of_nonneg_left ha (by positivity) hNL
  have hsplit1 : (4*a+(b : ℝ)+3)/(k : ℝ)^2 =
      4*(a/(k : ℝ)^2)+((b : ℝ)+3)/(k : ℝ)^2 := by ring
  have hsplit2 : (4*a+2)/(k : ℝ)^8 = 4*(a/(k : ℝ)^8)+2/(k : ℝ)^8 := by ring
  rw [hsplit1] at hTu
  rw [hsplit2] at hTu'
  have hz : (1 : ℝ)/64 ≤ a/(k : ℝ)^2 := by linarith
  have hm := (le_div_iff₀ (show (0 : ℝ) < (k : ℝ)^2 by positivity)).mp hz
  simpa [L, div_eq_mul_inv, mul_comm] using hm

/-- At least `k/32` expected checks are needed, independently of any update
cost bound, even without a locality assumption. -/
theorem Randomized.checks_lower_bound (A : Randomized k Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hobsS : ∀ a, Measurable fun ω => successScore (A.policy ω) (A.tapes ω) (oracle a))
    (hobsC : ∀ a, Measurable fun ω => checksENN (A.policy ω) (A.tapes ω) (oracle a))
    (hk : 32 ≤ k) (hs : ∀ a, (1 : ℝ≥0∞)/2 ≤ A.success μ a) :
    (k : ℝ≥0∞)/32 ≤ A.averageChecks μ := by
  by_cases hc : A.averageChecks μ = ∞
  · simp [hc]
  have hkpos : 0 < k := by omega
  have hN : (N k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (N_pos hkpos).ne'
  let c := (A.averageChecks μ).toReal
  let Q : ℕ := ⌈4*c+1⌉₊
  have hcn : 0 ≤ c := ENNReal.toReal_nonneg
  have hQ : 4*c+1 ≤ (Q : ℝ) := Nat.le_ceil _
  have hQ' : (Q : ℝ) ≤ 4*c+2 := by
    have := Nat.ceil_lt_add_one (show 0 ≤ 4*c+1 by linarith)
    dsimp [Q]
    linarith
  have hQp : 0 < Q := by exact_mod_cast (show (0 : ℝ) < Q by linarith)
  have hQ0 : (Q : ℝ≥0∞) ≠ 0 := by exact_mod_cast hQp.ne'
  have hbud := (A.averageSuccess_ge_half μ hs).trans
    (A.expected_checks_budget μ hobsS hobsC Q hQp)
  have hHfin : ((((Q+1)*(D k+k^6) : ℕ) : ℝ≥0∞)/N k) ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hN
  have hCfin := ENNReal.div_ne_top hc hQ0
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hHfin, hCfin⟩) hbud
  simp only [ENNReal.toReal_add hHfin hCfin, ENNReal.toReal_div,
    ENNReal.toReal_natCast] at hreal
  have harith := checks_budget_arithmetic hk c hcn Q hQ hQ' hreal
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by norm_num)) hc).mp
  simpa [c, ENNReal.toReal_div, ENNReal.toReal_natCast] using harith

/-- At least `L/64` expected restoration updates are needed, independently of
any checking cost bound. Genuine runs and both infinite costs are allowed. -/
theorem Randomized.updates_lower_bound (A : Randomized k Ω)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hobsS : ∀ a, Measurable fun ω => successScore (A.policy ω) (A.tapes ω) (oracle a))
    (hobsU : ∀ a, Measurable fun ω => updatesENN (A.policy ω) (A.tapes ω) (oracle a))
    (b : ℕ) (hb : 1 ≤ b) (hk : 16*(b+1) ≤ k)
    (hA : A.Restoration b) (hs : ∀ a, (1 : ℝ≥0∞)/2 ≤ A.success μ a) :
    (L k : ℝ≥0∞)/64 ≤ A.averageUpdates μ := by
  by_cases ha : A.averageUpdates μ = ∞
  · simp [ha]
  have hkpos : 0 < k := by omega
  have hN : (N k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (N_pos hkpos).ne'
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
    (A.expected_updates_budget μ hobsS hobsU b T hA hTp)
  have hHfin : ((((T+b+1)*k^6+(b+1)*D k+T : ℕ) : ℝ≥0∞)/N k) ≠ ∞ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hN
  have hUfin := ENNReal.div_ne_top ha hT0
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hHfin, hUfin⟩) hbud
  simp only [ENNReal.toReal_add hHfin hUfin, ENNReal.toReal_div,
    ENNReal.toReal_natCast] at hreal
  have harith := updates_budget_arithmetic b hb hk a han T hT hT' hreal
  apply (ENNReal.toReal_le_toReal (ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by norm_num)) ha).mp
  simpa [a, ENNReal.toReal_div, ENNReal.toReal_natCast] using harith

end Cycle
end RandomWalkSearch
