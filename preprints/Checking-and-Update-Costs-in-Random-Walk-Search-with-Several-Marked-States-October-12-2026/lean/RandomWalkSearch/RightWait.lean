import RandomWalkSearch.LazyExitLaw

/-! Waiting for actual rightward symbols, with derived mean four attempts per advance. -/
noncomputable section
namespace RandomWalkSearch.LazyWalk
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

structure RightState where
  remaining : ℕ
  elapsed : ℕ

def rightAdvance (s : RightState) (q : Fin 4) : RightState :=
  if s.remaining = 0 then s
  else ⟨if q = 1 then s.remaining - 1 else s.remaining, s.elapsed + 1⟩

def rightRun (r : ℕ) : (n : ℕ) → Tape n → RightState
  | 0, _ => ⟨r, 0⟩
  | n + 1, w => rightAdvance (rightRun r n w.1) w.2

def rightAlive (s : RightState) : ℝ := if s.remaining = 0 then 0 else 1

def rightSurvival (r n : ℕ) : ℝ := expect (fun w : Tape n => rightAlive (rightRun r n w))
def rightTruncated (r n : ℕ) : ℝ := expect (fun w : Tape n => ((rightRun r n w).elapsed : ℝ))

def rightENN (r : ℕ) (w : ℕ → Fin 4) : ℝ≥0∞ :=
  ⨆ n, ((rightRun r n (prefixTape n w)).elapsed : ℝ≥0∞)

def rightCount : (n : ℕ) → Tape n → ℕ
  | 0, _ => 0
  | n + 1, w => rightCount n w.1 + if w.2 = 1 then 1 else 0

def rightCountStream (w : ℕ → Fin 4) (n : ℕ) : ℕ := rightCount n (prefixTape n w)

theorem right_remaining (r n : ℕ) (w : Tape n) :
    (rightRun r n w).remaining = r - rightCount n w := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [rightRun, rightAdvance, rightCount]
    by_cases hz : (rightRun r n w.1).remaining = 0
    · simp only [hz, reduceIte]
      rw [ih] at hz
      split <;> omega
    · simp only [hz, reduceIte]
      split <;> rw [ih] <;> omega

theorem right_remaining_le (r n : ℕ) (w : Tape n) : (rightRun r n w).remaining ≤ r := by
  rw [right_remaining]
  omega

theorem right_alive_elapsed (r n : ℕ) (w : Tape n) (h : (rightRun r n w).remaining ≠ 0) :
    (rightRun r n w).elapsed = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [rightRun, rightAdvance] at h ⊢
    by_cases hz : (rightRun r n w.1).remaining = 0
    · simp [hz] at h
    · simp only [hz, reduceIte]
      exact congrArg (· + 1) (ih w.1 hz)

theorem right_conservation_step (s : RightState) :
    (𝔼 q : Fin 4, (((rightAdvance s q).elapsed : ℝ) +
      4 * ((rightAdvance s q).remaining : ℝ))) = (s.elapsed : ℝ) + 4 * (s.remaining : ℝ) := by
  by_cases hz : s.remaining = 0
  · simp [rightAdvance, hz]
  · have hr : 1 ≤ s.remaining := by omega
    rw [expect_four]
    norm_num [rightAdvance, hz, Nat.cast_sub hr]
    ring

theorem right_conservation (r n : ℕ) :
    rightTruncated r n + 4 * expect (fun w : Tape n => ((rightRun r n w).remaining : ℝ)) =
      4 * (r : ℝ) := by
  unfold rightTruncated
  rw [← expect_const_mul, ← expect_add]
  induction n with
  | zero => simp [rightRun]
  | succ n ih =>
    rw [expect_succ]
    change expect (fun w : Tape n => 𝔼 q : Fin 4,
      (((rightAdvance (rightRun r n w) q).elapsed : ℝ) +
      4 * ((rightAdvance (rightRun r n w) q).remaining : ℝ))) = _
    simp_rw [right_conservation_step]
    exact ih

theorem rightTruncated_le (r n : ℕ) : rightTruncated r n ≤ 4 * (r : ℝ) := by
  have := right_conservation r n
  have := expect_nonneg (fun w : Tape n => Nat.cast_nonneg (rightRun r n w).remaining)
  linarith

theorem rightSurvival_nonneg (r n : ℕ) : 0 ≤ rightSurvival r n :=
  expect_nonneg (fun _ => by dsimp [rightAlive]; split <;> norm_num)

theorem rightSurvival_le (r n : ℕ) (hn : 0 < n) :
    rightSurvival r n ≤ 4 * (r : ℝ) / (n : ℝ) := by
  have hm : (n : ℝ) * rightSurvival r n ≤ rightTruncated r n := by
    unfold rightSurvival rightTruncated
    rw [← expect_const_mul]
    apply expect_mono
    intro w
    by_cases hz : (rightRun r n w).remaining = 0
    · simp [rightAlive, hz]
    · simp [rightAlive, hz, right_alive_elapsed r n w hz]
  apply (le_div_iff₀ (by exact_mod_cast hn)).mpr
  rw [mul_comm]
  exact hm.trans (rightTruncated_le r n)

theorem rightSurvival_tendsto (r : ℕ) : Tendsto (rightSurvival r) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (rightSurvival_nonneg r))
    (show ∀ᶠ n : ℕ in atTop, rightSurvival r n ≤ 4 * (r : ℝ) / (n : ℝ) from
      (eventually_gt_atTop 0).mono (fun n hn => rightSurvival_le r n hn))
    (tendsto_const_div_atTop_nhds_zero_nat _)

theorem rightRemaining_tendsto (r : ℕ) :
    Tendsto (fun n => expect (fun w : Tape n => ((rightRun r n w).remaining : ℝ))) atTop (𝓝 0) := by
  have hu (n : ℕ) : expect (fun w : Tape n => ((rightRun r n w).remaining : ℝ)) ≤
      (r : ℝ) * rightSurvival r n := by
    unfold rightSurvival
    rw [← expect_const_mul]
    apply expect_mono
    intro w
    by_cases hz : (rightRun r n w).remaining = 0
    · simp [rightAlive, hz]
    · simp only [rightAlive, hz, reduceIte, mul_one]
      exact_mod_cast right_remaining_le r n w
  apply squeeze_zero (fun n => expect_nonneg (fun w => Nat.cast_nonneg (rightRun r n w).remaining)) hu
  simpa using (rightSurvival_tendsto r).const_mul (r : ℝ)

theorem rightTruncated_tendsto (r : ℕ) : Tendsto (rightTruncated r) atTop (𝓝 (4 * (r : ℝ))) := by
  have he : rightTruncated r = fun n => 4 * (r : ℝ) -
      4 * expect (fun w : Tape n => ((rightRun r n w).remaining : ℝ)) := by
    funext n
    have := right_conservation r n
    linarith
  rw [he]
  simpa using tendsto_const_nhds.sub ((rightRemaining_tendsto r).const_mul 4)

theorem right_elapsed_monotone (r : ℕ) (w : ℕ → Fin 4) :
    Monotone (fun n => (rightRun r n (prefixTape n w)).elapsed) := by
  apply monotone_nat_of_le_succ
  intro n
  change (rightRun r n (prefixTape n w)).elapsed ≤
    (rightAdvance (rightRun r n (prefixTape n w)) (w n)).elapsed
  unfold rightAdvance
  split
  · exact le_rfl
  · exact Nat.le_succ _

theorem rightRun_before (r n : ℕ) (w : ℕ → Fin 4)
    (h : ∀ j < n, rightCountStream w j < r) : (rightRun r n (prefixTape n w)).elapsed = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi := ih (fun j hj => h j (by omega))
    have hn := h n (by omega)
    have hne : (rightRun r n (prefixTape n w)).remaining ≠ 0 := by
      rw [right_remaining]
      change r - rightCountStream w n ≠ 0
      omega
    change (rightAdvance (rightRun r n (prefixTape n w)) (w n)).elapsed = n + 1
    simp [rightAdvance, hne, hi]

theorem rightENN_of_no_finish (r : ℕ) (w : ℕ → Fin 4)
    (h : ¬∃ n, r ≤ rightCountStream w n) : rightENN r w = ⊤ := by
  have hh (j : ℕ) : rightCountStream w j < r := lt_of_not_ge (fun hj => h ⟨j, hj⟩)
  unfold rightENN
  simp only [rightRun_before r _ w (fun j _ => hh j), ENNReal.iSup_natCast]

theorem rightENN_at_first {r : ℕ} (w : ℕ → Fin 4) (h : ∃ n, r ≤ rightCountStream w n) :
    rightENN r w = (Nat.find h : ℝ≥0∞) := by
  let t := Nat.find h
  have hbefore : ∀ j < t, rightCountStream w j < r := fun j hj => lt_of_not_ge (Nat.find_min h hj)
  have hremain : (rightRun r t (prefixTape t w)).remaining = 0 := by
    rw [right_remaining]
    exact Nat.sub_eq_zero_of_le (Nat.find_spec h)
  have hstable (n : ℕ) (hn : t ≤ n) : rightRun r n (prefixTape n w) = rightRun r t (prefixTape t w) := by
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n _ ih =>
      change rightAdvance (rightRun r n (prefixTape n w)) (w n) = _
      simp [ih, rightAdvance, hremain]
  have hat : (rightRun r t (prefixTape t w)).elapsed = t := rightRun_before r t w hbefore
  apply le_antisymm
  · apply iSup_le
    intro n
    by_cases hn : n < t
    · rw [rightRun_before r n w (fun j hj => hbefore j (by omega))]
      exact_mod_cast hn.le
    · rw [hstable n (by omega), hat]
  · exact le_trans (by rw [hat]) (le_iSup (fun n => ((rightRun r n (prefixTape n w)).elapsed : ℝ≥0∞)) t)

variable {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_rightENN (μ : Measure Ω) (w : Ω → ℕ → Fin 4) (hlaw : IID μ w) (r : ℕ) :
    Measurable (fun ω => rightENN r (w ω)) := by
  apply Measurable.iSup
  intro n
  exact measurable_finite_prefix μ w hlaw n (fun t => ((rightRun r n t).elapsed : ℝ≥0∞))

theorem lintegral_rightTruncated (μ : Measure Ω) (w : Ω → ℕ → Fin 4)
    (hlaw : IID μ w) (r n : ℕ) :
    (∫⁻ ω, ((rightRun r n (prefixTape n (w ω))).elapsed : ℝ≥0∞) ∂μ) =
      ENNReal.ofReal (rightTruncated r n) :=
  lintegral_uniform_nat μ (fun ω => prefixTape n (w ω))
    (fun t => (hlaw n t).1) (fun t => (hlaw n t).2) (fun t => (rightRun r n t).elapsed)

theorem lintegral_rightENN (μ : Measure Ω) (w : Ω → ℕ → Fin 4)
    (hlaw : IID μ w) (r : ℕ) :
    (∫⁻ ω, rightENN r (w ω) ∂μ) = ENNReal.ofReal (4 * (r : ℝ)) := by
  have hm : Monotone (fun n ω => ((rightRun r n (prefixTape n (w ω))).elapsed : ℝ≥0∞)) := by
    intro n m hnm ω
    change ((rightRun r n (prefixTape n (w ω))).elapsed : ℝ≥0∞) ≤
      ((rightRun r m (prefixTape m (w ω))).elapsed : ℝ≥0∞)
    exact_mod_cast right_elapsed_monotone r (w ω) hnm
  unfold rightENN
  rw [lintegral_iSup (fun n => measurable_finite_prefix μ w hlaw n
    (fun t => ((rightRun r n t).elapsed : ℝ≥0∞))) hm]
  simp_rw [lintegral_rightTruncated μ w hlaw r]
  have hmono : Monotone (fun n => ENNReal.ofReal (rightTruncated r n)) := by
    intro n m hnm
    change ENNReal.ofReal (rightTruncated r n) ≤ ENNReal.ofReal (rightTruncated r m)
    rw [← lintegral_rightTruncated μ w hlaw r n, ← lintegral_rightTruncated μ w hlaw r m]
    exact lintegral_mono (hm hnm)
  exact tendsto_nhds_unique (tendsto_atTop_iSup hmono)
    (ENNReal.tendsto_ofReal (rightTruncated_tendsto r))

theorem ae_right_finite (μ : Measure Ω) (w : Ω → ℕ → Fin 4)
    (hlaw : IID μ w) (r : ℕ) : ∀ᵐ ω ∂μ, ∃ n, r ≤ rightCountStream (w ω) n := by
  have h := ae_lt_top (measurable_rightENN μ w hlaw r)
    (show (∫⁻ ω, rightENN r (w ω) ∂μ) ≠ ⊤ by rw [lintegral_rightENN μ w hlaw r]; exact ENNReal.ofReal_ne_top)
  exact h.mono (fun ω hω => by
    by_contra hn
    rw [rightENN_of_no_finish r (w ω) hn] at hω
    exact lt_irrefl _ hω)

end RandomWalkSearch.LazyWalk
