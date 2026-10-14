import RandomWalkSearch.LazyWalk
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Genuine exit times of the lazy walk

The finite-horizon quantities are computed by running the actual absorbing
nearest-neighbour walk. Their expectation is then proved from its transition
law. The potential calculation is used to derive finite expected absorption,
not to define an expectation.
-/

noncomputable section
namespace RandomWalkSearch.LazyWalk
open scoped BigOperators
open Filter Topology

structure ExitState where
  position : ℤ
  elapsed : ℕ

def exitInitial : ExitState := ⟨0, 0⟩

def exitAdvance (r : ℕ) (s : ExitState) (q : Fin 4) : ExitState :=
  if |s.position| < (r : ℤ) then
    ⟨s.position + (Cycle.increment q).value, s.elapsed + 1⟩
  else s

def exitRun (r : ℕ) : (n : ℕ) → Tape n → ExitState
  | 0, _ => exitInitial
  | n + 1, w => exitAdvance r (exitRun r n w.1) w.2

def exitPotential (r : ℕ) (s : ExitState) : ℝ :=
  2 * ((r : ℝ) ^ 2 - (s.position : ℝ) ^ 2)

def alive (r : ℕ) (s : ExitState) : ℝ := if |s.position| < (r : ℤ) then 1 else 0

/-- Actual finite-horizon survival probability. -/
def survival (r n : ℕ) : ℝ := expect (fun w : Tape n => alive r (exitRun r n w))

/-- Expected actual number of steps made before absorption or the horizon. -/
def truncatedExit (r n : ℕ) : ℝ :=
  expect (fun w : Tape n => ((exitRun r n w).elapsed : ℝ))

theorem increment_abs_le (q : Fin 4) : |(Cycle.increment q).value| ≤ 1 := by
  cases h : Cycle.increment q <;> norm_num [Cycle.Increment.value]

theorem exitRun_position_bound (r n : ℕ) (w : Tape n) :
    |(exitRun r n w).position| ≤ (r : ℤ) := by
  induction n with
  | zero => simp [exitRun, exitInitial]
  | succ n ih =>
    dsimp [exitRun, exitAdvance]
    split
    · rename_i h
      have hp := abs_add_le (exitRun r n w.1).position (Cycle.increment w.2).value
      have hi := increment_abs_le w.2
      dsimp
      omega
    · exact ih w.1

theorem exitRun_elapsed_le (r n : ℕ) (w : Tape n) : (exitRun r n w).elapsed ≤ n := by
  induction n with
  | zero => simp [exitRun, exitInitial]
  | succ n ih =>
    have := ih w.1
    dsimp [exitRun, exitAdvance]
    split
    · change (exitRun r n w.1).elapsed + 1 ≤ n + 1
      omega
    · exact Nat.le_succ_of_le this

theorem exitRun_alive_elapsed (r n : ℕ) (w : Tape n)
    (h : |(exitRun r n w).position| < (r : ℤ)) : (exitRun r n w).elapsed = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    dsimp [exitRun, exitAdvance] at h ⊢
    by_cases ha : |(exitRun r n w.1).position| < (r : ℤ)
    · simp only [ha, reduceIte] at h ⊢
      exact congrArg (· + 1) (ih w.1 ha)
    · simp only [ha, reduceIte] at h

theorem exitPotential_nonneg {r : ℕ} {s : ExitState} (h : |s.position| ≤ (r : ℤ)) :
    0 ≤ exitPotential r s := by
  have hb := abs_le.mp h
  have h1 : -(r : ℝ) ≤ (s.position : ℝ) := by exact_mod_cast hb.1
  have h2 : (s.position : ℝ) ≤ (r : ℝ) := by exact_mod_cast hb.2
  dsimp [exitPotential]
  nlinarith

theorem exitPotential_boundary {r : ℕ} {s : ExitState}
    (h : |s.position| ≤ (r : ℤ)) (ha : ¬ |s.position| < (r : ℤ)) :
    exitPotential r s = 0 := by
  have he : |s.position| = (r : ℤ) := le_antisymm h (le_of_not_gt ha)
  have hs : s.position = (r : ℤ) ∨ s.position = -(r : ℤ) := (abs_eq (by omega)).mp he
  rcases hs with hs | hs <;> simp [exitPotential, hs]

theorem exitPotential_le_alive {r : ℕ} {s : ExitState} (h : |s.position| ≤ (r : ℤ)) :
    exitPotential r s ≤ 2 * (r : ℝ) ^ 2 * alive r s := by
  by_cases ha : |s.position| < (r : ℤ)
  · simp only [alive, ha, reduceIte, mul_one, exitPotential]
    nlinarith [sq_nonneg (s.position : ℝ)]
  · rw [exitPotential_boundary h ha]
    simp [alive, ha]

theorem exit_step_identity (r : ℕ) (s : ExitState) :
    (𝔼 q : Fin 4, (((exitAdvance r s q).elapsed : ℝ) +
      exitPotential r (exitAdvance r s q))) = (s.elapsed : ℝ) + exitPotential r s := by
  by_cases ha : |s.position| < (r : ℤ)
  · rw [expect_four]
    simp only [exitAdvance, ha, reduceIte, exitPotential]
    norm_num [Cycle.increment, Cycle.Increment.value]
    ring
  · simp only [exitAdvance, ha, reduceIte]
    exact Fintype.expect_const _

theorem exit_expected_conservation (r n : ℕ) :
    truncatedExit r n + expect (fun w : Tape n => exitPotential r (exitRun r n w)) =
      2 * (r : ℝ) ^ 2 := by
  unfold truncatedExit
  rw [← expect_add]
  induction n with
  | zero => simp [exitRun, exitInitial, exitPotential]
  | succ n ih =>
    rw [expect_succ]
    change expect (fun w : Tape n => 𝔼 q : Fin 4,
      (((exitAdvance r (exitRun r n w) q).elapsed : ℝ) +
      exitPotential r (exitAdvance r (exitRun r n w) q))) = _
    simp_rw [exit_step_identity]
    exact ih

theorem truncatedExit_le (r n : ℕ) : truncatedExit r n ≤ 2 * (r : ℝ) ^ 2 := by
  have := exit_expected_conservation r n
  have := expect_nonneg (fun w : Tape n =>
    exitPotential_nonneg (exitRun_position_bound r n w))
  linarith

theorem survival_nonneg (r n : ℕ) : 0 ≤ survival r n := by
  exact expect_nonneg (fun _ => by dsimp [alive]; split <;> norm_num)

theorem survival_mul_le (r n : ℕ) : (n : ℝ) * survival r n ≤ truncatedExit r n := by
  unfold survival truncatedExit
  rw [← expect_const_mul]
  apply expect_mono
  intro w
  by_cases ha : |(exitRun r n w).position| < (r : ℤ)
  · simp [alive, ha, exitRun_alive_elapsed r n w ha]
  · simp [alive, ha]

theorem survival_le (r n : ℕ) (hn : 0 < n) :
    survival r n ≤ 2 * (r : ℝ) ^ 2 / (n : ℝ) := by
  have hp : 0 < (n : ℝ) := by exact_mod_cast hn
  apply (le_div_iff₀ hp).mpr
  rw [mul_comm]
  exact (survival_mul_le r n).trans (truncatedExit_le r n)

/-- In particular, the probability of failing to exit tends to zero. -/
theorem survival_tendsto_zero (r : ℕ) : Tendsto (survival r) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall (survival_nonneg r))
    (show ∀ᶠ n : ℕ in atTop, survival r n ≤ 2 * (r : ℝ) ^ 2 / (n : ℝ) from
      (eventually_gt_atTop 0).mono (fun n hn => survival_le r n hn))
    (tendsto_const_div_atTop_nhds_zero_nat _)

theorem exitPotential_expect_tendsto_zero (r : ℕ) :
    Tendsto (fun n => expect (fun w : Tape n => exitPotential r (exitRun r n w)))
      atTop (𝓝 0) := by
  have hu (n : ℕ) : expect (fun w : Tape n => exitPotential r (exitRun r n w)) ≤
      2 * (r : ℝ) ^ 2 * survival r n := by
    unfold survival
    rw [← expect_const_mul]
    exact expect_mono (fun w => exitPotential_le_alive (exitRun_position_bound r n w))
  apply squeeze_zero (fun n => expect_nonneg (fun w =>
    exitPotential_nonneg (exitRun_position_bound r n w))) hu
  simpa using (survival_tendsto_zero r).const_mul (2 * (r : ℝ) ^ 2)

/-- The expected truncated, genuinely executed exit time converges to `2 r²`. -/
theorem truncatedExit_tendsto (r : ℕ) :
    Tendsto (truncatedExit r) atTop (𝓝 (2 * (r : ℝ) ^ 2)) := by
  have he : truncatedExit r = fun n => 2 * (r : ℝ) ^ 2 -
      expect (fun w : Tape n => exitPotential r (exitRun r n w)) := by
    funext n
    have := exit_expected_conservation r n
    linarith
  rw [he]
  simpa using tendsto_const_nhds.sub (exitPotential_expect_tendsto_zero r)

/-- One more genuine update is made exactly on the event of still being inside. -/
theorem truncatedExit_succ (r n : ℕ) :
    truncatedExit r (n + 1) = truncatedExit r n + survival r n := by
  unfold truncatedExit survival
  rw [expect_succ, ← expect_add]
  apply congrArg expect
  funext w
  change (𝔼 q : Fin 4, ((exitAdvance r (exitRun r n w) q).elapsed : ℝ)) = _
  by_cases ha : |(exitRun r n w).position| < (r : ℤ)
  · simp [exitAdvance, alive, ha]
  · simp [exitAdvance, alive, ha]

theorem sum_survival_eq_truncatedExit (r n : ℕ) :
    ∑ t ∈ Finset.range n, survival r t = truncatedExit r n := by
  induction n with
  | zero => simp [truncatedExit, exitRun, exitInitial]
  | succ n ih => rw [Finset.sum_range_succ, ih, truncatedExit_succ]

/-- Tail-sum expectation derived from the actual finite-prefix probabilities. -/
theorem hasSum_survival (r : ℕ) : HasSum (survival r) (2 * (r : ℝ) ^ 2) := by
  apply (hasSum_iff_tendsto_nat_of_nonneg (survival_nonneg r) _).mpr
  simpa only [sum_survival_eq_truncatedExit] using truncatedExit_tendsto r

theorem tsum_survival (r : ℕ) : ∑' n, survival r n = 2 * (r : ℝ) ^ 2 :=
  (hasSum_survival r).tsum_eq

/-- The original, unstopped integer-valued walk, driven by the same tape. -/
def integerWalk (w : ℕ → Fin 4) : ℕ → ℤ
  | 0 => 0
  | n + 1 => integerWalk w n + (Cycle.increment (w n)).value

theorem run_prefix_position (w : ℕ → Fin 4) (n : ℕ) :
    (run n (prefixTape n w)).position = (integerWalk w n : ℝ) := by
  induction n with
  | zero => simp [prefixTape, initial, integerWalk]
  | succ n ih =>
    simp only [prefixTape, run_succ, advance, ih, integerWalk, delta, Int.cast_add]

theorem integerWalk_abs_step (w : ℕ → Fin 4) (n : ℕ) :
    |integerWalk w (n + 1)| ≤ |integerWalk w n| + 1 := by
  change |integerWalk w n + (Cycle.increment (w n)).value| ≤ |integerWalk w n| + 1
  have h₁ := abs_add_le (integerWalk w n) (Cycle.increment (w n)).value
  have h₂ := increment_abs_le (w n)
  omega

/-- First departure from the open interval, with value infinity if no departure occurs. -/
def exitTime (r : ℕ) (w : ℕ → Fin 4) : WithTop ℕ := by
  classical
  exact if h : ∃ n, (r : ℤ) ≤ |integerWalk w n| then (Nat.find h : WithTop ℕ) else ⊤

theorem first_exit_boundary {r : ℕ} {w : ℕ → Fin 4}
    (h : ∃ n, (r : ℤ) ≤ |integerWalk w n|) :
    |integerWalk w (Nat.find h)| = (r : ℤ) := by
  have hh := Nat.find_spec h
  rcases ht : Nat.find h with _ | t
  · rw [ht] at hh
    simp only [integerWalk, abs_zero] at hh ⊢
    omega
  · have hb : |integerWalk w t| < (r : ℤ) := lt_of_not_ge (Nat.find_min h (by omega))
    have hs := integerWalk_abs_step w t
    rw [ht] at hh
    omega

/-- Before its first exit the absorbed execution is literally the original walk. -/
theorem exitRun_before (r n : ℕ) (w : ℕ → Fin 4)
    (h : ∀ j < n, |integerWalk w j| < (r : ℤ)) :
    exitRun r n (prefixTape n w) = ⟨integerWalk w n, n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hi := ih (fun j hj => h j (by omega))
    have hn := h n (by omega)
    simp [prefixTape, exitRun, hi, exitAdvance, hn, integerWalk]

/-- Exact stopped-process representation at a genuine first boundary hit. -/
theorem exitRun_at_first {r t : ℕ} (w : ℕ → Fin 4)
    (hb : |integerWalk w t| = (r : ℤ))
    (hbefore : ∀ j < t, |integerWalk w j| < (r : ℤ)) (n : ℕ) :
    exitRun r n (prefixTape n w) = ⟨integerWalk w (min n t), min n t⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    by_cases hn : n < t
    · have hm : min n t = n := Nat.min_eq_left (by omega)
      have hm' : min (n + 1) t = n + 1 := Nat.min_eq_left (by omega)
      have ha := hbefore n hn
      simp [prefixTape, exitRun, ih, hm, hm', exitAdvance, ha, integerWalk]
    · have hm : min n t = t := Nat.min_eq_right (by omega)
      have hm' : min (n + 1) t = t := Nat.min_eq_right (by omega)
      simp [prefixTape, exitRun, ih, hm, hm', exitAdvance, hb]

/-- The executed truncated counter equals the minimum of the actual stopping time and horizon. -/
theorem elapsed_eq_min_exitTime (r n : ℕ) (w : ℕ → Fin 4) :
    ((exitRun r n (prefixTape n w)).elapsed : WithTop ℕ) = min (n : WithTop ℕ) (exitTime r w) := by
  unfold exitTime
  split
  · rename_i h
    have hs := exitRun_at_first w (first_exit_boundary h)
      (fun j hj => lt_of_not_ge (Nat.find_min h hj)) n
    rw [hs]
    change ((min n (Nat.find h) : ℕ) : WithTop ℕ) = _
    by_cases hn : n ≤ Nat.find h
    · rw [Nat.min_eq_left hn]
      exact (min_eq_left (by exact_mod_cast hn)).symm
    · have hn' : Nat.find h ≤ n := by omega
      rw [Nat.min_eq_right hn']
      exact (min_eq_right (by exact_mod_cast hn')).symm
  · rename_i h
    have hh (j : ℕ) : |integerWalk w j| < (r : ℤ) := by
      exact lt_of_not_ge (fun hj => h ⟨j, hj⟩)
    rw [exitRun_before r n w (fun j _ => hh j)]
    simp

theorem exitTime_le_iff (r n : ℕ) (w : ℕ → Fin 4) :
    exitTime r w ≤ (n : WithTop ℕ) ↔ ∃ t ≤ n, |integerWalk w t| = (r : ℤ) := by
  unfold exitTime
  split
  · rename_i h
    constructor
    · intro hn
      exact ⟨Nat.find h, by exact_mod_cast hn, first_exit_boundary h⟩
    · rintro ⟨t, ht, hb⟩
      exact_mod_cast (Nat.find_min' h (le_of_eq hb.symm)).trans ht
  · rename_i h
    constructor
    · intro hn
      exact False.elim (WithTop.not_top_le_coe n hn)
    · rintro ⟨t, _, hb⟩
      exact False.elim (h ⟨t, le_of_eq hb.symm⟩)

/-- The survival indicator is precisely the event that the genuine first boundary hit
has not happened by the horizon. -/
theorem alive_iff_lt_exitTime (r n : ℕ) (w : ℕ → Fin 4) :
    |(exitRun r n (prefixTape n w)).position| < (r : ℤ) ↔
      (n : WithTop ℕ) < exitTime r w := by
  unfold exitTime
  split
  · rename_i h
    have hs := exitRun_at_first w (first_exit_boundary h)
      (fun j hj => lt_of_not_ge (Nat.find_min h hj)) n
    rw [hs]
    change |integerWalk w (min n (Nat.find h))| < (r : ℤ) ↔ _
    by_cases hn : n < Nat.find h
    · rw [Nat.min_eq_left hn.le]
      constructor
      · intro _
        exact_mod_cast hn
      · intro _
        exact lt_of_not_ge (Nat.find_min h hn)
    · rw [Nat.min_eq_right (by omega), first_exit_boundary h]
      simp only [lt_self_iff_false, false_iff, not_lt]
      exact_mod_cast (show Nat.find h ≤ n by omega)
  · rename_i h
    have hh (j : ℕ) : |integerWalk w j| < (r : ℤ) :=
      lt_of_not_ge (fun hj => h ⟨j, hj⟩)
    rw [exitRun_before r n w (fun j _ => hh j)]
    simp [hh]

end RandomWalkSearch.LazyWalk
