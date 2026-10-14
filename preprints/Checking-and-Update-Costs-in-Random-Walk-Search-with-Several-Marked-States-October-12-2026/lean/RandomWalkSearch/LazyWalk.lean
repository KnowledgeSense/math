import RandomWalkSearch.Cycle
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! # The actual lazy walk on independent uniform four-symbol tapes

`Tape n` is the full finite product of `n` copies of `Fin 4`. All expectations
below are `Finset.expect` over this product, not a stipulated moment formula.
The maximal estimate uses the elementary submartingale potential
`2 M |S| - M²`, where `M` is the running absolute maximum.
-/

noncomputable section

namespace RandomWalkSearch.LazyWalk
open scoped BigOperators

/-- A tape with one independent uniform four-symbol coordinate per update. -/
@[reducible] def Tape : ℕ → Type
  | 0 => Unit
  | n + 1 => Tape n × Fin 4

instance tapeFintype : (n : ℕ) → Fintype (Tape n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => by
    letI := tapeFintype n
    exact inferInstanceAs (Fintype (Tape n × Fin 4))

instance tapeNonempty : (n : ℕ) → Nonempty (Tape n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n + 1 => by
    let := tapeNonempty n
    exact inferInstanceAs (Nonempty (Tape n × Fin 4))

/-- The finite prefix read from an actual infinite update tape. -/
def prefixTape : (n : ℕ) → (ℕ → Fin 4) → Tape n
  | 0, _ => ()
  | n + 1, w => (prefixTape n w, w n)

/-- Exact expectation under the uniform product law. -/
def expect {n : ℕ} (f : Tape n → ℝ) : ℝ := 𝔼 w, f w

@[simp] theorem expect_zero (f : Tape 0 → ℝ) : expect f = f () := by
  have hf : f = fun _ => f () := funext (fun w => congrArg f (Subsingleton.elim w ()))
  rw [hf]
  exact Fintype.expect_const _

@[simp] theorem expect_const (n : ℕ) (c : ℝ) :
    expect (n := n) (fun _ => c) = c := Fintype.expect_const c

theorem expect_succ {n : ℕ} (f : Tape (n + 1) → ℝ) :
    expect f = expect (fun w : Tape n => (𝔼 q : Fin 4, f (w, q))) := by
  change (𝔼 w : Tape n × Fin 4, f w) = 𝔼 w : Tape n, 𝔼 q : Fin 4, f (w, q)
  rw [← Finset.univ_product_univ, Finset.expect_product]

theorem expect_four (f : Fin 4 → ℝ) :
    (𝔼 q, f q) = (f 0 + f 1 + f 2 + f 3) / 4 := by
  have h := Fintype.card_mul_expect f
  simp only [Fintype.card_fin, Nat.cast_ofNat, Fin.sum_univ_succ] at h
  norm_num at h
  linarith

theorem expect_mono {n : ℕ} {f g : Tape n → ℝ} (h : ∀ w, f w ≤ g w) :
    expect f ≤ expect g := Finset.expect_le_expect (fun w _ => h w)

theorem expect_nonneg {n : ℕ} {f : Tape n → ℝ} (h : ∀ w, 0 ≤ f w) :
    0 ≤ expect f := Finset.expect_nonneg (fun w _ => h w)

@[simp] theorem expect_add {n : ℕ} (f g : Tape n → ℝ) :
    expect (fun w => f w + g w) = expect f + expect g :=
  Finset.expect_add_distrib _ _ _

@[simp] theorem expect_sub {n : ℕ} (f g : Tape n → ℝ) :
    expect (fun w => f w - g w) = expect f - expect g :=
  Finset.expect_sub_distrib _ _ _

@[simp] theorem expect_mul_const {n : ℕ} (f : Tape n → ℝ) (c : ℝ) :
    expect (fun w => f w * c) = expect f * c := (Finset.expect_mul _ _ _).symm

@[simp] theorem expect_const_mul {n : ℕ} (c : ℝ) (f : Tape n → ℝ) :
    expect (fun w => c * f w) = c * expect f := (Finset.mul_expect _ _ _).symm

/-- Actual increment; the symbols 2 and 3 both mean a stay. -/
def delta (q : Fin 4) : ℝ := (Cycle.increment q).value

@[simp] theorem delta_zero : delta 0 = -1 := by norm_num [delta, Cycle.increment, Cycle.Increment.value]
@[simp] theorem delta_one : delta 1 = 1 := by norm_num [delta, Cycle.increment, Cycle.Increment.value]
@[simp] theorem delta_two : delta 2 = 0 := by norm_num [delta, Cycle.increment, Cycle.Increment.value]
@[simp] theorem delta_three : delta 3 = 0 := by norm_num [delta, Cycle.increment, Cycle.Increment.value]

structure State where
  position : ℝ
  upper : ℝ
  lower : ℝ
  maxAbs : ℝ

def initial : State := ⟨0, 0, 0, 0⟩

def advance (s : State) (q : Fin 4) : State :=
  let x := s.position + delta q
  ⟨x, max s.upper x, min s.lower x, max s.maxAbs |x|⟩

def run : (n : ℕ) → Tape n → State
  | 0, _ => initial
  | n + 1, w => advance (run n w.1) w.2

@[simp] theorem run_zero (w : Tape 0) : run 0 w = initial := rfl
@[simp] theorem run_succ (n : ℕ) (w : Tape n) (q : Fin 4) :
    run (n + 1) (w, q) = advance (run n w) q := rfl

/-- The upper and lower fields are the extrema of the actual successive positions. -/
def positions : (n : ℕ) → Tape n → Finset ℝ
  | 0, _ => {0}
  | n + 1, w => insert (run (n + 1) w).position (positions n w.1)

theorem run_bounds (n : ℕ) (w : Tape n) :
    0 ≤ (run n w).maxAbs ∧ (run n w).upper ≤ (run n w).maxAbs ∧
      -(run n w).maxAbs ≤ (run n w).lower := by
  induction n with
  | zero => simp [initial]
  | succ n ih =>
    obtain ⟨hm, hu, hl⟩ := ih w.1
    dsimp [run, advance]
    refine ⟨hm.trans (le_max_left _ _), max_le ?_ ?_, le_min ?_ ?_⟩
    · exact hu.trans (le_max_left _ _)
    · exact (le_abs_self _).trans (le_max_right _ _)
    · exact (neg_le_neg (le_max_left _ _)).trans hl
    · exact (neg_le_neg (le_max_right _ _)).trans (neg_abs_le _)

/-- The variance identity is calculated from the actual iid product expectation. -/
theorem position_second_moment (n : ℕ) :
    expect (fun w : Tape n => (run n w).position ^ 2) = (n : ℝ) / 2 := by
  induction n with
  | zero => simp [initial]
  | succ n ih =>
    rw [expect_succ]
    simp_rw [expect_four]
    simp only [run_succ, advance, delta_zero, delta_one, delta_two, delta_three, add_zero]
    have h (x : ℝ) : ((x + -1) ^ 2 + (x + 1) ^ 2 + x ^ 2 + x ^ 2) / 4 =
        x ^ 2 + 1 / 2 := by ring
    simp_rw [h]
    rw [expect_add, expect_const, ih]
    push_cast
    ring

/-- A one-step pathwise lookback-potential inequality. -/
theorem maximal_potential_step (m x : ℝ) :
    2 * m * |x| - m ^ 2 ≤ 2 * max m |x| * |x| - (max m |x|) ^ 2 := by
  rcases le_total m |x| with h | h
  · rw [max_eq_right h]
    nlinarith [sq_nonneg (m - |x|)]
  · rw [max_eq_left h]

/-- Conditional nonnegative drift of the lookback potential under the real lazy law. -/
theorem maximal_potential_drift (s : State) (hm : 0 ≤ s.maxAbs) :
    2 * s.maxAbs * |s.position| - s.maxAbs ^ 2 ≤
      𝔼 q : Fin 4, (2 * (advance s q).maxAbs * |(advance s q).position| -
        (advance s q).maxAbs ^ 2) := by
  have h := Finset.expect_le_expect (s := Finset.univ)
    (fun q _ => maximal_potential_step s.maxAbs (s.position + delta q))
  dsimp [advance] at h ⊢
  refine le_trans ?_ h
  rw [expect_four]
  simp only [delta_zero, delta_one, delta_two, delta_three, add_zero]
  have ha : 2 * |s.position| ≤ |s.position + -1| + |s.position + 1| := by
    have := abs_add_le (s.position + -1) (s.position + 1)
    have he : s.position + -1 + (s.position + 1) = 2 * s.position := by ring
    rw [he, abs_mul] at this
    norm_num at this
    exact this
  nlinarith [mul_nonneg hm (sub_nonneg.mpr ha)]

/-- The finite-product L² maximal inequality, proved without an assumed martingale theorem. -/
theorem maximal_potential_nonneg (n : ℕ) :
    0 ≤ expect (fun w : Tape n =>
      2 * (run n w).maxAbs * |(run n w).position| - (run n w).maxAbs ^ 2) := by
  induction n with
  | zero => simp [initial]
  | succ n ih =>
    rw [expect_succ]
    exact ih.trans (expect_mono (fun w => maximal_potential_drift _ (run_bounds n w).1))

theorem expect_cauchy_schwarz {n : ℕ} (f g : Tape n → ℝ) :
    expect (fun w => f w * g w) ^ 2 ≤
      expect (fun w => f w ^ 2) * expect (fun w => g w ^ 2) :=
  Finset.expect_mul_sq_le_sq_mul_sq _ _ _

theorem maxAbs_second_moment_le (n : ℕ) :
    expect (fun w : Tape n => (run n w).maxAbs ^ 2) ≤ 2 * (n : ℝ) := by
  have hp := maximal_potential_nonneg n
  have hc := expect_cauchy_schwarz (fun w : Tape n => (run n w).maxAbs)
    (fun w => |(run n w).position|)
  simp only [sq_abs] at hc
  rw [position_second_moment] at hc
  have hn := expect_nonneg (fun w : Tape n => sq_nonneg (run n w).maxAbs)
  have hcross := expect_nonneg (fun w : Tape n =>
    mul_nonneg (run_bounds n w).1 (abs_nonneg (run n w).position))
  have he : expect (fun w : Tape n =>
      2 * (run n w).maxAbs * |(run n w).position| - (run n w).maxAbs ^ 2) =
      2 * expect (fun w : Tape n => (run n w).maxAbs * |(run n w).position|) -
        expect (fun w : Tape n => (run n w).maxAbs ^ 2) := by
    simp only [mul_assoc, expect_sub, expect_const_mul]
  rw [he] at hp
  nlinarith [sq_nonneg (expect (fun w : Tape n => (run n w).maxAbs ^ 2) -
    2 * expect (fun w : Tape n => (run n w).maxAbs * |(run n w).position|))]

theorem maxAbs_expect_le (n : ℕ) :
    expect (fun w : Tape n => (run n w).maxAbs) ≤ Real.sqrt (2 * (n : ℝ)) := by
  have hc := expect_cauchy_schwarz (fun w : Tape n => (run n w).maxAbs) (fun _ => 1)
  simp only [mul_one, one_pow, expect_const] at hc
  have h2 := hc.trans (maxAbs_second_moment_le n)
  exact (Real.le_sqrt (expect_nonneg (fun w => (run_bounds n w).1)) (by positivity)).mpr h2

/-- Expected range of the actual lazy walk, at every natural horizon. -/
theorem range_expect_le (n : ℕ) :
    expect (fun w : Tape n => (run n w).upper - (run n w).lower) ≤
      2 * Real.sqrt (2 * (n : ℝ)) := by
  calc
    _ ≤ expect (fun w : Tape n => 2 * (run n w).maxAbs) :=
      expect_mono (fun w => by obtain ⟨_, hu, hl⟩ := run_bounds n w; linarith)
    _ = 2 * expect (fun w : Tape n => (run n w).maxAbs) := expect_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (maxAbs_expect_le n) (by norm_num)

end RandomWalkSearch.LazyWalk
