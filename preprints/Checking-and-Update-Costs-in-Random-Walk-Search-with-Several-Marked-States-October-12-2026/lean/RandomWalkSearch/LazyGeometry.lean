import RandomWalkSearch.LazyWalk

/-! Integer lifts and exact extrema for the finite-prefix lazy walk. -/
noncomputable section
namespace RandomWalkSearch.LazyWalk

structure IntegerState where
  position : ℤ
  upper : ℤ
  lower : ℤ

def integerRun : (n : ℕ) → Tape n → IntegerState
  | 0, _ => ⟨0, 0, 0⟩
  | n + 1, w =>
    let s := integerRun n w.1
    let x := s.position + (Cycle.increment w.2).value
    ⟨x, max s.upper x, min s.lower x⟩

def integerPosition (n : ℕ) (w : Tape n) : ℤ := (integerRun n w).position
def integerUpper (n : ℕ) (w : Tape n) : ℤ := (integerRun n w).upper
def integerLower (n : ℕ) (w : Tape n) : ℤ := (integerRun n w).lower

theorem integer_casts (n : ℕ) (w : Tape n) :
    (integerPosition n w : ℝ) = (run n w).position ∧
    (integerUpper n w : ℝ) = (run n w).upper ∧
    (integerLower n w : ℝ) = (run n w).lower := by
  induction n with
  | zero => simp [integerPosition, integerUpper, integerLower, integerRun, initial]
  | succ n ih =>
    obtain ⟨hp, hu, hl⟩ := ih w.1
    simp only [integerPosition, integerUpper, integerLower] at hp hu hl ⊢
    simp only [integerRun, run, advance, Int.cast_add, Int.cast_max, Int.cast_min, hp, hu, hl, delta]
    exact ⟨trivial, trivial, trivial⟩

theorem integerLower_le_position (n : ℕ) (w : Tape n) :
    integerLower n w ≤ integerPosition n w := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact min_le_right _ _

theorem position_le_integerUpper (n : ℕ) (w : Tape n) :
    integerPosition n w ≤ integerUpper n w := by
  cases n with
  | zero => exact le_rfl
  | succ n => exact le_max_right _ _

theorem integerLower_le_upper (n : ℕ) (w : Tape n) :
    integerLower n w ≤ integerUpper n w :=
  (integerLower_le_position n w).trans (position_le_integerUpper n w)

/-- Every position up to the horizon lies in the actual attained integer range. -/
theorem prefix_position_bounds (w : ℕ → Fin 4) (n t : ℕ) (ht : t ≤ n) :
    integerLower n (prefixTape n w) ≤ integerPosition t (prefixTape t w) ∧
    integerPosition t (prefixTape t w) ≤ integerUpper n (prefixTape n w) := by
  induction n with
  | zero =>
    have he : t = 0 := by omega
    subst t
    exact ⟨le_rfl, le_rfl⟩
  | succ n ih =>
    by_cases he : t = n + 1
    · subst t
      exact ⟨integerLower_le_position _ _, position_le_integerUpper _ _⟩
    · obtain ⟨hl, hu⟩ := ih (by omega)
      dsimp [prefixTape, integerLower, integerUpper, integerRun]
      exact ⟨(min_le_left _ _).trans hl, hu.trans (le_max_left _ _)⟩

/-- The recorded upper endpoint really is attained by a prefix position. -/
theorem prefix_upper_attained (w : ℕ → Fin 4) (n : ℕ) :
    ∃ t ≤ n, integerPosition t (prefixTape t w) = integerUpper n (prefixTape n w) := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    by_cases h : integerUpper n (prefixTape n w) ≤ integerPosition (n + 1) (prefixTape (n + 1) w)
    · refine ⟨n + 1, le_rfl, ?_⟩
      exact (max_eq_right h).symm
    · obtain ⟨t, ht, he⟩ := ih
      refine ⟨t, by omega, ?_⟩
      exact he.trans (max_eq_left (le_of_not_ge h)).symm

/-- The recorded lower endpoint really is attained by a prefix position. -/
theorem prefix_lower_attained (w : ℕ → Fin 4) (n : ℕ) :
    ∃ t ≤ n, integerPosition t (prefixTape t w) = integerLower n (prefixTape n w) := by
  induction n with
  | zero => exact ⟨0, le_rfl, rfl⟩
  | succ n ih =>
    by_cases h : integerPosition (n + 1) (prefixTape (n + 1) w) ≤ integerLower n (prefixTape n w)
    · refine ⟨n + 1, le_rfl, ?_⟩
      exact (min_eq_right h).symm
    · obtain ⟨t, ht, he⟩ := ih
      refine ⟨t, by omega, ?_⟩
      exact he.trans (min_eq_left (le_of_not_ge h)).symm

def integerRange (n : ℕ) (w : Tape n) : ℕ :=
  (integerUpper n w - integerLower n w).toNat

theorem integerRange_cast (n : ℕ) (w : Tape n) :
    (integerRange n w : ℝ) = (run n w).upper - (run n w).lower := by
  have h := Int.toNat_of_nonneg (sub_nonneg.mpr (integerLower_le_upper n w))
  have hc : ((integerRange n w : ℕ) : ℤ) = integerUpper n w - integerLower n w := h
  have hr := congrArg (fun z : ℤ => (z : ℝ)) hc
  simpa only [Int.cast_natCast, Int.cast_sub, (integer_casts n w).2.1,
    (integer_casts n w).2.2] using hr

theorem integerRange_expect_le (n : ℕ) :
    expect (fun w : Tape n => (integerRange n w : ℝ)) ≤ 2 * Real.sqrt (2 * (n : ℝ)) := by
  simpa only [integerRange_cast] using range_expect_le n

end RandomWalkSearch.LazyWalk
