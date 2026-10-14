import ArithmeticSections.TailGrowth

namespace ArithmeticSections

variable {b : ℕ → ℕ} (hb : ∀ n, 1 ≤ b (n + 1))
include hb

theorem denominator_mono_step (n : ℕ) : denominator b n ≤ denominator b (n + 1) := by
  induction n with
  | zero => simpa [denominator] using hb 0
  | succ n hn =>
    change denominator b (n + 1) ≤ b (n + 2) * denominator b (n + 1) + denominator b n
    have h := hb (n + 1)
    nlinarith

theorem denominator_two_step (n : ℕ) : 2 * denominator b n ≤ denominator b (n + 2) := by
  have h := denominator_mono_step hb n
  have h' := hb (n + 1)
  rw [denominator]
  nlinarith

/-- Equation (2.3), over all positive digit sequences. -/
theorem exponential_le_denominator (n : ℕ) : 2 ^ (n / 2) ≤ denominator b n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [denominator]
  | one => simpa [denominator] using hb 0
  | more n hn _ =>
    have he : (n + 2) / 2 = n / 2 + 1 := by omega
    rw [he, pow_succ]
    have hd := denominator_two_step hb n
    omega

theorem tailThreshold_lt_denominator (j : ℕ) (hj : 256 ≤ j) :
    72 * tailThreshold j < denominator b j :=
  lt_of_lt_of_le (tailThreshold_lt_exponential j hj) (exponential_le_denominator hb j)

theorem denominator_succ_le (n : ℕ) (hn : 1 ≤ n) :
    denominator b (n + 1) ≤ (b (n + 1) + 1) * denominator b n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := denominator_mono_step hb k
  change b (k + 2) * denominator b (k + 1) + denominator b k ≤
    (b (k + 2) + 1) * denominator b (k + 1)
  nlinarith

/-- The four-factor bound in Proposition 4.2. -/
theorem denominator_distortion (j : ℕ) (hj : 256 ≤ j)
    (hdigits : ∀ l, 257 ≤ l → b l ≤ l ^ 2) :
    denominator b (j + 3) * (b (j + 4) + 2) ≤ tailThreshold j * denominator b j := by
  let B := (j + 4) ^ 2 + 2
  have hb1 : b (j + 1) + 1 ≤ B := by
    have h := hdigits (j + 1) (by omega)
    dsimp [B]
    nlinarith
  have hb2 : b (j + 2) + 1 ≤ B := by
    have h := hdigits (j + 2) (by omega)
    dsimp [B]
    nlinarith
  have hb3 : b (j + 3) + 1 ≤ B := by
    have h := hdigits (j + 3) (by omega)
    dsimp [B]
    nlinarith
  have hb4 : b (j + 4) + 2 ≤ B := by
    have h := hdigits (j + 4) (by omega)
    dsimp [B]
    omega
  have hq1 : denominator b (j + 1) ≤ B * denominator b j :=
    le_trans (denominator_succ_le hb j (by omega)) (Nat.mul_le_mul_right _ hb1)
  have hq2 : denominator b (j + 2) ≤ B ^ 2 * denominator b j := by
    calc
      denominator b (j + 2) ≤ (b (j + 2) + 1) * denominator b (j + 1) :=
        denominator_succ_le hb (j + 1) (by omega)
      _ ≤ B * (B * denominator b j) := Nat.mul_le_mul hb2 hq1
      _ = B ^ 2 * denominator b j := by ring
  have hq3 : denominator b (j + 3) ≤ B ^ 3 * denominator b j := by
    calc
      denominator b (j + 3) ≤ (b (j + 3) + 1) * denominator b (j + 2) :=
        denominator_succ_le hb (j + 2) (by omega)
      _ ≤ B * (B ^ 2 * denominator b j) := Nat.mul_le_mul hb3 hq2
      _ = B ^ 3 * denominator b j := by ring
  calc
    denominator b (j + 3) * (b (j + 4) + 2) ≤ (B ^ 3 * denominator b j) * B :=
      Nat.mul_le_mul hq3 hb4
    _ = tailThreshold j * denominator b j := by unfold tailThreshold; dsimp [B]; ring

end ArithmeticSections
