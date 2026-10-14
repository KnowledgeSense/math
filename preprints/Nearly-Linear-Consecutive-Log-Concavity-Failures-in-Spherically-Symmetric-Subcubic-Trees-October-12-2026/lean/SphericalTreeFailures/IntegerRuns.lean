import SphericalTreeFailures.CurvatureLimit
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring

namespace SphericalTreeFailures

noncomputable def latticeInterval (u H a b : ℝ) : Finset ℤ :=
  Finset.Icc ⌈u + H * a⌉ ⌊u + H * b⌋

theorem mem_latticeInterval {u H a b : ℝ} (hH : 0 < H) (j : ℤ) :
    j ∈ latticeInterval u H a b ↔ a ≤ ((j : ℝ) - u) / H ∧ ((j : ℝ) - u) / H ≤ b := by
  rw [latticeInterval, Finset.mem_Icc, Int.ceil_le, Int.le_floor,
    le_div_iff₀ hH, div_le_iff₀ hH]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> nlinarith

theorem latticeInterval_consecutive {u H a b : ℝ} {i j l : ℤ}
    (hi : i ∈ latticeInterval u H a b) (hl : l ∈ latticeInterval u H a b)
    (hij : i ≤ j) (hjl : j ≤ l) : j ∈ latticeInterval u H a b := by
  simp only [latticeInterval, Finset.mem_Icc] at *
  exact ⟨hi.1.trans hij, hjl.trans hl.2⟩

theorem latticeInterval_card_lower (u H a b : ℝ) :
    H * (b - a) - 1 ≤ ((latticeInterval u H a b).card : ℝ) := by
  have hf := Int.sub_one_lt_floor (u + H * b)
  have hc := Int.ceil_lt_add_one (u + H * a)
  have hn : (⌊u + H * b⌋ + 1 - ⌈u + H * a⌉ : ℤ) ≤
      ((⌊u + H * b⌋ + 1 - ⌈u + H * a⌉).toNat : ℤ) := by omega
  have hn' : (⌊u + H * b⌋ : ℝ) + 1 - (⌈u + H * a⌉ : ℝ) ≤
      ((latticeInterval u H a b).card : ℝ) := by
    unfold latticeInterval
    rw [Int.card_Icc]
    exact_mod_cast hn
  nlinarith

noncomputable def reflectedLeft (m : ℕ) (a b : ℝ) : ℝ :=
  if (-1 : ℝ) ^ m = 1 then a else -b
noncomputable def reflectedRight (m : ℕ) (a b : ℝ) : ℝ :=
  if (-1 : ℝ) ^ m = 1 then b else -a

theorem reflected_interval (m : ℕ) (a b x : ℝ) :
    reflectedLeft m a b ≤ x ∧ x ≤ reflectedRight m a b ↔
      a ≤ (-1 : ℝ) ^ m * x ∧ (-1 : ℝ) ^ m * x ≤ b := by
  rcases neg_one_pow_eq_or (R := ℝ) m with h | h
  · simp [reflectedLeft, reflectedRight, h]
  · simp only [reflectedLeft, reflectedRight, h, neg_one_mul]
    norm_num
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

theorem reflected_length (m : ℕ) (a b : ℝ) :
    reflectedRight m a b - reflectedLeft m a b = b - a := by
  unfold reflectedLeft reflectedRight
  split_ifs <;> ring

noncomputable def releaseRun (k : ℕ) (hk : 16384 ≤ k) (a b : ℝ) (m : ℕ) : Finset ℤ :=
  latticeInterval (releaseCenter k hk m) (releaseScale k hk m)
    (reflectedLeft m a b) (reflectedRight m a b)

theorem mem_releaseRun (k : ℕ) (hk : 16384 ≤ k) (a b : ℝ) (m : ℕ) (j : ℤ) :
    j ∈ releaseRun k hk a b m ↔
      (-1 : ℝ) ^ m * releaseGrid k hk m j ∈ Set.Icc a b := by
  rw [releaseRun, mem_latticeInterval (releaseScale_pos k hk m), reflected_interval]
  rfl

theorem releaseRun_card_lower (k : ℕ) (hk : 16384 ≤ k) (a b : ℝ) (m : ℕ) :
    releaseScale k hk m * (b - a) - 1 ≤ ((releaseRun k hk a b m).card : ℝ) := by
  have h := latticeInterval_card_lower (releaseCenter k hk m) (releaseScale k hk m)
    (reflectedLeft m a b) (reflectedRight m a b)
  rwa [reflected_length] at h

end SphericalTreeFailures
