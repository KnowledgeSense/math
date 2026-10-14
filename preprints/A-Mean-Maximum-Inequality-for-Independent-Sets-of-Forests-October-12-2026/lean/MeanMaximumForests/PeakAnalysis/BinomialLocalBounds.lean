import MeanMaximumForests.PeakAnalysis.BinomialComparison
import MeanMaximumForests.PeakAnalysis.BinomialMode
import MeanMaximumForests.PeakAnalysis.FiniteConcentration
import Mathlib.Algebra.Order.Floor.Ring

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset

/-- A uniform lower bound for every binomial mass in a fixed central window. -/
theorem binomial_central_mass_lower (n k : ℕ) (z r L : ℝ)
    (hz : (1 / 4 : ℝ) ≤ z) (hz1 : z ≤ 1) (hL : 1 ≤ L)
    (hr : 40 * (L + 1) ≤ r) (hrn : r ^ 2 = n)
    (hk : |(k : ℝ) - z * n / (1 + z)| ≤ L * r) :
    Real.exp (-(120 * L * (L + 1))) ≤ 6 * r * binomialSizeMass n z k := by
  have hz0 : 0 < z := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨j, hjn, hj, hmode⟩ := exists_binomial_mode n z hz0
  let j' : Fin (n + 1) := ⟨j, by omega⟩
  have hvar : 2 * (binomialSizeLaw n z hz0).variance (fun j => (j.val : ℝ)) ≤ r ^ 2 := by
    have h := binomialSizeLaw_variance_le n z hz0
    have hn0 := Nat.cast_nonneg (α := ℝ) n
    nlinarith only [h, hrn, hn0]
  have hml := finiteLaw_mode_mass_lower (binomialSizeLaw n z hz0) j'
    (fun i => hmode i.val) r hr1 hvar
  have hjwin : |(j : ℝ) - z * n / (1 + z)| ≤ L * r := hj.trans (one_le_mul_of_one_le_of_one_le hL hr1)
  have hc := binomial_central_mass_comparison n k j z r L hz hz1 hL0 hr hrn hk hjwin
  have hm := mul_le_mul_of_nonneg_left hml (Real.exp_pos (-(120 * L * (L + 1)))).le
  have hc' := mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ 6 * r)
  change _ * 1 ≤ _ * (6 * r * binomialSizeMass n z j) at hm
  nlinarith only [hm, hc']

theorem binomialSizeMass_sum_range (n : ℕ) (z : ℝ) (hz : 0 < z) :
    (∑ k ∈ range (n + 1), binomialSizeMass n z k) = 1 := by
  have h := (binomialSizeLaw n z hz).sum_one
  change (∑ k : Fin (n + 1), binomialSizeMass n z k.val) = 1 at h
  rw [Finset.sum_fin_eq_sum_range] at h
  convert h using 1
  apply sum_congr rfl
  intro k hk
  simp only [dite_eq_left (mem_range.mp hk)]

/-- A uniform upper bound on all binomial masses, with no restriction on the index. -/
theorem binomial_mass_upper_large (n k : ℕ) (z r : ℝ)
    (hz : (1 / 4 : ℝ) ≤ z) (hz1 : z ≤ 1) (hr : 120 ≤ r) (hrn : r ^ 2 = n) :
    r * binomialSizeMass n z k ≤ Real.exp 720 := by
  classical
  have hz0 : 0 < z := by linarith
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨j, hjn, hj, hmode⟩ := exists_binomial_mode n z hz0
  let T := Icc j (j + ⌊r⌋₊)
  have hfloor : (⌊r⌋₊ : ℝ) ≤ r := Nat.floor_le hr0
  have hsize : r ≤ (T.card : ℝ) := by
    dsimp [T]
    rw [Nat.card_Icc]
    have he : j + ⌊r⌋₊ + 1 - j = ⌊r⌋₊ + 1 := by omega
    rw [he, Nat.cast_add, Nat.cast_one]
    exact (Nat.lt_floor_add_one r).le
  have hjwin : |(j : ℝ) - z * n / (1 + z)| ≤ 2 * r := hj.trans (by linarith)
  have hiwin (i : ℕ) (hi : i ∈ T) : |(i : ℝ) - z * n / (1 + z)| ≤ 2 * r := by
    obtain ⟨hil, hiu⟩ := mem_Icc.mp hi
    have hil' : (j : ℝ) ≤ i := by exact_mod_cast hil
    have hiu' : (i : ℝ) ≤ j + (⌊r⌋₊ : ℝ) := by exact_mod_cast hiu
    rw [abs_le] at hj ⊢
    constructor <;> linarith [hj.1, hj.2]
  have hsub : T ⊆ range (n + 1) := by
    intro i hi
    have h := (binomial_central_log_step n i z r 2 hz hz1 (by norm_num)
      (by linarith) hrn (hiwin i hi)).1
    exact mem_range.mpr (by omega)
  have hl (i : ℕ) (hi : i ∈ T) : Real.exp (-720) * binomialSizeMass n z j ≤ binomialSizeMass n z i := by
    have h := binomial_central_mass_comparison n i j z r 2 hz hz1 (by norm_num)
      (by linarith) hrn (hiwin i hi) hjwin
    norm_num at h
    exact h
  have hsum := sum_le_sum (s := T) (f := fun _ => Real.exp (-720) * binomialSizeMass n z j)
    (g := binomialSizeMass n z) hl
  rw [sum_const, nsmul_eq_mul] at hsum
  have htotal : (∑ i ∈ T, binomialSizeMass n z i) ≤ 1 := by
    rw [← binomialSizeMass_sum_range n z hz0]
    apply sum_le_sum_of_subset_of_nonneg hsub
    intro i _ _
    unfold binomialSizeMass
    positivity
  have hs := mul_le_mul_of_nonneg_right hsize
    (mul_nonneg (Real.exp_pos (-720)).le (binomialSizeMass_pos n j z hz0 hjn).le)
  have hsmall : r * (Real.exp (-720) * binomialSizeMass n z j) ≤ 1 := hs.trans (hsum.trans htotal)
  have hbig := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos 720).le
  have he : Real.exp 720 * Real.exp (-720) = 1 := by rw [← Real.exp_add]; norm_num
  have hbj : r * binomialSizeMass n z j ≤ Real.exp 720 := by
    calc
      _ = Real.exp 720 * (r * (Real.exp (-720) * binomialSizeMass n z j)) := by
        calc
          _ = (Real.exp 720 * Real.exp (-720)) * (r * binomialSizeMass n z j) := by rw [he, one_mul]
          _ = _ := by ring
      _ ≤ _ := by simpa only [mul_one] using hbig
  exact (mul_le_mul_of_nonneg_left (hmode k) hr0).trans hbj

end MeanMaximumForests.PeakAnalysis
