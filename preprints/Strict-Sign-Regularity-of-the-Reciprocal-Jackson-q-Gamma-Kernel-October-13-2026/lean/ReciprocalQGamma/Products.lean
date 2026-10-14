import ReciprocalQGamma.Definitions

noncomputable section
open scoped BigOperators
open Filter Topology
namespace ReciprocalQGamma

theorem qProduct_zero (q a : ℝ) : qProduct q a 0 = 1 := by simp [qProduct]

theorem qProduct_succ (q a : ℝ) (n : ℕ) :
    qProduct q a (n + 1) = qProduct q a n * (1 - a * q ^ n) := by
  simp [qProduct, Finset.prod_range_succ]

theorem qFactor_pos (q a : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (n : ℕ) : 0 < 1 - a * q ^ n := by
  have hpow : q ^ n ≤ 1 := pow_le_one₀ hq0 hq1
  have h := mul_le_mul_of_nonneg_left hpow ha0
  nlinarith

theorem qProduct_pos (q a : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (n : ℕ) : 0 < qProduct q a n := by
  exact Finset.prod_pos (fun j _ => qFactor_pos q a hq0 hq1 ha0 ha1 j)

theorem qProduct_le_one (q a : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (n : ℕ) : qProduct q a n ≤ 1 := by
  apply Finset.prod_le_one₀
  · intro j _; exact (qFactor_pos q a hq0 hq1 ha0 ha1 j).le
  · intro j _
    have : 0 ≤ a * q ^ j := by positivity
    linarith

theorem qLog_summable (q a : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun j : ℕ => Real.log (1 - a * q ^ j)) := by
  simpa only [sub_eq_add_neg, neg_mul] using
    Real.summable_log_one_add_of_summable
      ((summable_geometric_of_lt_one hq0 hq1).mul_left (-a))

theorem qInfiniteProduct_pos (q a : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) : 0 < qInfiniteProduct q a := by
  rw [qInfiniteProduct, ← Real.rexp_tsum_eq_tprod
    (qFactor_pos q a hq0 hq1.le ha0 ha1) (qLog_summable q a hq0 hq1)]
  exact Real.exp_pos _

theorem qFactors_multipliable (q a : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) : Multipliable (fun j : ℕ => 1 - a * q ^ j) :=
  Real.multipliable_of_summable_log (qFactor_pos q a hq0 hq1.le ha0 ha1)
    (qLog_summable q a hq0 hq1)

theorem qProduct_limit (q a : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Tendsto (qProduct q a) atTop (𝓝 (qInfiniteProduct q a)) :=
  (qFactors_multipliable q a hq0 hq1 ha0 ha1).hasProd.tendsto_prod_nat

theorem qProduct_antitone (q a : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) : Antitone (qProduct q a) := by
  apply antitone_nat_of_succ_le
  intro n
  rw [qProduct_succ]
  apply mul_le_of_le_one_right (qProduct_pos q a hq0 hq1 ha0 ha1 n).le
  have : 0 ≤ a * q ^ n := by positivity
  linarith

theorem qInfiniteProduct_le_partial (q a : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (ha0 : 0 ≤ a) (ha1 : a < 1) (n : ℕ) : qInfiniteProduct q a ≤ qProduct q a n :=
  (qProduct_antitone q a hq0 hq1.le ha0 ha1).le_of_tendsto
    (qProduct_limit q a hq0 hq1 ha0 ha1) n

end ReciprocalQGamma
