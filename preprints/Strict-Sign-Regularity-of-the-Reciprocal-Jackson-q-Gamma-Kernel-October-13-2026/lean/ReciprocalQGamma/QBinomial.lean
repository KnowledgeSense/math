import ReciprocalQGamma.Products
import Mathlib.Analysis.Normed.Group.Tannery

noncomputable section
open scoped BigOperators
open Filter Topology
namespace ReciprocalQGamma

def qBinomialCoefficient (q u : ℝ) (k : ℕ) : ℝ :=
  qProduct q u k / qProduct q q k

def qBinomialSeries (q u v : ℝ) : ℝ :=
  ∑' k : ℕ, qBinomialCoefficient q u k * v ^ k

lemma qBinomialCoefficient_zero (q u : ℝ) : qBinomialCoefficient q u 0 = 1 := by
  simp [qBinomialCoefficient, qProduct_zero]

lemma qBinomialCoefficient_pos (q u : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (k : ℕ) : 0 < qBinomialCoefficient q u k :=
  div_pos (qProduct_pos q u hq0 hq1.le hu0 hu1 k)
    (qProduct_pos q q hq0 hq1.le hq0 hq1 k)

lemma qBinomialCoefficient_le (q u : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (k : ℕ) :
    qBinomialCoefficient q u k ≤ 1 / qInfiniteProduct q q := by
  have hpos := qInfiniteProduct_pos q q hq0 hq1 hq0 hq1
  have hp := qProduct_pos q q hq0 hq1.le hq0 hq1 k
  exact div_le_div₀ (by norm_num)
    (qProduct_le_one q u hq0 hq1.le hu0 hu1 k) hpos
    (qInfiniteProduct_le_partial q q hq0 hq1 hq0 hq1 k)

lemma qBinomialCoefficient_recurrence (q u : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (k : ℕ) : qBinomialCoefficient q u (k+1) * (1-q^(k+1)) =
      qBinomialCoefficient q u k * (1-u*q^k) := by
  have h0 := (qProduct_pos q q hq0 hq1.le hq0 hq1 k).ne'
  have h1 := (qFactor_pos q q hq0 hq1.le hq0 hq1 k).ne'
  unfold qBinomialCoefficient
  rw [qProduct_succ, qProduct_succ, pow_succ']
  have h1' : 1 - q^k*q ≠ 0 := by simpa [mul_comm] using h1
  field_simp

lemma qBinomialSeries_summable (q u v : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    Summable (fun k : ℕ => qBinomialCoefficient q u k * v^k) := by
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (qBinomialCoefficient_pos q u hq0 hq1 hu0 hu1 k).le
      (pow_nonneg hv0 k))
    (fun k => mul_le_mul_of_nonneg_right
      (qBinomialCoefficient_le q u hq0 hq1 hu0 hu1 k) (pow_nonneg hv0 k))
  exact (summable_geometric_of_lt_one hv0 hv1).mul_left _

lemma qBinomialSeries_functional (q u v : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    (1-v) * qBinomialSeries q u v = (1-u*v) * qBinomialSeries q u (q*v) := by
  have hqv0 : 0 ≤ q*v := mul_nonneg hq0 hv0
  have hqv1 : q*v < 1 := lt_of_le_of_lt (mul_le_of_le_one_left hv0 hq1.le) hv1
  have hs := qBinomialSeries_summable q u v hq0 hq1 hu0 hu1 hv0 hv1
  have ht := qBinomialSeries_summable q u (q*v) hq0 hq1 hu0 hu1 hqv0 hqv1
  have he (k : ℕ) :
      qBinomialCoefficient q u (k+1)*v^(k+1) -
        qBinomialCoefficient q u (k+1)*(q*v)^(k+1) =
      v*(qBinomialCoefficient q u k*v^k-u*(qBinomialCoefficient q u k*(q*v)^k)) := by
    have h := qBinomialCoefficient_recurrence q u hq0 hq1 k
    rw [mul_pow, mul_pow]
    rw [pow_succ v]
    nlinarith [congrArg (fun z : ℝ => z * v^k * v) h]
  have hd := (hs.sub ht).tsum_eq_zero_add
  simp only [pow_zero, mul_one, sub_self, zero_add] at hd
  have hsum : qBinomialSeries q u v - qBinomialSeries q u (q*v) =
      v*(qBinomialSeries q u v-u*qBinomialSeries q u (q*v)) := by
    unfold qBinomialSeries
    rw [← hs.tsum_sub ht, hd]
    simp_rw [he]
    rw [tsum_mul_left, hs.tsum_sub (ht.mul_left u), tsum_mul_left]
  nlinarith

lemma qBinomialSeries_zero (q u : ℝ) : qBinomialSeries q u 0 = 1 := by
  unfold qBinomialSeries
  rw [tsum_eq_single 0]
  · simp [qBinomialCoefficient_zero]
  · intro k hk
    simp [zero_pow hk]

lemma qBinomialSeries_limit (q u v : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) :
    Tendsto (fun n : ℕ => qBinomialSeries q u (v*q^n)) atTop (𝓝 1) := by
  have hc : 0 < 1 / qInfiniteProduct q q :=
    one_div_pos.mpr (qInfiniteProduct_pos q q hq0 hq1 hq0 hq1)
  have hp : Tendsto (fun n : ℕ => v*q^n) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1) :
      Tendsto (fun n : ℕ => v*q^n) atTop (𝓝 (v*0)))
  have hh := tendsto_tsum_of_dominated_convergence
    ((summable_geometric_of_lt_one hv0 hv1).mul_left (1 / qInfiniteProduct q q))
    (fun k : ℕ => (tendsto_const_nhds.mul (hp.pow k) :
      Tendsto (fun n : ℕ => qBinomialCoefficient q u k * (v*q^n)^k) atTop
        (𝓝 (qBinomialCoefficient q u k * (0 : ℝ)^k))))
    (Filter.Eventually.of_forall (fun n k => show
      ‖qBinomialCoefficient q u k * (v*q^n)^k‖ ≤
        (1 / qInfiniteProduct q q) * v^k from by
      have hbase : 0 ≤ v*q^n := mul_nonneg hv0 (pow_nonneg hq0 n)
      rw [Real.norm_eq_abs, abs_of_nonneg
        (mul_nonneg (qBinomialCoefficient_pos q u hq0 hq1 hu0 hu1 k).le
          (pow_nonneg hbase k))]
      apply mul_le_mul (qBinomialCoefficient_le q u hq0 hq1 hu0 hu1 k)
      · exact pow_le_pow_left₀ hbase (mul_le_of_le_one_right hv0 (pow_le_one₀ hq0 hq1.le)) k
      · exact pow_nonneg hbase k
      · exact hc.le))
  change Tendsto (fun n : ℕ => qBinomialSeries q u (v*q^n)) atTop
    (𝓝 (qBinomialSeries q u 0)) at hh
  simpa only [qBinomialSeries_zero] using hh

lemma qBinomialSeries_iterate (q u v : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hu0 : 0 ≤ u) (hu1 : u < 1) (hv0 : 0 ≤ v) (hv1 : v < 1) (n : ℕ) :
    qProduct q v n * qBinomialSeries q u v =
      qProduct q (u*v) n * qBinomialSeries q u (v*q^n) := by
  induction n with
  | zero => simp [qProduct_zero]
  | succ n ih =>
    have hvq0 : 0 ≤ v*q^n := mul_nonneg hv0 (pow_nonneg hq0 n)
    have hvq1 : v*q^n < 1 := lt_of_le_of_lt
      (mul_le_of_le_one_right hv0 (pow_le_one₀ hq0 hq1.le)) hv1
    have hf := qBinomialSeries_functional q u (v*q^n) hq0 hq1 hu0 hu1 hvq0 hvq1
    have he : q*(v*q^n) = v*q^(n+1) := by ring
    rw [he] at hf
    rw [qProduct_succ, qProduct_succ]
    calc
      qProduct q v n * (1-v*q^n) * qBinomialSeries q u v =
        (1-v*q^n) * (qProduct q v n * qBinomialSeries q u v) := by ring
      _ = (1-v*q^n) * (qProduct q (u*v) n * qBinomialSeries q u (v*q^n)) := by rw [ih]
      _ = qProduct q (u*v) n * ((1-v*q^n) * qBinomialSeries q u (v*q^n)) := by ring
      _ = qProduct q (u*v) n * ((1-u*(v*q^n)) * qBinomialSeries q u (v*q^(n+1))) := by rw [hf]
      _ = _ := by ring

theorem qBinomial_identity (q u v : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    qInfiniteProduct q (u*v) = qInfiniteProduct q v *
      ∑' k : ℕ, qProduct q u k / qProduct q q k * v^k := by
  have huv0 : 0 ≤ u*v := (mul_pos hu0 hv0).le
  have huv1 : u*v < 1 := lt_of_le_of_lt (mul_le_of_le_one_left hv0.le hu1.le) hv1
  have hl := (qProduct_limit q v hq0.le hq1 hv0.le hv1).mul_const
    (qBinomialSeries q u v)
  have hr := (qProduct_limit q (u*v) hq0.le hq1 huv0 huv1).mul
    (qBinomialSeries_limit q u v hq0.le hq1 hu0.le hu1 hv0.le hv1)
  have he : (fun n => qProduct q v n * qBinomialSeries q u v) =
      (fun n => qProduct q (u*v) n * qBinomialSeries q u (v*q^n)) := by
    funext n
    exact qBinomialSeries_iterate q u v hq0.le hq1 hu0.le hu1 hv0.le hv1 n
  rw [he] at hl
  have h := tendsto_nhds_unique hl hr
  simpa [qBinomialSeries, qBinomialCoefficient] using h.symm

end ReciprocalQGamma
