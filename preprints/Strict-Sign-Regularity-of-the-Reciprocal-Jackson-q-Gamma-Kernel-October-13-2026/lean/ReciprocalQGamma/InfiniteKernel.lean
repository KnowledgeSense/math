import ReciprocalQGamma.FiniteKernel
import ReciprocalQGamma.QBinomial
import Mathlib.Topology.Instances.Matrix

noncomputable section
open scoped BigOperators
open Filter Topology
namespace ReciprocalQGamma

theorem partialKernel_limit (q s t : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) (r : ℕ) :
    Tendsto (fun N => partialKernel q s t (r + N)) atTop
      (𝓝 (qBinomialSeries q (1 - s) t)) := by
  have hu0 : 0 ≤ 1 - s := by linarith
  have hu1 : 1 - s < 1 := by linarith
  have h := (qBinomialSeries_summable q (1 - s) t hq0.le hq1 hu0 hu1 ht0.le ht1).hasSum.tendsto_sum_nat
  have h' := h.comp (tendsto_add_atTop_nat r)
  simpa [partialKernel, qBinomialSeries, qBinomialCoefficient, Nat.add_comm, Function.comp_def] using h'

theorem qBinomial_kernel_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    {r : ℕ} (s t : Fin r → ℝ) (hs : StrictMono s) (ht : StrictMono t)
    (hs0 : ∀ i, 0 < s i) (hs1 : ∀ i, s i < 1)
    (ht0 : ∀ i, 0 < t i) (ht1 : ∀ i, t i < 1) :
    0 < Matrix.det (fun i j => qBinomialSeries q (1 - s i) (t j)) := by
  let M : Matrix (Fin r) (Fin r) ℝ := fun i j => qBinomialSeries q (1 - s i) (t j)
  have hm : Tendsto (fun N => (fun i j : Fin r => partialKernel q (s i) (t j) (r + N)))
      atTop (𝓝 M) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_pi_nhds.mpr
    intro j
    exact partialKernel_limit q (s i) (t j) hq0 hq1 (hs0 i) (hs1 i) (ht0 j) (ht1 j) r
  have hd := (continuous_id.matrix_det : Continuous (Matrix.det : Matrix (Fin r) (Fin r) ℝ → ℝ)).continuousAt.tendsto.comp hm
  have hlim := hd.const_mul (r.factorial : ℝ)
  have hb : firstMinor q s t ≤ (r.factorial : ℝ) * M.det :=
    ge_of_tendsto' hlim (partialKernel_det_lower_bound q hq0 hq1 s t hs ht hs0 ht0)
  exact pos_of_mul_pos_right (lt_of_lt_of_le (firstMinor_pos q hq0 hq1 s t hs ht hs0 ht0) hb)
    (by positivity)

/-- Strict positivity of every finite ordered minor of the transformed infinite-product kernel. -/
theorem qInfiniteProduct_kernel_pos (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    {r : ℕ} (s t : Fin r → ℝ) (hs : StrictMono s) (ht : StrictMono t)
    (hs0 : ∀ i, 0 < s i) (hs1 : ∀ i, s i < 1)
    (ht0 : ∀ i, 0 < t i) (ht1 : ∀ i, t i < 1) :
    0 < Matrix.det (fun i j => qInfiniteProduct q ((1 - s i) * t j)) := by
  have he : (fun i j : Fin r => qInfiniteProduct q ((1 - s i) * t j)) =
      Matrix.of (fun i j : Fin r => qInfiniteProduct q (t j) * qBinomialSeries q (1 - s i) (t j)) := by
    ext i j
    exact qBinomial_identity q (1 - s i) (t j) hq0 hq1 (by linarith [hs1 i])
      (by linarith [hs0 i]) (ht0 j) (ht1 j)
  rw [he, Matrix.det_mul_row (fun j : Fin r => qInfiniteProduct q (t j))
    (fun i j : Fin r => qBinomialSeries q (1 - s i) (t j))]
  exact mul_pos (Finset.prod_pos (fun j _ => qInfiniteProduct_pos q (t j) hq0.le hq1 (ht0 j).le (ht1 j)))
    (qBinomial_kernel_pos q hq0 hq1 s t hs ht hs0 hs1 ht0 ht1)

end ReciprocalQGamma
