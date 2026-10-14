import SphericalTreeFailures.EnvelopeConvergence

namespace SphericalTreeFailures

 theorem scaledEnvelope_nonneg (m k : ℕ) (r t : ℝ) : 0 ≤ scaledEnvelope m k r t :=
  rawEnvelope_nonneg _ _ _ _

theorem scaledEnvelope_iterate (k : ℕ) {r : ℝ} (hr : 0 < r)
    (htune : tunedActivity r * pathPartition (2 * k) (tunedActivity r) =
      r * pathPartition (2 * k + 1) (tunedActivity r)) (h j : ℕ) (t : ℝ) :
    scaledEnvelope (h + j) k r t ≤ scaledEnvelope h k r (t / fluctuationScale r ^ j) ^ (2 ^ j) := by
  induction j generalizing t with
  | zero => simp
  | succ j ih =>
    have hs := scaledEnvelope_succ k hr htune (h + j) t
    have hi := pow_le_pow_left₀ (scaledEnvelope_nonneg (h + j) k r (t / fluctuationScale r))
      (ih (t / fluctuationScale r)) 2
    have he : (t / fluctuationScale r) / fluctuationScale r ^ j = t / fluctuationScale r ^ (j + 1) := by
      rw [pow_succ, div_div]
      congr 1
      ring
    simpa only [Nat.add_assoc, he, ← pow_mul, ← pow_succ] using hs.trans hi

theorem scaledEnvelope_iterate_bound (k : ℕ) {r ρ : ℝ} (hr : 0 < r)
    (htune : tunedActivity r * pathPartition (2 * k) (tunedActivity r) =
      r * pathPartition (2 * k + 1) (tunedActivity r)) (h j : ℕ) (t : ℝ)
    (hb : scaledEnvelope h k r (t / fluctuationScale r ^ j) ≤ ρ) :
    scaledEnvelope (h + j) k r t ≤ ρ ^ (2 ^ j) :=
  (scaledEnvelope_iterate k hr htune h j t).trans
    (pow_le_pow_left₀ (scaledEnvelope_nonneg _ _ _ _) hb _)

end SphericalTreeFailures
