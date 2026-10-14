import SphericalTreeFailures.EnvelopeIteration
import Mathlib.Topology.Order.Compact

namespace SphericalTreeFailures
open Set Filter
open scoped Topology

def frequencyAnnulus (R : ℝ) : Set ℝ := {t | 1 ≤ |t| ∧ |t| ≤ R}

theorem frequencyAnnulus_compact (R : ℝ) : IsCompact (frequencyAnnulus R) := by
  apply (isCompact_Icc : IsCompact (Icc (-R) R)).of_isClosed_subset
  · exact (isClosed_le continuous_const continuous_abs).inter (isClosed_le continuous_abs continuous_const)
  · intro t ht
    exact abs_le.mp ht.2

theorem frequencyAnnulus_nonempty {R : ℝ} (hR : 1 ≤ R) : (frequencyAnnulus R).Nonempty :=
  ⟨1, by simpa [frequencyAnnulus] using hR⟩

theorem compact_annulus_contraction {R : ℝ} (hR : 1 ≤ R) {F : ℝ → ℝ} (hF : Continuous F)
    (h0 : ∀ t ∈ frequencyAnnulus R, 0 ≤ F t) (h1 : ∀ t ∈ frequencyAnnulus R, F t < 1) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∀ t ∈ frequencyAnnulus R, F t ≤ ρ := by
  obtain ⟨t, ht, hmax⟩ := (frequencyAnnulus_compact R).exists_isMaxOn
    (frequencyAnnulus_nonempty hR) hF.continuousOn
  refine ⟨(1 + F t) / 2, ?_, ?_, ?_⟩
  · have := h0 t ht
    linarith
  · have := h1 t ht
    linarith
  · intro s hs
    have hm : F s ≤ F t := hmax hs
    have := h1 t ht
    linarith

theorem release_annulus_eventual_bound (k : ℕ) (hk : 16384 ≤ k)
    {R ρ : ℝ} (hρ : ρ < 1)
    (hb : ∀ t ∈ frequencyAnnulus R,
      censusEnvelope (releaseBroadcastParameter k hk) (tailShift k (releaseParameter k hk) * t) ≤ ρ) :
    ∀ᶠ m in atTop, ∀ t ∈ frequencyAnnulus R,
      scaledEnvelope m k (releaseParameter k hk) t ≤ (1 + ρ) / 2 := by
  have he : 0 < (1 - ρ) / 2 := by linarith
  filter_upwards [release_scaledEnvelope_uniform k hk R ((1 - ρ) / 2) he] with m hm
  intro t ht
  have h := hm t ht.2
  have hd := le_abs_self (scaledEnvelope m k (releaseParameter k hk) t -
    censusEnvelope (releaseBroadcastParameter k hk) (tailShift k (releaseParameter k hk) * t))
  have hh := hb t ht
  linarith

end SphericalTreeFailures
