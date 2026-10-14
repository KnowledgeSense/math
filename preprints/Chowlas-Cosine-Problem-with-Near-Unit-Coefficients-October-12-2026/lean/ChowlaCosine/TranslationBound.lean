import ChowlaCosine.SelectorPairing
import ChowlaCosine.PaperPairingUpper

namespace ChowlaCosine
open MeasureTheory AddCircle

/-- The release's single-translation estimate, with every analytic input proved. -/
theorem single_translation_bound {A : Finset ℤ} {s : ℤ → ℝ} {K : ℝ} (t : ℤ)
    (hne : A.Nonempty) (h0 : 0 ∉ A) (hA : ∀ a, -a ∈ A ↔ a ∈ A)
    (hs : ∀ a ∈ A, s (-a) = s a)
    (hcoeff : ∀ a ∈ A, s a ∈ Set.Icc (0.99 : ℝ) 1.01)
    (hlower : ∀ x, -K ≤ (polynomial A s x).re) :
    ((5.27 : ℝ)*0.99^4-4.86*1.01^4) * (B A t).card ≤
      12.86*(1.01^2/100)^2*(C A t).card + 5408*K^8 := by
  obtain ⟨a, ha⟩ := hne
  have hKa := polynomial_coefficient_le h0 hA hs hlower ha
  have hK : 0 ≤ K := by linarith [(hcoeff a ha).1, le_abs_self (s a)]
  have hlo := selector_pairing_lower t hA hs hcoeff
  have hup := paper_pairing_upper t h0 hA hs hcoeff hK hlower
  have hpair := hlo.trans hup
  have hL2 := selector_integral_norm_sq_le t hcoeff
  have hL1 := selector_integral_norm_le t ⟨a, ha⟩ h0 hA hs hcoeff hlower
  have hL10 : 0 ≤ ∫ x, ‖selector A s t x‖ ∂haarAddCircle :=
    integral_nonneg (fun _ => norm_nonneg _)
  have hL1sq := (sq_le_sq₀ hL10 (show 0 ≤ 13*K^3 by positivity)).2 hL1
  have hscaled1 := mul_le_mul_of_nonneg_left hL1sq (show 0 ≤ 32*K^2 by positivity)
  have hscaled2 := mul_le_mul_of_nonneg_left hL2 (show (0:ℝ) ≤ 4.86 by norm_num)
  have hpower : 32*K^2*(13*K^3)^2 = 5408*K^8 := by ring
  rw [hpower] at hscaled1
  linarith

end ChowlaCosine
