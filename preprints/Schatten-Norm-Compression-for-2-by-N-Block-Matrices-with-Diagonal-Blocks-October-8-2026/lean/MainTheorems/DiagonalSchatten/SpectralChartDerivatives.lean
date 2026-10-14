import MainTheorems.DiagonalSchatten.SpectralJacobian
import MainTheorems.DiagonalSchatten.NormalizedDerivative

namespace ResearchMain.DiagonalSchatten

noncomputable section

def spectralChartScale (p t w : ℝ) : ℝ :=
  ((1 + t ^ 2) * (1 + w ^ 2)) ^ ((p - 2) / 2)

def spectralChartGradient (p h t w : ℝ) (j : Fin 4) : ℝ :=
  spectralChartScale p t w * spectralChartEntries t w (h ^ (p - 1)) j /
    spectralChartEntries t w h j ^ (p - 1)

theorem spectralChartEntries_deriv_t (h t w : ℝ) (j : Fin 4) :
    HasDerivAt (fun x => spectralChartEntries x w h j) (spectralChartTangentT w h j) t := by
  fin_cases j
  · change HasDerivAt (fun x => 1 + h * x * w) (h * w) t
    convert! (hasDerivAt_const t (1 : ℝ)).add
      (((hasDerivAt_id t).const_mul h).mul_const w) using 1
    ring
  · change HasDerivAt (fun x => x - h * w) 1 t
    exact (hasDerivAt_id t).sub_const (h * w)
  · change HasDerivAt (fun x => w - h * x) (-h) t
    convert! (hasDerivAt_const t w).sub ((hasDerivAt_id t).const_mul h) using 1
    ring
  · change HasDerivAt (fun x => x * w + h) w t
    simpa only [id_eq, one_mul] using ((hasDerivAt_id t).mul_const w).add_const h

theorem spectralChartEntries_deriv_w (h t w : ℝ) (j : Fin 4) :
    HasDerivAt (fun x => spectralChartEntries t x h j) (spectralChartTangentW t h j) w := by
  fin_cases j
  · change HasDerivAt (fun x => 1 + h * t * x) (h * t) w
    convert! (hasDerivAt_const w (1 : ℝ)).add
      ((hasDerivAt_id w).const_mul (h * t)) using 1
    ring
  · change HasDerivAt (fun x => t - h * x) (-h) w
    convert! (hasDerivAt_const w t).sub ((hasDerivAt_id w).const_mul h) using 1
    ring
  · change HasDerivAt (fun x => x - h * t) 1 w
    exact (hasDerivAt_id w).sub_const (h * t)
  · change HasDerivAt (fun x => t * x + h) t w
    convert! ((hasDerivAt_id w).const_mul t).add_const h using 1
    ring

theorem spectralChartEntries_deriv_h (h t w : ℝ) (j : Fin 4) :
    HasDerivAt (fun x => spectralChartEntries t w x j) (spectralChartTangentH t w j) h := by
  fin_cases j
  · change HasDerivAt (fun x => 1 + x * t * w) (t * w) h
    convert! (hasDerivAt_const h (1 : ℝ)).add
      (((hasDerivAt_id h).mul_const t).mul_const w) using 1
    ring
  · change HasDerivAt (fun x => t - x * w) (-w) h
    convert! (hasDerivAt_const h t).sub ((hasDerivAt_id h).mul_const w) using 1
    ring
  · change HasDerivAt (fun x => w - x * t) (-t) h
    convert! (hasDerivAt_const h w).sub ((hasDerivAt_id h).mul_const t) using 1
    ring
  · change HasDerivAt (fun x => t * w + x) 1 h
    exact (hasDerivAt_id h).const_add (t * w)

theorem spectralChartScale_deriv_t (p t w : ℝ) :
    HasDerivAt (fun x => spectralChartScale p x w)
      (spectralChartScale p t w * (p - 2) * t / (1 + t ^ 2)) t := by
  have hbase : HasDerivAt (fun x : ℝ => (1 + x ^ 2) * (1 + w ^ 2))
      (2 * t * (1 + w ^ 2)) t := by
    convert! (((hasDerivAt_id t).fun_pow 2).const_add 1).mul_const (1 + w ^ 2) using 1
    dsimp only [id_eq]
    ring
  have hp : 0 < (1 + t ^ 2) * (1 + w ^ 2) := by positivity
  convert! hbase.rpow_const (p := (p - 2) / 2) (Or.inl hp.ne') using 1
  rw [Real.rpow_sub hp, Real.rpow_one]
  unfold spectralChartScale
  field_simp [show 1 + t ^ 2 ≠ 0 by positivity, show 1 + w ^ 2 ≠ 0 by positivity]

theorem spectralChartScale_deriv_w (p t w : ℝ) :
    HasDerivAt (fun x => spectralChartScale p t x)
      (spectralChartScale p t w * (p - 2) * w / (1 + w ^ 2)) w := by
  have hbase : HasDerivAt (fun x : ℝ => (1 + t ^ 2) * (1 + x ^ 2))
      (2 * w * (1 + t ^ 2)) w := by
    convert! (((hasDerivAt_id w).fun_pow 2).const_add 1).const_mul (1 + t ^ 2) using 1
    dsimp only [id_eq]
    ring
  have hp : 0 < (1 + t ^ 2) * (1 + w ^ 2) := by positivity
  convert! hbase.rpow_const (p := (p - 2) / 2) (Or.inl hp.ne') using 1
  rw [Real.rpow_sub hp, Real.rpow_one]
  unfold spectralChartScale
  field_simp [show 1 + t ^ 2 ≠ 0 by positivity, show 1 + w ^ 2 ≠ 0 by positivity]

theorem spectralChartGradient_deriv_t (p h t w : ℝ) (j : Fin 4)
    (hpos : 0 < spectralChartEntries t w h j) :
    ∃ v, HasDerivAt (fun x => spectralChartGradient p h x w j) v t ∧
      (1 + t ^ 2) * v * spectralChartEntries t w h j ^ p =
        spectralChartScale p t w * normalizedSpectralJacobian p (h ^ (p - 1)) h t w 1 j := by
  obtain ⟨v, hd, hv⟩ := normalized_rpow_quotient_deriv
    (spectralChartScale_deriv_t p t w)
    (spectralChartEntries_deriv_t (h ^ (p - 1)) t w j)
    (spectralChartEntries_deriv_t h t w j) (q := p - 1) hpos
  rw [show p - 1 + 1 = p by ring] at hv
  refine ⟨v, hd, ?_⟩
  rw [mul_assoc, hv]
  simp [normalizedSpectralJacobian]
  field_simp [show 1 + t ^ 2 ≠ 0 by positivity]
  ring

theorem spectralChartGradient_deriv_w (p h t w : ℝ) (j : Fin 4)
    (hpos : 0 < spectralChartEntries t w h j) :
    ∃ v, HasDerivAt (fun x => spectralChartGradient p h t x j) v w ∧
      (1 + w ^ 2) * v * spectralChartEntries t w h j ^ p =
        spectralChartScale p t w * normalizedSpectralJacobian p (h ^ (p - 1)) h t w 2 j := by
  obtain ⟨v, hd, hv⟩ := normalized_rpow_quotient_deriv
    (spectralChartScale_deriv_w p t w)
    (spectralChartEntries_deriv_w (h ^ (p - 1)) t w j)
    (spectralChartEntries_deriv_w h t w j) (q := p - 1) hpos
  rw [show p - 1 + 1 = p by ring] at hv
  refine ⟨v, hd, ?_⟩
  rw [mul_assoc, hv]
  simp [normalizedSpectralJacobian]
  field_simp [show 1 + w ^ 2 ≠ 0 by positivity]
  ring

theorem spectralChartGradient_deriv_h (p t w : ℝ) {h : ℝ} (hh : 0 < h) (j : Fin 4)
    (hpos : 0 < spectralChartEntries t w h j) :
    ∃ v, HasDerivAt (fun x => spectralChartGradient p x t w j) v h ∧
      h * v * spectralChartEntries t w h j ^ p =
        spectralChartScale p t w * normalizedSpectralJacobian p (h ^ (p - 1)) h t w 0 j := by
  have hpow := (hasDerivAt_id h).rpow_const (p := p - 1) (Or.inl hh.ne')
  have hn := (spectralChartEntries_deriv_h (h ^ (p - 1)) t w j).comp h hpow
  obtain ⟨v, hd, hv⟩ := normalized_rpow_quotient_deriv
    (hasDerivAt_const h (spectralChartScale p t w)) hn
    (spectralChartEntries_deriv_h h t w j) (q := p - 1) hpos
  rw [show p - 1 + 1 = p by ring] at hv
  refine ⟨v, hd, ?_⟩
  rw [mul_assoc, hv]
  simp [normalizedSpectralJacobian]
  rw [Real.rpow_sub hh (p - 1) 1, Real.rpow_one]
  field_simp [hh.ne']

end

end ResearchMain.DiagonalSchatten
