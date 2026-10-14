import MainTheorems.Chollet.Congruence
import MainTheorems.Chollet.BorderIdentities
import MainTheorems.Chollet.Regularization

noncomputable section

namespace ResearchMain.Chollet

open Matrix

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem border_row_zero (a : ℝ) (z : I → ℂ) (B : Matrix I I ℂ) :
    (∑ j ∈ Finset.univ.erase (Sum.inl () : Unit ⊕ I),
      ‖border a z B (Sum.inl ()) j‖) = ∑ j, ‖z j‖ := by
  have h := Finset.add_sum_erase Finset.univ
    (fun j => ‖border a z B (Sum.inl ()) j‖) (Finset.mem_univ (Sum.inl ()))
  have hs : (∑ j, ‖border a z B (Sum.inl ()) j‖) = ‖(a : ℂ)‖ + ∑ j, ‖z j‖ := by
    rw [Fintype.sum_sum_type]
    simp [border, Matrix.fromBlocks]
  rw [hs] at h
  change ‖(a : ℂ)‖ + _ = ‖(a : ℂ)‖ + _ at h
  exact add_left_cancel h

theorem border_row_lower (a : ℝ) (z : I → ℂ) (B : Matrix I I ℂ) (i : I) :
    (∑ j ∈ Finset.univ.erase (Sum.inr i : Unit ⊕ I),
      ‖border a z B (Sum.inr i) j‖) =
      ‖z i‖ + ∑ j ∈ Finset.univ.erase i, ‖B i j‖ := by
  have h := Finset.add_sum_erase Finset.univ
    (fun j => ‖border a z B (Sum.inr i) j‖) (Finset.mem_univ (Sum.inr i))
  have hB := Finset.add_sum_erase Finset.univ
    (fun j => ‖B i j‖) (Finset.mem_univ i)
  have hs : (∑ j, ‖border a z B (Sum.inr i) j‖) = ‖z i‖ + ∑ j, ‖B i j‖ := by
    rw [Fintype.sum_sum_type]
    simp [border, Matrix.fromBlocks]
  rw [hs] at h
  change ‖B i i‖ + _ = ‖z i‖ + _ at h
  linarith

omit [Fintype I] [DecidableEq I] in
theorem scaledMatrix_border (a : ℝ) (z : I → ℂ) (B : Matrix I I ℂ)
    (d : Unit ⊕ I → ℝ) :
    scaledMatrix (border a z B) d =
      border (d (Sum.inl ()) ^ 2 * a)
        (fun i => ((d (Sum.inl ()) * d (Sum.inr i) : ℝ) : ℂ) * z i)
        (scaledMatrix B (fun i => d (Sum.inr i))) := by
  ext i j
  cases i with
  | inl u =>
    cases u
    cases j with
    | inl v =>
      cases v
      change (d (Sum.inl ()) : ℂ) * (a : ℂ) * (d (Sum.inl ()) : ℂ) =
        ((d (Sum.inl ()) ^ 2 * a : ℝ) : ℂ)
      push_cast
      ring
    | inr j =>
      change (d (Sum.inl ()) : ℂ) * star (z j) * (d (Sum.inr j) : ℂ) =
        star (((d (Sum.inl ()) * d (Sum.inr j) : ℝ) : ℂ) * z j)
      simp only [Complex.star_def, map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
      ring
  | inr i =>
    cases j with
    | inl u =>
      cases u
      change (d (Sum.inr i) : ℂ) * z i * (d (Sum.inl ()) : ℂ) =
        ((d (Sum.inl ()) * d (Sum.inr i) : ℝ) : ℂ) * z i
      push_cast
      ring
    | inr j => rfl

omit [Fintype I] [DecidableEq I] in
theorem normalizedBorder_scaled (a : ℝ) (z : I → ℂ)
    (s : ℝ) (hs : 0 < s) (d : I → ℝ) :
    normalizedBorder (s ^ 2 * a) (fun i => ((s * d i : ℝ) : ℂ) * z i) =
      fun i => (d i : ℂ) * normalizedBorder a z i := by
  funext i
  have hsqrt : Real.sqrt (s ^ 2 * a) = s * Real.sqrt a := by
    rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  simp only [normalizedBorder, hsqrt, Complex.ofReal_mul]
  field_simp [hsC]

theorem positive_border_dominance {a : ℝ} {z : I → ℂ} {B : Matrix I I ℂ}
    (hA : ComparisonPD (border a z B)) :
    ∃ d : Unit ⊕ I → ℝ, (∀ i, 0 < d i) ∧
      (∑ i, ‖((d (Sum.inl ()) * d (Sum.inr i) : ℝ) : ℂ) * z i‖) <
        d (Sum.inl ()) ^ 2 * a ∧
      ∀ i, ‖((d (Sum.inl ()) * d (Sum.inr i) : ℝ) : ℂ) * z i‖ +
        (∑ j ∈ Finset.univ.erase i,
          ‖scaledMatrix B (fun j => d (Sum.inr j)) i j‖) <
            (scaledMatrix B (fun j => d (Sum.inr j)) i i).re := by
  obtain ⟨d, hd, hdd⟩ := comparison_positive_scaling (border a z B) hA.2
  refine ⟨d, hd, ?_, ?_⟩
  · have h := hdd (Sum.inl ())
    rw [scaledMatrix_border, border_row_zero] at h
    exact h
  · intro i
    have h := hdd (Sum.inr i)
    rw [scaledMatrix_border, border_row_lower] at h
    exact h

end ResearchMain.Chollet
