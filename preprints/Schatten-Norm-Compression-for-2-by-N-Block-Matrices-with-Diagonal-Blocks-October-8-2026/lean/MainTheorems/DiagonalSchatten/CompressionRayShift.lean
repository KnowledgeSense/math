import MainTheorems.DiagonalSchatten.FixedGramShift
import MainTheorems.DiagonalSchatten.RayBoundaryContinuity
import MainTheorems.DiagonalSchatten.PowerInverseIdentity

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

theorem compressionRay_gram_inverse {p : ℝ} (hp2 : p ≠ 2)
    (X : Matrix (Fin 2) J ℝ) (Z : Fin 3 → ℝ)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) (hc : gramCross X ≠ 0) :
    gramCoordinates X = symmetricPower (2 / (compressionRay p X Z).k)
      ![(compressionRay p X Z).a, (compressionRay p X Z).b, (compressionRay p X Z).c] := by
  have hr : (p - 2) / 2 ≠ 0 := div_ne_zero (sub_ne_zero.mpr hp2) (by norm_num)
  have hH : ![(compressionRay p X Z).a, (compressionRay p X Z).b, (compressionRay p X Z).c] =
      symmetricPower ((p - 2) / 2) (gramCoordinates X) := by
    rw [gramCoordinates, symmetricPower_gram]
    funext i
    fin_cases i <;> simp [compressionRay]
  rw [hH]
  change gramCoordinates X = symmetricPower (2 / (p - 2)) _
  have he : 2 / (p - 2) = 1 / ((p - 2) / 2) := by field_simp
  rw [he, symmetricPower_inverse hr _ (gramFirst_positive_of_determinant X hdet) hdet hc]

theorem compressionRay_shift_difference {p : ℝ} (hp : 1 < p) (hp2 : p ≠ 2)
    (X : Matrix (Fin 2) J ℝ) (Z : Fin 3 → ℝ) (t : ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (hdet : 0 < gramFirst X * gramSecond X - gramCross X ^ 2) (hc : 0 < gramCross X) :
    let g := compressionRay p X Z
    (∑ j, (g.shift t).functional (fun i => X i j)) -
        symmetricTraceProduct ![(g.shift t).z1, (g.shift t).z2, (g.shift t).z12]
          (symmetricPowerVariation (2 / g.k) ![g.a, g.b, g.c]
            ![(g.shift t).z1, (g.shift t).z2, (g.shift t).z12]) / 2 =
      (∑ j, g.functional (fun i => X i j)) - inverseGramQuadratic p X Z / 2 := by
  let g := compressionRay p X Z
  have hk : g.k ≠ 0 := sub_ne_zero.mpr hp2
  obtain ⟨ha, _, hd⟩ := symmetricPower_positive_definite ((p - 2) / 2) (gramCoordinates X)
    (gramFirst_positive_of_determinant X hdet) hdet hc.ne'
  simp only [gramCoordinates, symmetricPower_gram] at ha hd
  have hgc : g.c ≠ 0 := by
    rcases lt_or_gt_of_ne hp2 with hp2 | hp2
    · have h := symmetricPower_cross_negative (by linarith : (p - 2) / 2 < 0)
        (gramCoordinates X) (gramFirst_positive_of_determinant X hdet) hdet hc
      simp only [gramCoordinates, symmetricPower_gram] at h
      exact h.ne
    · have h := symmetricPower_cross_positive (by linarith : 0 < (p - 2) / 2)
        (gramCoordinates X) (gramFirst_positive_of_determinant X hdet) hdet hc
      simp only [gramCoordinates, symmetricPower_gram] at h
      exact h.ne'
  have hD (j : J) (hn : X 0 j ≠ 0 ∨ X 1 j ≠ 0) : g.denominator (fun i => X i j) ≠ 0 := by
    apply (compressionRay_denominator_nonnegative hp hp2 X Z _ hdet hc (fun i => hX i j) ?_).ne'
    rcases hn with hn | hn
    · exact Or.inl (lt_of_le_of_ne (hX 0 j) (Ne.symm hn))
    · exact Or.inr (lt_of_le_of_ne (hX 1 j) (Ne.symm hn))
  have h := g.fixedGram_shift_difference t X hk ha hd hgc
    (compressionRay_gram_inverse hp2 X Z hdet hc.ne') hD
  have hH : ![g.a, g.b, g.c] = symmetricPower ((p - 2) / 2) (gramCoordinates X) := by
    rw [gramCoordinates, symmetricPower_gram]
    funext i
    fin_cases i <;> simp [g, compressionRay]
  have hZ : ![g.z1, g.z2, g.z12] = Z := by
    funext i
    fin_cases i <;> simp [g, compressionRay]
  have he : 2 / g.k = 1 / ((p - 2) / 2) := by change 2 / (p - 2) = _; field_simp
  rw [hZ] at h
  have hquad : symmetricTraceProduct Z
      (symmetricPowerVariation (2 / g.k) ![g.a, g.b, g.c] Z) =
      inverseGramQuadratic p X Z := by
    rw [hH, he]
    rfl
  rw [hquad] at h
  exact h

end

end ResearchMain.DiagonalSchatten
