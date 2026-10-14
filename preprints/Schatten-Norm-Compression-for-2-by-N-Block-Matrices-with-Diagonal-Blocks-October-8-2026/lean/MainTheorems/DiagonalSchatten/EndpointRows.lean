import MainTheorems.DiagonalSchatten.RealGramRepresentation
import MainTheorems.DiagonalSchatten.ThreeRayObjective

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

def firstEndpointRows (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt a, 0; c / Real.sqrt a, Real.sqrt (b - c ^ 2 / a)]

def secondEndpointRows (a b c : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.sqrt (a - c ^ 2 / b), c / Real.sqrt b; 0, Real.sqrt b]

theorem firstEndpointRows_gram {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hd : 0 < a * b - c ^ 2) :
    (∀ i j, 0 ≤ firstEndpointRows a b c i j) ∧
      gramFirst (firstEndpointRows a b c) = a ∧
      gramSecond (firstEndpointRows a b c) = b ∧
      gramCross (firstEndpointRows a b c) = c := by
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hr : 0 ≤ b - c ^ 2 / a := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ ha).mpr
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [firstEndpointRows, div_nonneg hc.le hs.le]
  · simp [firstEndpointRows, gramFirst, Fin.sum_univ_two, Real.sq_sqrt ha.le]
  · simp only [gramSecond, Fin.sum_univ_two]
    change (c / Real.sqrt a) ^ 2 + Real.sqrt (b - c ^ 2 / a) ^ 2 = b
    rw [div_pow, Real.sq_sqrt ha.le, Real.sq_sqrt hr]
    ring
  · simp only [gramCross, Fin.sum_univ_two]
    change Real.sqrt a * (c / Real.sqrt a) + 0 * Real.sqrt (b - c ^ 2 / a) = c
    simp only [zero_mul, add_zero]
    field_simp [hs.ne']

theorem secondEndpointRows_gram {a b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < a * b - c ^ 2) :
    (∀ i j, 0 ≤ secondEndpointRows a b c i j) ∧
      gramFirst (secondEndpointRows a b c) = a ∧
      gramSecond (secondEndpointRows a b c) = b ∧
      gramCross (secondEndpointRows a b c) = c := by
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hr : 0 ≤ a - c ^ 2 / b := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ hb).mpr
    nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [secondEndpointRows, div_nonneg hc.le hs.le]
  · simp only [gramFirst, Fin.sum_univ_two]
    change Real.sqrt (a - c ^ 2 / b) ^ 2 + (c / Real.sqrt b) ^ 2 = a
    rw [div_pow, Real.sq_sqrt hb.le, Real.sq_sqrt hr]
    ring
  · simp [secondEndpointRows, gramSecond, Fin.sum_univ_two, Real.sq_sqrt hb.le]
  · simp only [gramCross, Fin.sum_univ_two]
    change Real.sqrt (a - c ^ 2 / b) * 0 + (c / Real.sqrt b) * Real.sqrt b = c
    simp only [mul_zero, zero_add]
    field_simp [hs.ne']

theorem firstEndpointRows_objective {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (hd : 0 < a * b - c ^ 2) (h : (Fin 2 → ℝ) → ℝ)
    (hh : ∀ x t, h (t • x) = t ^ 2 * h x) :
    columnObjective h (firstEndpointRows a b c) =
      (a - c / (c / a)) * h ![1, 0] +
        (b - c * (c / a)) * h ![0, 1] + (c / (c / a)) * h ![1, c / a] := by
  obtain ⟨hn, hA, hB, hC⟩ := firstEndpointRows_gram ha hc hd
  rw [three_ray_objective _ hn (div_pos hc ha) ?_ h hh, hA, hB, hC]
  intro j hj0 _
  fin_cases j
  · change c / Real.sqrt a = (c / a) * Real.sqrt a
    have hs := (Real.sqrt_pos.mpr ha).ne'
    have hs2 := Real.sq_sqrt ha.le
    field_simp [ha.ne', hs]
    nlinarith
  · change 0 < 0 at hj0
    exact (lt_irrefl 0 hj0).elim

theorem secondEndpointRows_objective {a b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < a * b - c ^ 2) (h : (Fin 2 → ℝ) → ℝ)
    (hh : ∀ x t, h (t • x) = t ^ 2 * h x) :
    columnObjective h (secondEndpointRows a b c) =
      (a - c / (b / c)) * h ![1, 0] +
        (b - c * (b / c)) * h ![0, 1] + (c / (b / c)) * h ![1, b / c] := by
  obtain ⟨hn, hA, hB, hC⟩ := secondEndpointRows_gram hb hc hd
  rw [three_ray_objective _ hn (div_pos hb hc) ?_ h hh, hA, hB, hC]
  intro j _ hj1
  fin_cases j
  · change 0 < 0 at hj1
    exact (lt_irrefl 0 hj1).elim
  · change Real.sqrt b = (b / c) * (c / Real.sqrt b)
    have hs := (Real.sqrt_pos.mpr hb).ne'
    have hs2 := Real.sq_sqrt hb.le
    field_simp [hc.ne', hs]
    nlinarith

end

end ResearchMain.DiagonalSchatten
