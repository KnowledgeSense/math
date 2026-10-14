import HonestEmbeddingDimension.PlaneValues
import HonestEmbeddingDimension.Definitions

namespace HonestEmbeddingDimension

@[simp] theorem analyticTaylor_id : analyticTaylor (fun t : ℂ => t) = PowerSeries.X := by
  ext n
  by_cases h0 : n = 0
  · subst n; simp [coeff_analyticTaylor, PowerSeries.coeff_X]
  · by_cases h1 : n = 1
    · subst n; simp [coeff_analyticTaylor, PowerSeries.coeff_X]
    · have hd : iteratedDeriv n (fun t : ℂ => t) 0 = 0 := by
        change iteratedDeriv n id (0 : ℂ) = 0
        simp [iteratedDeriv_id, h0, h1]
      simp [coeff_analyticTaylor, hd, PowerSeries.coeff_X, h1]

theorem analyticTaylor_pow {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    analyticTaylor (fun t => f t ^ n) = analyticTaylor f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ]
    rw [analyticTaylor_mul (f := fun t => f t ^ n) (g := f) (hf.pow n) hf, ih]

/-- The plane lemma for the original convergent complex value algebra. -/
theorem analytic_plane_values (m a : ℕ) (hm : 0 < m) (ha : 0 < a) (hcop : m.Coprime a)
    (y : ℂ → ℂ) (hy : AnalyticAt ℂ y 0) (horder : analyticOrderAt y 0 = a) :
    analyticValues (fun t : ℂ => ![t^m,y t]) = {n | ∃ k j : ℕ, n = m*k + a*j} := by
  have hY : (analyticTaylor y).order = a := (order_analyticTaylor hy).trans horder
  have hy0 : y 0 = 0 := by
    have h := PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
      (show (1 : ℕ∞) ≤ (analyticTaylor y).order by rw [hY]; exact_mod_cast ha)
    simpa using h
  have hF : ∀ i : Fin 2, AnalyticAt ℂ (fun t : ℂ => (![t^m,y t] : Fin 2 → ℂ) i) 0 := by
    intro i
    fin_cases i
    · exact analyticAt_id.pow m
    · exact hy
  rw [analyticValues_eq_formalValues _ hF (by simp [Nat.ne_of_gt hm,hy0])]
  have he : (fun i : Fin 2 => analyticTaylor
      (fun t : ℂ => (![t^m,y t] : Fin 2 → ℂ) i)) = planeCoordinates m (analyticTaylor y) := by
    funext i
    fin_cases i
    · simpa [planeCoordinates] using analyticTaylor_pow (f := fun t : ℂ => t) analyticAt_id m
    · rfl
  rw [he]
  exact formal_plane_values m a hm ha hcop (analyticTaylor y) hY

end HonestEmbeddingDimension
