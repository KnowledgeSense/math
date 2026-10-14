import HonestEmbeddingDimension.PlaneReduction
import HonestEmbeddingDimension.ParameterAlgebra

namespace HonestEmbeddingDimension

theorem plane_coordinateAlgebra_sub_parameter (m : ℕ) (Y h : PowerSeries ℂ)
    (hh : h ∈ parameterAlgebra m) :
    coordinateAlgebra (planeCoordinates m (Y-h)) = coordinateAlgebra (planeCoordinates m Y) := by
  have hh' : h ∈ Algebra.adjoin ℂ (Set.range
      (fun j : {j : Fin 2 // j ≠ 1} => planeCoordinates m Y j)) := by
    apply Algebra.adjoin_mono _ hh
    rintro x hx
    obtain rfl := Set.mem_singleton_iff.mp hx
    exact ⟨⟨0,by decide⟩,rfl⟩
  have he : planeCoordinates m (Y-h) =
      Function.update (planeCoordinates m Y) 1 (planeCoordinates m Y 1-h) := by
    funext i
    fin_cases i <;> simp [planeCoordinates]
  rw [he]
  exact coordinateAlgebra_update_sub _ 1 h hh'

/-- Finite cancellation finds the genuine first nonparameter value as the second coordinate. -/
theorem normalize_second_plane_coordinate (m a : ℕ) (hm : m ≠ 0)
    (Y : PowerSeries ℂ) (ha : ¬m ∣ a)
    (hval : a ∈ polynomialValues (planeCoordinates m Y))
    (hmin : ∀ n ∈ polynomialValues (planeCoordinates m Y), ¬m ∣ n → a ≤ n) :
    ∃ Z : PowerSeries ℂ, Z.order = a ∧
      polynomialValues (planeCoordinates m Z) = polynomialValues (planeCoordinates m Y) := by
  obtain ⟨h,hh,hred⟩ := exists_reduced_mod_subalgebra (parameterAlgebra m) (a+1) Y
  have he := polynomialValues_eq_of_coordinateAlgebra_eq _ _
    (plane_coordinateAlgebra_sub_parameter m Y h hh)
  have hav : a ∈ polynomialValues (planeCoordinates m (Y-h)) := by rwa [he]
  rcases hred with hhigh | ⟨n,hn,horder,houtside⟩
  · exact False.elim (ha (plane_low_value_dvd m (a+1) a hm (Y-h) hhigh (by omega) hav))
  · have hnval : n ∈ polynomialValues (planeCoordinates m (Y-h)) := by
      refine ⟨MvPolynomial.X 1, ?_⟩
      simpa [planeCoordinates] using horder
    have hnm : ¬m ∣ n := by rwa [← parameterAlgebra_values m hm n]
    have han := hmin n (by rwa [← he]) hnm
    have hna : n = a := by omega
    exact ⟨Y-h,hna ▸ horder,he⟩

end HonestEmbeddingDimension
