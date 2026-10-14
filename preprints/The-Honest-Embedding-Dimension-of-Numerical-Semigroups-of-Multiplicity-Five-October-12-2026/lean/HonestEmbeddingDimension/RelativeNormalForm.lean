import HonestEmbeddingDimension.SubalgebraJets

namespace HonestEmbeddingDimension

noncomputable def partialCoordinateAlgebra {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (I : Set (Fin d)) : Subalgebra ℂ (PowerSeries ℂ) := Algebra.adjoin ℂ (f '' I)

theorem coordinateAlgebra_sub_partial {d : ℕ} (f h : Fin d → PowerSeries ℂ)
    (I : Set (Fin d)) (hh : ∀ i, h i ∈ partialCoordinateAlgebra f I)
    (hzero : ∀ i ∈ I, h i = 0) :
    coordinateAlgebra (fun i => f i-h i) = coordinateAlgebra f := by
  let g := fun i => f i-h i
  have hBf : partialCoordinateAlgebra f I ≤ coordinateAlgebra f :=
    Algebra.adjoin_mono (by rintro x ⟨i,_,rfl⟩; exact Set.mem_range_self i)
  have hBg : partialCoordinateAlgebra f I ≤ coordinateAlgebra g := by
    apply Algebra.adjoin_le
    rintro x ⟨i,hi,rfl⟩
    have he : g i = f i := by simp [g,hzero i hi]
    rw [← he]
    exact Algebra.subset_adjoin (Set.mem_range_self i)
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x ⟨i,rfl⟩
    exact (coordinateAlgebra f).sub_mem (Algebra.subset_adjoin (Set.mem_range_self i)) (hBf (hh i))
  · apply Algebra.adjoin_le
    rintro x ⟨i,rfl⟩
    have he : f i = g i+h i := by simp [g]
    rw [he]
    exact (coordinateAlgebra g).add_mem (Algebra.subset_adjoin (Set.mem_range_self i)) (hBg (hh i))

/-- Finite coordinate changes expose the least value outside a protected coordinate algebra. -/
theorem normalize_coordinate_outside_subalgebra {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (I : Set (Fin d)) (a : ℕ)
    (ha : a ∈ polynomialValues f) (hout : a ∉ subalgebraValues (partialCoordinateAlgebra f I))
    (hmin : ∀ n ∈ polynomialValues f,
      n ∉ subalgebraValues (partialCoordinateAlgebra f I) → a ≤ n) :
    ∃ g : Fin d → PowerSeries ℂ,
      coordinateAlgebra g = coordinateAlgebra f ∧
      (∀ i ∈ I, g i = f i) ∧
      (∀ i, i ∉ I → (a : ℕ∞) ≤ (g i).order) ∧
      ∃ j, j ∉ I ∧ (g j).order = a := by
  classical
  let B := partialCoordinateAlgebra f I
  have hchoose : ∀ i, ∃ h : PowerSeries ℂ, h ∈ B ∧
      (i ∈ I → h = 0) ∧ (i ∉ I → ReducedBelow B (a+1) (f i-h)) := by
    intro i
    by_cases hi : i ∈ I
    · exact ⟨0,B.zero_mem,by simp [hi]⟩
    · obtain ⟨h,hh,hr⟩ := exists_reduced_mod_subalgebra B (a+1) (f i)
      exact ⟨h,hh,by simp [hi],by intro _; exact hr⟩
  choose h hh hzero hred using hchoose
  let g := fun i => f i-h i
  have he : coordinateAlgebra g = coordinateAlgebra f := coordinateAlgebra_sub_partial f h I hh hzero
  have hvalues : polynomialValues g = polynomialValues f := polynomialValues_eq_of_coordinateAlgebra_eq g f he
  refine ⟨g,he,?_,?_,?_⟩
  · intro i hi
    simp [g,hzero i hi]
  · intro i hi
    rcases hred i hi with hhi | ⟨n,hn,hord,houtside⟩
    · exact le_trans (by exact_mod_cast Nat.le_succ a) hhi
    · have hnval : n ∈ polynomialValues g := by
        refine ⟨MvPolynomial.X i,?_⟩
        simpa [g] using hord
      have han := hmin n (by rwa [← hvalues]) houtside
      change (a : ℕ∞) ≤ (f i-h i).order
      rw [hord]
      exact_mod_cast han
  · by_contra hnot
    have hhigh : ∀ i, i ∉ I → ((a+1 : ℕ) : ℕ∞) ≤ (g i).order := by
      intro i hi
      rcases hred i hi with hhi | ⟨n,hn,hord,houtside⟩
      · exact hhi
      · have hnval : n ∈ polynomialValues g := by
          refine ⟨MvPolynomial.X i,?_⟩
          simpa [g] using hord
        have han := hmin n (by rwa [← hvalues]) houtside
        have hna : n = a := by omega
        apply False.elim
        apply hnot
        exact ⟨i,hi,hna ▸ hord⟩
    apply hout
    apply low_value_mem_subalgebra B g (a+1) a (by omega) _ (by rwa [hvalues])
    intro i
    by_cases hi : i ∈ I
    · refine ⟨f i,Algebra.subset_adjoin ⟨i,hi,rfl⟩,?_⟩
      simp [g,hzero i hi]
    · exact ⟨0,B.zero_mem,(formalJet_eq_zero_iff _).mpr (hhigh i hi)⟩

/-- The relative normal form preserves zero-constant formal substitution and its full value algebra. -/
theorem normalize_formal_coordinate_outside_subalgebra {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (hf0 : ∀ i, (f i).constantCoeff = 0) (I : Set (Fin d)) (a : ℕ) (ha0 : 0 < a)
    (ha : a ∈ formalValues f) (hout : a ∉ subalgebraValues (partialCoordinateAlgebra f I))
    (hmin : ∀ n ∈ formalValues f,
      n ∉ subalgebraValues (partialCoordinateAlgebra f I) → a ≤ n) :
    ∃ g : Fin d → PowerSeries ℂ,
      (∀ i, (g i).constantCoeff = 0) ∧ formalValues g = formalValues f ∧
      (∀ i ∈ I, g i = f i) ∧ ∃ j, j ∉ I ∧ (g j).order = a := by
  have hva := formalValues_eq_polynomialValues f hf0
  obtain ⟨g,he,hfix,horder,j,hj,hja⟩ := normalize_coordinate_outside_subalgebra f I a
    (by rwa [← hva]) hout (by intro n hn; exact hmin n (by rwa [hva]))
  have hg0 : ∀ i, (g i).constantCoeff = 0 := by
    intro i
    by_cases hi : i ∈ I
    · rw [hfix i hi]; exact hf0 i
    · apply PowerSeries.one_le_order_iff_constCoeff_eq_zero.mp
      exact le_trans (by exact_mod_cast ha0) (horder i hi)
  refine ⟨g,hg0,?_,hfix,j,hj,hja⟩
  rw [formalValues_eq_polynomialValues g hg0, hva]
  exact polynomialValues_eq_of_coordinateAlgebra_eq g f he

end HonestEmbeddingDimension
