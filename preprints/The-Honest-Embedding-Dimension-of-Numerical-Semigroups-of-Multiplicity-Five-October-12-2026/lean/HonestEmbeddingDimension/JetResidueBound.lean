import HonestEmbeddingDimension.ParameterJetValues

namespace HonestEmbeddingDimension

/-- A finite jet spanning certificate bounds the number of low value residues, even for a dependent basis. -/
theorem low_value_residue_count {d q m N p : ℕ} (hm : m ≠ 0)
    (f : Fin d → PowerSeries ℂ) (B : Fin q → PowerSeries ℂ)
    (hspan : ∀ P : MvPolynomial (Fin d) ℂ,
      InParameterJetSpan m hm B N (MvPolynomial.aeval f P))
    (w : Fin p → ℕ) (hw : ∀ i, w i < N)
    (hres : Function.Injective (fun i => w i % m))
    (hv : ∀ i, w i ∈ polynomialValues f) : p ≤ q := by
  classical
  have hex : ∀ i, ∃ u : Fin q → PowerSeries ℂ,
      (parameterCombination m hm B u).order = w i := by
    intro i
    obtain ⟨P,hP⟩ := hv i
    obtain ⟨u,hu⟩ := hspan P
    exact ⟨u,(order_eq_of_jet_eq hu (hw i)).mp hP⟩
  choose u hu using hex
  exact distinct_residues_le_parameter_generators p q m hm
    (fun i => parameterCombination m hm B (u i)) B u w hu hres (by intro i; rfl)

theorem low_formal_value_residue_count {d q m N p : ℕ} (hm : m ≠ 0)
    (f : Fin d → PowerSeries ℂ) (hf0 : ∀ i, (f i).constantCoeff = 0)
    (B : Fin q → PowerSeries ℂ)
    (hspan : ∀ P : MvPolynomial (Fin d) ℂ,
      InParameterJetSpan m hm B N (MvPolynomial.aeval f P))
    (w : Fin p → ℕ) (hw : ∀ i, w i < N)
    (hres : Function.Injective (fun i => w i % m))
    (hv : ∀ i, w i ∈ formalValues f) : p ≤ q := by
  apply low_value_residue_count hm f B hspan w hw hres
  intro i
  rw [← formalValues_eq_polynomialValues f hf0]
  exact hv i

end HonestEmbeddingDimension
