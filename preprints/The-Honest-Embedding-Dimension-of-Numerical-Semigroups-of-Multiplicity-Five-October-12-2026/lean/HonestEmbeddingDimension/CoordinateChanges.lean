import HonestEmbeddingDimension.Reparametrization

namespace HonestEmbeddingDimension

noncomputable def coordinateAlgebra {d : ℕ} (f : Fin d → PowerSeries ℂ) :
    Subalgebra ℂ (PowerSeries ℂ) := Algebra.adjoin ℂ (Set.range f)

theorem mem_coordinateAlgebra_iff {d : ℕ} (f : Fin d → PowerSeries ℂ) (g : PowerSeries ℂ) :
    g ∈ coordinateAlgebra f ↔ ∃ p : MvPolynomial (Fin d) ℂ, MvPolynomial.aeval f p=g := by
  rw [coordinateAlgebra, ← MvPolynomial.aeval_range]
  rfl

theorem polynomialValues_eq_of_coordinateAlgebra_eq {d e : ℕ}
    (f : Fin d → PowerSeries ℂ) (g : Fin e → PowerSeries ℂ)
    (h : coordinateAlgebra f=coordinateAlgebra g) : polynomialValues f=polynomialValues g := by
  ext n
  constructor
  · rintro ⟨p,hp⟩
    have hm : MvPolynomial.aeval f p ∈ coordinateAlgebra g := by
      rw [← h, mem_coordinateAlgebra_iff]
      exact ⟨p,rfl⟩
    obtain ⟨q,hq⟩ := (mem_coordinateAlgebra_iff g _).mp hm
    exact ⟨q, hq ▸ hp⟩
  · rintro ⟨p,hp⟩
    have hm : MvPolynomial.aeval g p ∈ coordinateAlgebra f := by
      rw [h, mem_coordinateAlgebra_iff]
      exact ⟨p,rfl⟩
    obtain ⟨q,hq⟩ := (mem_coordinateAlgebra_iff f _).mp hm
    exact ⟨q, hq ▸ hp⟩

theorem coordinateAlgebra_update_sub {d : ℕ} (f : Fin d → PowerSeries ℂ) (i : Fin d)
    (h : PowerSeries ℂ)
    (hh : h ∈ Algebra.adjoin ℂ (Set.range (fun j : {j : Fin d // j ≠ i} => f j))) :
    coordinateAlgebra (Function.update f i (f i-h))=coordinateAlgebra f := by
  classical
  let g := Function.update f i (f i-h)
  have hfmem (j : Fin d) : f j ∈ coordinateAlgebra f := Algebra.subset_adjoin (Set.mem_range_self j)
  have hgmem (j : Fin d) : g j ∈ coordinateAlgebra g := Algebra.subset_adjoin (Set.mem_range_self j)
  have hhf : h ∈ coordinateAlgebra f :=
    Algebra.adjoin_mono (by rintro x ⟨j,rfl⟩; exact Set.mem_range_self j.val) hh
  have hhg : h ∈ coordinateAlgebra g :=
    Algebra.adjoin_mono (by
      rintro x ⟨j,rfl⟩
      refine ⟨j.val, ?_⟩
      simp [g, Function.update_of_ne j.property]) hh
  change coordinateAlgebra g=coordinateAlgebra f
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x ⟨j,rfl⟩
    by_cases hj : j=i
    · subst j
      simpa [g] using (coordinateAlgebra f).sub_mem (hfmem i) hhf
    · simpa [g, Function.update_of_ne hj] using hfmem j
  · apply Algebra.adjoin_le
    rintro x ⟨j,rfl⟩
    by_cases hj : j=i
    · subst j
      have hm := (coordinateAlgebra g).add_mem (hgmem i) hhg
      simpa [g] using hm
    · simpa [g, Function.update_of_ne hj] using hgmem j

theorem coordinateAlgebra_update_scale {d : ℕ} (f : Fin d → PowerSeries ℂ) (i : Fin d)
    (c : ℂ) (hc : c ≠ 0) :
    coordinateAlgebra (Function.update f i (c • f i))=coordinateAlgebra f := by
  classical
  let g := Function.update f i (c • f i)
  have hfmem (j : Fin d) : f j ∈ coordinateAlgebra f := Algebra.subset_adjoin (Set.mem_range_self j)
  have hgmem (j : Fin d) : g j ∈ coordinateAlgebra g := Algebra.subset_adjoin (Set.mem_range_self j)
  change coordinateAlgebra g=coordinateAlgebra f
  apply le_antisymm
  · apply Algebra.adjoin_le
    rintro x ⟨j,rfl⟩
    by_cases hj : j=i
    · subst j
      simpa [g] using (coordinateAlgebra f).smul_mem (hfmem i) c
    · simpa [g, Function.update_of_ne hj] using hfmem j
  · apply Algebra.adjoin_le
    rintro x ⟨j,rfl⟩
    by_cases hj : j=i
    · subst j
      have hm := (coordinateAlgebra g).smul_mem (hgmem i) c⁻¹
      simpa [g, smul_smul, hc] using hm
    · simpa [g, Function.update_of_ne hj] using hgmem j

end HonestEmbeddingDimension
