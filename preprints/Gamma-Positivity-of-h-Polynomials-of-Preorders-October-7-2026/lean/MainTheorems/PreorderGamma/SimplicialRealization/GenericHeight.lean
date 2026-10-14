import MainTheorems.PreorderGamma.SimplicialRealization.ProjectiveSupporting
import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.Order.Interval.Set.Infinite

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

abbrev DependentSubset (E : Type*) [Fintype E] [DecidableEq E] [Preorder E] :=
  {s : Finset (QuotientIndex E) // ¬LinearIndependent ℝ (fun v : s => v.val.val)}

noncomputable instance dependentSubsetFintype : Fintype (DependentSubset E) := by
  classical
  unfold DependentSubset
  infer_instance

theorem dependentSubset_relation (s : DependentSubset E) :
    ∃ w : s.val → ℝ, (∑ v, w v • v.val.val) = 0 ∧ ∃ v, w v ≠ 0 := by
  have h := s.property
  rw [Fintype.linearIndependent_iff] at h
  push Not at h
  exact h

noncomputable def dependentCoefficients (s : DependentSubset E) : s.val → ℝ :=
  Classical.choose (dependentSubset_relation s)

theorem dependentCoefficients_sum (s : DependentSubset E) :
    (∑ v, dependentCoefficients s v • v.val.val) = 0 :=
  (Classical.choose_spec (dependentSubset_relation s)).1

theorem dependentCoefficients_nonzero (s : DependentSubset E) :
    ∃ v, dependentCoefficients s v ≠ 0 :=
  (Classical.choose_spec (dependentSubset_relation s)).2

noncomputable def dependentHeightMap (s : DependentSubset E) :
    (QuotientIndex E → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun h => ∑ v : s.val, dependentCoefficients s v * h v.val
  map_add' := by intro h g; simp [mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c h
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro v hv
    ring

theorem dependentHeightMap_nonzero (s : DependentSubset E) :
    ∃ h, dependentHeightMap s h ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := dependentCoefficients_nonzero s
  refine ⟨(Pi.single v.val (1 : ℝ) : QuotientIndex E → ℝ), ?_⟩
  change (∑ w : s.val, dependentCoefficients s w *
    (Pi.single v.val (1 : ℝ) : QuotientIndex E → ℝ) w.val) ≠ 0
  simpa [Pi.single_apply, Subtype.val_injective.eq_iff, eq_comm] using hv

theorem genericHeight_simplicial (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v)
    (hgeneric : ∀ s : DependentSubset E, dependentHeightMap s height ≠ 0) :
    HasSimplicialBoundary height := by
  classical
  intro s hs
  have hface := (boundaryVertexFace_iff_heightFace height hheight s).mp
    ((mem_boundaryVertexFaces height s).mp hs)
  have hlin : LinearIndependent ℝ (fun v : s => v.val.val) := by
    by_contra hnot
    let d : DependentSubset E := ⟨s, hnot⟩
    rcases hface with rfl | ⟨l, hl, hb, ht, hn⟩
    · have hEmpty : LinearIndependent ℝ (fun v : (∅ : Finset (QuotientIndex E)) => v.val.val) :=
        linearIndependent_empty_type
      exact hnot hEmpty
    · have hzero : dependentHeightMap d height = 0 := by
        calc
          _ = l (∑ v : d.val, dependentCoefficients d v • v.val.val) := by
            simp only [dependentHeightMap, LinearMap.coe_mk,
              map_sum, map_smul, smul_eq_mul]
            apply Finset.sum_congr rfl
            intro v hv
            rw [(ht v.val).mp v.property]
          _ = 0 := by rw [dependentCoefficients_sum, map_zero]
      exact hgeneric d hzero
  have hscaled := hlin.units_smul (fun v : s =>
    Units.mk0 (height v.val)⁻¹ (inv_ne_zero (ne_of_gt (hheight v.val))))
  have hp : LinearIndependent ℝ (fun v : s => projectiveVertex height v.val) := by
    change LinearIndependent ℝ (fun v : s => (height v.val)⁻¹ • v.val.val) at hscaled
    exact hscaled
  exact hp.affineIndependent

theorem exists_generic_positive_height (δ : ℝ) (hδ : 0 < δ) :
    ∃ height : QuotientIndex E → ℝ,
      (∀ v, 0 < height v) ∧ (∀ v, |height v - 1| < δ) ∧
        HasSimplicialBoundary height := by
  classical
  obtain ⟨w, hw⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (dependentHeightMap (E := E)) dependentHeightMap_nonzero
  let M : ℝ := 1 + ∑ v : QuotientIndex E, |w v|
  have hM : 0 < M := by
    have hsum : 0 ≤ ∑ v : QuotientIndex E, |w v| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    dsimp [M]
    linarith
  let η := min δ (1 / 2 : ℝ)
  have hη : 0 < η := lt_min hδ (by norm_num)
  let roots : Set ℝ := Set.range fun s : DependentSubset E =>
    -dependentHeightMap s (fun _ => 1) / dependentHeightMap s w
  have hroots : roots.Finite := Set.finite_range _
  have hinterval : (Set.Ioo (0 : ℝ) (η / M)).Infinite :=
    Set.Ioo_infinite (div_pos hη hM)
  obtain ⟨ε, hε, havoid⟩ := (hinterval.sdiff hroots).nonempty
  let height : QuotientIndex E → ℝ := fun v => 1 + ε * w v
  have hsmall : ∀ v, |height v - 1| < η := by
    intro v
    have hv : |w v| ≤ M := by
      have h := Finset.single_le_sum (fun i hi => abs_nonneg (w i)) (Finset.mem_univ v)
      dsimp [M]
      linarith
    have hεM : ε * M < η := (lt_div_iff₀ hM).mp hε.2
    calc
      |height v - 1| = ε * |w v| := by simp [height, abs_mul, abs_of_pos hε.1]
      _ ≤ ε * M := mul_le_mul_of_nonneg_left hv hε.1.le
      _ < η := hεM
  have hpos : ∀ v, 0 < height v := by
    intro v
    have h := (abs_lt.mp (hsmall v)).1
    have hηhalf : η ≤ (1 / 2 : ℝ) := min_le_right _ _
    linarith
  refine ⟨height, hpos, fun v => (hsmall v).trans_le (min_le_left _ _), ?_⟩
  apply genericHeight_simplicial height hpos
  intro s hzero
  have heq : dependentHeightMap s (fun _ => 1) + ε * dependentHeightMap s w = 0 := by
    change dependentHeightMap s ((fun _ => 1) + ε • w) = 0 at hzero
    simpa only [map_add, map_smul, smul_eq_mul] using hzero
  have hεroot : ε = -dependentHeightMap s (fun _ => 1) / dependentHeightMap s w := by
    apply (eq_div_iff (hw s)).mpr
    linarith
  exact havoid ⟨s, hεroot.symm⟩

theorem exists_simplicial_projective_polytope :
    ∃ height : QuotientIndex E → ℝ,
      (∀ v, 0 < height v) ∧ HasSimplicialBoundary height ∧
        Module.finrank ℝ (affineSpan ℝ (projectivePolytope height)).direction = Fintype.card E := by
  obtain ⟨height, hpos, hnear, hsimp⟩ := exists_generic_positive_height (E := E) 1 zero_lt_one
  exact ⟨height, hpos, hsimp, projectivePolytope_dimension height hpos⟩

end ResearchMain.PreorderGamma.SimplicialRealization
