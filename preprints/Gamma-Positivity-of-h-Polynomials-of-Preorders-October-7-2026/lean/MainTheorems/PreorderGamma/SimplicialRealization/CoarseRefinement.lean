import MainTheorems.PreorderGamma.SimplicialRealization.GenericHeight
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Order.Compact

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def coefficientFunctional (a : E → ℝ) : (E → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, a i * x i
  map_add' x y := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum, mul_left_comm]

omit [Preorder E] in
theorem coefficientFunctional_single (a : E → ℝ) (i : E) :
    coefficientFunctional a (Pi.single i 1) = a i := by
  classical
  simp [coefficientFunctional, Pi.single_apply]

omit [Preorder E] in
theorem coefficientFunctional_coordinates (l : (E → ℝ) →ₗ[ℝ] ℝ) :
    coefficientFunctional (fun i => l (Pi.single i 1)) = l := by
  apply LinearMap.ext
  intro x
  change (∑ i, l (Pi.single i 1) * x i) = l x
  calc
    _ = ∑ i, l (Pi.single i (x i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have h : Pi.single i (x i) = x i • Pi.single i (1 : ℝ) := by
        ext j
        simp [Pi.single_apply]
      rw [h, map_smul, smul_eq_mul, mul_comm]
    _ = l x := by rw [← map_sum, Finset.univ_sum_single]

def IsCoarseFace (s : Finset (QuotientIndex E)) : Prop :=
  ∃ l : (E → ℝ) →ₗ[ℝ] ℝ, (∀ v : QuotientIndex E, l v.val ≤ 1) ∧
    ∀ v ∈ s, l v.val = 1

abbrev HeightSupportBox (E : Type*) [Fintype E] :=
  {a : E → ℝ // a ∈ Set.Icc (fun _ => -2) (fun _ => 2)}

noncomputable instance : CompactSpace (HeightSupportBox E) := by
  exact isCompact_iff_compactSpace.mp
    (isCompact_Icc : IsCompact (Set.Icc (fun _ : E => (-2 : ℝ)) (fun _ => 2)))

def boundedHeightFaces (s : Finset (QuotientIndex E)) : Set (QuotientIndex E → ℝ) :=
  {height | ∃ a : HeightSupportBox E,
    (∀ v, coefficientFunctional a.val v.val ≤ height v) ∧
      ∀ v ∈ s, coefficientFunctional a.val v.val = height v}

theorem boundedHeightFaces_closed (s : Finset (QuotientIndex E)) :
    IsClosed (boundedHeightFaces s) := by
  let C : Set ((QuotientIndex E → ℝ) × HeightSupportBox E) :=
    {p | (∀ v, coefficientFunctional p.2.val v.val ≤ p.1 v) ∧
      ∀ v ∈ s, coefficientFunctional p.2.val v.val = p.1 v}
  have hC : IsClosed C := by
    apply IsClosed.inter
    · change IsClosed {p : (QuotientIndex E → ℝ) × HeightSupportBox E |
        ∀ v, coefficientFunctional p.2.val v.val ≤ p.1 v}
      simp only [← Set.iInter_ofPred]
      apply isClosed_iInter
      intro v
      apply isClosed_le
      · change Continuous (fun p : (QuotientIndex E → ℝ) × HeightSupportBox E =>
          ∑ i, p.2.val i * v.val i)
        apply continuous_finsetSum
        intro i hi
        exact ((continuous_apply i).comp
          (continuous_subtype_val.comp continuous_snd)).mul continuous_const
      · fun_prop
    · change IsClosed {p : (QuotientIndex E → ℝ) × HeightSupportBox E |
        ∀ v ∈ s, coefficientFunctional p.2.val v.val = p.1 v}
      simp only [← Set.iInter_ofPred]
      apply isClosed_iInter
      intro v
      apply isClosed_iInter
      intro hv
      apply isClosed_eq
      · change Continuous (fun p : (QuotientIndex E → ℝ) × HeightSupportBox E =>
          ∑ i, p.2.val i * v.val i)
        apply continuous_finsetSum
        intro i hi
        exact ((continuous_apply i).comp
          (continuous_subtype_val.comp continuous_snd)).mul continuous_const
      · fun_prop
  have heq : boundedHeightFaces s = Prod.fst '' C := by
    ext height
    constructor
    · rintro ⟨a, ha⟩
      exact ⟨(height, a), ha, rfl⟩
    · rintro ⟨⟨h, a⟩, ha, rfl⟩
      exact ⟨a, ha⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace C hC

theorem boundedHeightFaces_one (s : Finset (QuotientIndex E))
    (hs : (fun _ => (1 : ℝ)) ∈ boundedHeightFaces s) : IsCoarseFace s := by
  obtain ⟨a, ha, ht⟩ := hs
  exact ⟨coefficientFunctional a.val, ha, ht⟩

theorem heightFace_mem_boundedHeightFaces (height : QuotientIndex E → ℝ)
    (hnear : ∀ v, |height v - 1| < 1) (s : Finset (QuotientIndex E))
    (hs : IsHeightFace height s) : height ∈ boundedHeightFaces s := by
  classical
  rcases hs with rfl | ⟨l, hl, hb, ht, hn⟩
  · refine ⟨⟨0, ?_⟩, ?_, ?_⟩
    · constructor <;> intro i <;> norm_num
    · intro v
      have h := (abs_lt.mp (hnear v)).1
      have hp : 0 ≤ height v := by linarith
      simpa [coefficientFunctional] using hp
    · simp
  · let a : E → ℝ := fun i => l (Pi.single i 1)
    have ha : a ∈ Set.Icc (fun _ => -2) (fun _ => 2) := by
      constructor
      · intro i
        have hb' := hb (negUnitIndex i)
        change l (-Pi.single i 1) ≤ height (negUnitIndex i) at hb'
        rw [map_neg] at hb'
        have hh := (abs_lt.mp (hnear (negUnitIndex i))).2
        change -2 ≤ l (Pi.single i 1)
        linarith
      · intro i
        have hb' := hb (unitIndex i)
        have hh := (abs_lt.mp (hnear (unitIndex i))).2
        change l (Pi.single i 1) ≤ 2
        change l (Pi.single i 1) ≤ height (unitIndex i) at hb'
        linarith
    refine ⟨⟨a, ha⟩, ?_, ?_⟩
    · simpa only [a, coefficientFunctional_coordinates] using hb
    · intro v hv
      simpa only [a, coefficientFunctional_coordinates] using (ht v).mp hv

theorem exists_coarse_refinement_radius :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧
      ∀ height : QuotientIndex E → ℝ, (∀ v, |height v - 1| < δ) →
        ∀ s : Finset (QuotientIndex E), IsHeightFace height s → IsCoarseFace s := by
  classical
  let U : Set (QuotientIndex E → ℝ) :=
    ⋂ s : Finset (QuotientIndex E),
      if IsCoarseFace s then Set.univ else (boundedHeightFaces s)ᶜ
  have hU : IsOpen U := by
    apply isOpen_iInter_of_finite
    intro s
    split_ifs
    · exact isOpen_univ
    · exact (boundedHeightFaces_closed s).isOpen_compl
  have h1 : (fun _ => (1 : ℝ)) ∈ U := by
    apply Set.mem_iInter.mpr
    intro s
    split_ifs with hs
    · trivial
    · exact fun h => hs (boundedHeightFaces_one s h)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU _ h1
  refine ⟨min ε 1, lt_min hε (by norm_num), min_le_right _ _, ?_⟩
  intro height hheight s hs
  have hn : ∀ v, |height v - 1| < 1 := fun v =>
    lt_of_lt_of_le (hheight v) (min_le_right _ _)
  have hmem : height ∈ U := by
    apply hball
    apply (dist_pi_lt_iff hε).mpr
    intro v
    simpa only [Real.dist_eq] using
      lt_of_lt_of_le (hheight v) (min_le_left _ _)
  have h := Set.mem_iInter.mp hmem s
  by_contra hnot
  simp only [hnot, ite_false] at h
  exact h (heightFace_mem_boundedHeightFaces height hn s hs)

theorem exists_simplicial_coarse_height :
    ∃ height : QuotientIndex E → ℝ, (∀ v, 0 < height v) ∧
      HasSimplicialBoundary height ∧
      ∀ s ∈ boundaryVertexFaces height, IsCoarseFace s := by
  obtain ⟨δ, hδ, hδ1, hδref⟩ := exists_coarse_refinement_radius (E := E)
  obtain ⟨height, hp, hn, hs⟩ := exists_generic_positive_height (E := E) δ hδ
  refine ⟨height, hp, hs, ?_⟩
  intro s hmem
  apply hδref height hn s
  exact (boundaryVertexFace_iff_heightFace height hp s).mp
    ((mem_boundaryVertexFaces height s).mp hmem)

end ResearchMain.PreorderGamma.SimplicialRealization
