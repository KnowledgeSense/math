import MainTheorems.PreorderGamma.SimplicialRealization.RadialBoundary
import MainTheorems.PreorderGamma.SimplicialRealization.BoundarySubsets

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

def InOpenBoundaryCone (s : Finset (QuotientIndex E)) (x : E → ℝ) : Prop :=
  ∃ c : s → ℝ, (∀ v, 0 < c v) ∧ (∑ v : s, c v • v.val.val) = x

theorem every_point_in_open_boundary_cone (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (hsimp : HasSimplicialBoundary height)
    (x : E → ℝ) : ∃ s ∈ boundaryVertexFaces height, InOpenBoundaryCone s x := by
  classical
  by_cases hx : x = 0
  · refine ⟨∅, (mem_boundaryVertexFaces height ∅).mpr (Or.inl rfl), ?_⟩
    refine ⟨fun v => False.elim (Finset.notMem_empty v.val v.property), ?_, ?_⟩
    · intro v
      exact False.elim (Finset.notMem_empty v.val v.property)
    · simp only [hx, Finset.univ_eq_empty, Finset.sum_empty]
  · obtain ⟨a, ha, hy⟩ := radial_boundary_point height hheight x hx
    let y := a⁻¹ • x
    obtain ⟨l, hl, hb, hm⟩ := boundary_point_support height hheight y hy
    have hymem : y ∈ projectivePolytope height :=
      (projectivePolytope_compact height).isClosed.closure_eq ▸ hy.1
    obtain ⟨w, hw, hw1, hwy⟩ := projectivePolytope_weights height hymem
    have hgap : (∑ v, w v * (l y - l (projectiveVertex height v))) = 0 := by
      calc
        _ = (∑ v, w v) * l y - l (∑ v, w v • projectiveVertex height v) := by
          simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul,
            map_sum, map_smul, smul_eq_mul]
        _ = 0 := by rw [hw1, hwy]; ring
    have htight : ∀ v, 0 < w v → l (projectiveVertex height v) = l y := by
      intro v hv
      have hz := (Finset.sum_eq_zero_iff_of_nonneg
        (fun v _ => mul_nonneg (hw v) (sub_nonneg.mpr (hb v)))).mp hgap
        v (Finset.mem_univ v)
      have hz' : l y - l (projectiveVertex height v) = 0 :=
        (mul_eq_zero.mp hz).resolve_left (ne_of_gt hv)
      exact (sub_eq_zero.mp hz').symm
    obtain ⟨v, hv, hvpos⟩ := (Finset.sum_pos_iff_of_nonneg
      (fun v _ => hw v)).mp (show 0 < ∑ v, w v by rw [hw1]; norm_num)
    let F : Finset (QuotientIndex E) := Finset.univ.filter
      (fun v => l (projectiveVertex height v) = l y)
    let S : Finset (QuotientIndex E) := Finset.univ.filter (fun v => 0 < w v)
    have hF : F ∈ boundaryVertexFaces height := by
      apply (mem_boundaryVertexFaces height F).mpr
      refine Or.inr ⟨l, hl, l y, hb, ?_, ?_⟩
      · intro v
        simp [F]
      · exact ⟨v, by simp [F, htight v hvpos]⟩
    have hSF : S ⊆ F := by
      intro v hv
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
        htight v (Finset.mem_filter.mp hv).2⟩
    have hS : S ∈ boundaryVertexFaces height :=
      boundaryVertexFaces_subset height hheight hsimp F S hF hSF
    have hout : ∀ v ∉ S, w v = 0 := by
      intro v hv
      have hn : ¬0 < w v := by simpa [S] using hv
      exact le_antisymm (le_of_not_gt hn) (hw v)
    have hsumS : (∑ v : S, w v.val • projectiveVertex height v.val) = y := by
      rw [Finset.sum_coe_sort S (fun v => w v • projectiveVertex height v)]
      calc
        _ = ∑ v, w v • projectiveVertex height v :=
          Finset.sum_subset (Finset.subset_univ S)
            (fun v _ hv => by rw [hout v hv, zero_smul])
        _ = y := hwy
    let c : S → ℝ := fun v => a * w v.val / height v.val
    refine ⟨S, hS, c, ?_, ?_⟩
    · intro v
      exact div_pos (mul_pos ha (Finset.mem_filter.mp v.property).2) (hheight v.val)
    · calc
        _ = a • (∑ v : S, w v.val • projectiveVertex height v.val) := by
          rw [Finset.smul_sum]
          apply Finset.sum_congr rfl
          intro v hv
          simp only [c, projectiveVertex, smul_smul, div_eq_mul_inv]
          rw [mul_assoc]
        _ = x := by rw [hsumS]; exact smul_inv_smul₀ (ne_of_gt ha) x

noncomputable def heightMass (height : QuotientIndex E → ℝ)
    (s : Finset (QuotientIndex E)) (c : s → ℝ) : ℝ :=
  ∑ v : s, c v * height v.val

theorem heightFace_mass (height : QuotientIndex E → ℝ)
    (s : Finset (QuotientIndex E)) (c : s → ℝ)
    (l : (E → ℝ) →ₗ[ℝ] ℝ) (ht : ∀ v ∈ s, l v.val = height v) :
    l (∑ v : s, c v • v.val.val) = heightMass height s c := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro v hv
  rw [map_smul, ht v.val v.property, smul_eq_mul]

theorem positive_heightMass (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (s : Finset (QuotientIndex E))
    (hs : s.Nonempty) (c : s → ℝ) (hc : ∀ v, 0 < c v) : 0 < heightMass height s c := by
  obtain ⟨v, hv⟩ := hs
  have hp : 0 < c ⟨v, hv⟩ * height v := mul_pos (hc _) (hheight _)
  have hle : c ⟨v, hv⟩ * height v ≤ heightMass height s c :=
    Finset.single_le_sum (f := fun i : s => c i * height i.val)
      (fun i _ => mul_nonneg (hc i).le (hheight i.val).le)
      (Finset.mem_univ (⟨v, hv⟩ : s))
  exact hp.trans_le hle

theorem open_boundary_cone_zero_iff (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (s : Finset (QuotientIndex E))
    (hs : s ∈ boundaryVertexFaces height) : InOpenBoundaryCone s 0 ↔ s = ∅ := by
  classical
  constructor
  · rintro ⟨c, hc, hz⟩
    by_contra hne
    have hn : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    have hf := (boundaryVertexFace_iff_heightFace height hheight s).mp
      ((mem_boundaryVertexFaces height s).mp hs)
    rcases hf with hzero | ⟨l, hl, hb, ht, hn'⟩
    · exact hne hzero
    · have hm := heightFace_mass height s c l (fun v hv => (ht v).mp hv)
      rw [hz, map_zero] at hm
      exact (ne_of_gt (positive_heightMass height hheight s hn c hc)) hm.symm
  · rintro rfl
    refine ⟨fun v => False.elim (Finset.notMem_empty v.val v.property), ?_, ?_⟩
    · intro v
      exact False.elim (Finset.notMem_empty v.val v.property)
    · simp

theorem open_boundary_cones_unique (height : QuotientIndex E → ℝ)
    (hheight : ∀ v, 0 < height v) (s t : Finset (QuotientIndex E))
    (hs : s ∈ boundaryVertexFaces height) (ht : t ∈ boundaryVertexFaces height)
    (x : E → ℝ) (hxs : InOpenBoundaryCone s x) (hxt : InOpenBoundaryCone t x) : s = t := by
  classical
  by_cases hx : x = 0
  · rw [hx] at hxs hxt
    exact ((open_boundary_cone_zero_iff height hheight s hs).mp hxs).trans
      ((open_boundary_cone_zero_iff height hheight t ht).mp hxt).symm
  have hsne : s.Nonempty := by
    by_contra h
    have hzero : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨c, hc, hsum⟩ := hxs
    subst s
    apply hx
    simpa using hsum.symm
  have htne : t.Nonempty := by
    by_contra h
    have hzero : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
    obtain ⟨c, hc, hsum⟩ := hxt
    subst t
    apply hx
    simpa using hsum.symm
  obtain ⟨c, hc, hcx⟩ := hxs
  obtain ⟨d, hd, hdx⟩ := hxt
  have hsface := (boundaryVertexFace_iff_heightFace height hheight s).mp
    ((mem_boundaryVertexFaces height s).mp hs)
  have htface := (boundaryVertexFace_iff_heightFace height hheight t).mp
    ((mem_boundaryVertexFaces height t).mp ht)
  rcases hsface with hs0 | ⟨ls, hls, hbs, hts, hns⟩
  · simp [hs0] at hsne
  rcases htface with ht0 | ⟨lt, hlt, hbt, htt, hnt⟩
  · simp [ht0] at htne
  have hms : ls x = heightMass height s c := by
    rw [← hcx]
    exact heightFace_mass height s c ls (fun v hv => (hts v).mp hv)
  have hmt : lt x = heightMass height t d := by
    rw [← hdx]
    exact heightFace_mass height t d lt (fun v hv => (htt v).mp hv)
  have hst : heightMass height s c ≤ heightMass height t d := by
    rw [← hms, ← hdx, map_sum]
    apply Finset.sum_le_sum
    intro v hv
    simpa only [map_smul, smul_eq_mul] using
      mul_le_mul_of_nonneg_left (hbs v.val) (hd v).le
  have hts' : heightMass height t d ≤ heightMass height s c := by
    rw [← hmt, ← hcx, map_sum]
    apply Finset.sum_le_sum
    intro v hv
    simpa only [map_smul, smul_eq_mul] using
      mul_le_mul_of_nonneg_left (hbt v.val) (hc v).le
  have heq := le_antisymm hst hts'
  have htsub : t ⊆ s := by
    have hgap : (∑ v : t, d v * (height v.val - ls v.val.val)) = 0 := by
      calc
        _ = heightMass height t d - ls (∑ v : t, d v • v.val.val) := by
          simp only [heightMass, mul_sub, Finset.sum_sub_distrib,
            map_sum, map_smul, smul_eq_mul]
        _ = 0 := by rw [hdx, hms, heq]; simp
    intro v hv
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v _ => mul_nonneg (hd v).le (sub_nonneg.mpr (hbs v.val)))).mp hgap
      ⟨v, hv⟩ (Finset.mem_univ _)
    apply (hts v).mpr
    have hz' := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hd ⟨v, hv⟩))
    exact (sub_eq_zero.mp hz').symm
  have hssub : s ⊆ t := by
    have hgap : (∑ v : s, c v * (height v.val - lt v.val.val)) = 0 := by
      calc
        _ = heightMass height s c - lt (∑ v : s, c v • v.val.val) := by
          simp only [heightMass, mul_sub, Finset.sum_sub_distrib,
            map_sum, map_smul, smul_eq_mul]
        _ = 0 := by rw [hcx, hmt, heq]; simp
    intro v hv
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun v _ => mul_nonneg (hc v).le (sub_nonneg.mpr (hbt v.val)))).mp hgap
      ⟨v, hv⟩ (Finset.mem_univ _)
    apply (htt v).mpr
    have hz' := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hc ⟨v, hv⟩))
    exact (sub_eq_zero.mp hz').symm
  exact Finset.Subset.antisymm hssub htsub

end ResearchMain.PreorderGamma.SimplicialRealization
