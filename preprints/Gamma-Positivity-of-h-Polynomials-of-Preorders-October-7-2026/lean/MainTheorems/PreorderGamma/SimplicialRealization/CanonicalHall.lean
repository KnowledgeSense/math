import MainTheorems.PreorderGamma.SimplicialRealization.QuotientHallCuts

namespace ResearchMain.PreorderGamma.SimplicialRealization

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

noncomputable def originalRows (A : Finset (Option E)) : Finset E :=
  Finset.univ.filter fun i => some i ∈ A

omit [Preorder E] in
@[simp] theorem mem_originalRows {A : Finset (Option E)} {i : E} :
    i ∈ originalRows A ↔ some i ∈ A := by
  classical
  simp [originalRows]

omit [Preorder E] in
theorem originalRows_image (A : Finset (Option E)) (hA : none ∉ A) :
    (originalRows A).image some = A := by
  classical
  ext a
  cases a with
  | none => simp [hA]
  | some i => simp

omit [DecidableEq E] in
theorem augmentedNeighbors_of_none {A : Finset (Option E)} (hA : none ∈ A) :
    graphNeighbors augmentedRelation A = Finset.univ := by
  classical
  ext b
  simp only [Finset.mem_univ, iff_true]
  exact mem_graphNeighbors.mpr ⟨none, hA, trivial⟩

theorem augmentedNeighbors_image (A : Finset E) (hA : A.Nonempty) :
    graphNeighbors augmentedRelation (A.image some) =
      insert none ((orderNeighbors A).image some) := by
  classical
  ext b
  cases b with
  | none =>
    simp only [Finset.mem_insert, true_or, iff_true]
    obtain ⟨a, ha⟩ := hA
    exact mem_graphNeighbors.mpr ⟨some a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, trivial⟩
  | some b =>
    simp only [mem_graphNeighbors, Finset.mem_image, Finset.mem_insert,
      Option.some_ne_none, false_or, Option.some.injEq]
    constructor
    · rintro ⟨a, ⟨i, hi, rfl⟩, hba⟩
      exact ⟨b, mem_graphNeighbors.mpr ⟨i, hi, hba⟩, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      obtain ⟨i, hi, hji⟩ := mem_graphNeighbors.mp hj
      exact ⟨some i, ⟨i, hi, rfl⟩, hji⟩

omit [DecidableEq E] [Preorder E] in
theorem canonicalLeftMargin_total (z : E → ℤ) {t : ℕ} (h : positiveMass z ≤ t) :
    (∑ a, canonicalLeftMargin z t a) = t := by
  rw [Fintype.sum_option]
  change t - positiveMass z + positiveMass z = t
  exact Nat.sub_add_cancel h

omit [DecidableEq E] [Preorder E] in
theorem canonicalRightMargin_total (z : E → ℤ) {t : ℕ} (h : negativeMass z ≤ t) :
    (∑ b, canonicalRightMargin z t b) = t := by
  rw [Fintype.sum_option]
  change t - negativeMass z + negativeMass z = t
  exact Nat.sub_add_cancel h

theorem quotientIntegerPoint_canonicalHall {t : ℕ} {z : E → ℤ}
    (hz : QuotientIntegerPoint t z) :
    IsSupplyDemand augmentedRelation (canonicalLeftMargin z t)
      (canonicalRightMargin z t) := by
  classical
  obtain ⟨hp, hn⟩ := quotientIntegerPoint_mass_bounds hz
  intro U
  by_cases hu : none ∈ U
  · rw [augmentedNeighbors_of_none hu, canonicalRightMargin_total z hn]
    calc
      (∑ a ∈ U, canonicalLeftMargin z t a) ≤ ∑ a, canonicalLeftMargin z t a :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
          (fun a ha hnot => Nat.zero_le _)
      _ = t := canonicalLeftMargin_total z hp
  · by_cases hU : U.Nonempty
    · let A := originalRows U
      have hA : A.Nonempty := by
        obtain ⟨a, ha⟩ := hU
        cases a with
        | none => exact (hu ha).elim
        | some i => exact ⟨i, mem_originalRows.mpr ha⟩
      have himage : A.image some = U := originalRows_image U hu
      rw [← himage, augmentedNeighbors_image A hA]
      have hnone : none ∉ (orderNeighbors A).image some := by simp
      rw [Finset.sum_insert hnone]
      have hleft : (∑ a ∈ A.image some, canonicalLeftMargin z t a) =
          ∑ i ∈ A, (z i).toNat := by
        rw [Finset.sum_image]
        · rfl
        · exact fun i hi j hj hij => Option.some.inj hij
      have hright : (∑ b ∈ (orderNeighbors A).image some, canonicalRightMargin z t b) =
          ∑ j ∈ orderNeighbors A, (-z j).toNat := by
        rw [Finset.sum_image]
        · rfl
        · exact fun i hi j hj hij => Option.some.inj hij
      rw [hleft, hright]
      change (∑ i ∈ A, (z i).toNat) ≤
        t - negativeMass z + ∑ j ∈ orderNeighbors A, (-z j).toNat
      have hcut := quotientIntegerPoint_hall_cut hz A
      have hsum := Finset.sum_sdiff (f := fun j => (-z j).toNat)
        (Finset.subset_univ (orderNeighbors A))
      change (∑ j ∈ Finset.univ \ orderNeighbors A, (-z j).toNat) +
        (∑ j ∈ orderNeighbors A, (-z j).toNat) = negativeMass z at hsum
      omega
    · have hU0 : U = ∅ := Finset.not_nonempty_iff_eq_empty.mp hU
      simp [hU0]

theorem quotientIntegerPoint_isCanonicalDegree {t : ℕ} {z : E → ℤ}
    (hz : QuotientIntegerPoint t z) : IsCanonicalDegree z t := by
  obtain ⟨hp, hn⟩ := quotientIntegerPoint_mass_bounds hz
  refine ⟨hp, hn, naturalTransport_supplyDemand _ _ _
    (quotientIntegerPoint_canonicalHall hz) ?_⟩
  exact (canonicalLeftMargin_total z hp).trans (canonicalRightMargin_total z hn).symm

end ResearchMain.PreorderGamma.SimplicialRealization
