import HilbertBipartite.DefectBlocks

namespace HilbertBipartite

@[simp] theorem mem_lowDegreePairs {p q s : Nat} (hs : 1 ≤ s)
    {a : BlockExponent p} {b : BlockExponent q} :
    (a,b) ∈ lowDegreePairs p q s ↔ blockDegree a + blockDegree b < 2*s := by
  classical
  constructor
  · intro h
    obtain ⟨x, hx, he⟩ := Finset.mem_image.mp h
    have he' := congrArg Finsupp.sumFinsuppEquivProdFinsupp.symm he
    simp only [Equiv.symm_apply_apply] at he'
    rw [he'] at hx
    have hd := mem_degreeAtMost.mp hx
    rw [Fintype.sum_sum_type] at hd
    change blockDegree a + blockDegree b ≤ 2*s-1 at hd
    omega
  · intro hd
    apply Finset.mem_image.mpr
    refine ⟨Finsupp.sumFinsuppEquivProdFinsupp.symm (a,b), ?_,
      Finsupp.sumFinsuppEquivProdFinsupp.apply_symm_apply (a,b)⟩
    apply mem_degreeAtMost.mpr
    rw [Fintype.sum_sum_type]
    change blockDegree a + blockDegree b ≤ 2*s-1
    omega

noncomputable def rightDefectExponents (p q s : Nat) : Finset (ExponentPair p q) :=
  (defectExponents q p s).image Prod.swap

@[simp] theorem mem_rightDefectExponents {p q s : Nat} {a : BlockExponent p}
    {b : BlockExponent q} : (a,b) ∈ rightDefectExponents p q s ↔
      2*s ≤ blockDegree a + blockDegree b ∧ halfDegree b + blockDegree a < s := by
  classical
  constructor
  · intro h
    obtain ⟨⟨b',a'⟩, hx, he⟩ := Finset.mem_image.mp h
    have hea : a' = a := congrArg Prod.fst he
    have heb : b' = b := congrArg Prod.snd he
    subst a'; subst b'
    have hx' := mem_defectExponents.mp hx
    omega
  · intro h
    apply Finset.mem_image.mpr
    refine ⟨(b,a), ?_, rfl⟩
    apply mem_defectExponents.mpr
    omega

/-- A disjoint classification of all standard monomials, with no bounded-degree
or parity case omitted. -/
theorem standardExponents_partition (p q s : Nat) (hs : 1 ≤ s) :
    standardExponents p q s =
      (lowDegreePairs p q s ∪ defectExponents p q s) ∪ rightDefectExponents p q s := by
  classical
  ext ⟨a,b⟩
  simp only [mem_standardExponents, Finset.mem_union, mem_lowDegreePairs hs,
    mem_defectExponents, mem_rightDefectExponents, PowerCriterion]
  omega

/-- The number of actual standard exponent pairs equals the complete length
formula in part (a) of the main theorem. The quotient basis is a separate bridge. -/
theorem standardExponents_card (p q s : Nat) (hp : 1 ≤ p) (hq : 1 ≤ q) (hs : 1 ≤ s) :
    (standardExponents p q s).card =
      (2*s+p+q-1).choose (p+q) + correction p q s + correction q p s := by
  classical
  have hlow : Disjoint (lowDegreePairs p q s) (defectExponents p q s) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨a,b⟩ ha hb
    have ha' := (mem_lowDegreePairs hs).mp ha
    have hb' := mem_defectExponents.mp hb
    omega
  have hright : Disjoint (lowDegreePairs p q s ∪ defectExponents p q s)
      (rightDefectExponents p q s) := by
    apply Finset.disjoint_left.mpr
    rintro ⟨a,b⟩ ha hb
    have hb' := mem_rightDefectExponents.mp hb
    rcases Finset.mem_union.mp ha with ha | ha
    · have ha' := (mem_lowDegreePairs hs).mp ha
      omega
    · have ha' := mem_defectExponents.mp ha
      omega
  rw [standardExponents_partition p q s hs, Finset.card_union_of_disjoint hright,
    Finset.card_union_of_disjoint hlow, card_lowDegreePairs p q s hs,
    card_defectExponents p q s hp hq]
  unfold rightDefectExponents
  rw [Finset.card_image_of_injective _ Prod.swap_injective, card_defectExponents q p s hq hp]

end HilbertBipartite
