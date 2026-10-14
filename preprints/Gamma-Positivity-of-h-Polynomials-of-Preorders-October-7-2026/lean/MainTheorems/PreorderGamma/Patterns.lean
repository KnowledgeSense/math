import MainTheorems.PreorderGamma.SurplusHall
import MainTheorems.PreorderGamma.LatticePoints

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

structure SurplusPattern (E : Type*) [Fintype E] [DecidableEq E] [Preorder E] where
  zeros : Finset E
  high : Finset E
  disjoint : Disjoint zeros high
  demand : E → ℕ
  positive_iff : ∀ a, 0 < demand a ↔ a ∈ high
  hall : ∀ s : Finset E, s ⊆ high →
    ∑ a ∈ s, demand a ≤ (neighborhood zeros s).card

def patternPoint (p : SurplusPattern E) (a : E) : ℕ :=
  if a ∈ p.zeros then 0 else 1 + p.demand a

theorem patternPoint_zeroSet (p : SurplusPattern E) :
    zeroSet (patternPoint p) = p.zeros := by
  classical
  ext a
  simp [zeroSet, patternPoint]

theorem patternPoint_highSet (p : SurplusPattern E) :
    highSet (patternPoint p) = p.high := by
  classical
  ext a
  rw [mem_highSet]
  by_cases hz : a ∈ p.zeros
  · have hhigh : a ∉ p.high :=
      fun hh => Finset.disjoint_left.mp p.disjoint hz hh
    simp [patternPoint, hz, hhigh]
  · simp only [patternPoint, ite_eq_right hz]
    exact (show 2 ≤ 1 + p.demand a ↔ 0 < p.demand a by omega).trans (p.positive_iff a)

theorem patternPoint_surplus (p : SurplusPattern E) (a : E) :
    patternPoint p a - 1 = p.demand a := by
  by_cases hz : a ∈ p.zeros
  · have hn : a ∉ p.high := fun hh => Finset.disjoint_left.mp p.disjoint hz hh
    have hzero : p.demand a = 0 := Nat.eq_zero_of_not_pos
      (fun hd => hn ((p.positive_iff a).mp hd))
    simp [patternPoint, hz, hzero]
  · simp [patternPoint, hz]

theorem patternPoint_isLatticePoint (p : SurplusPattern E) :
    IsLatticePoint (patternPoint p) := by
  apply (isLatticePoint_iff_surplusHall _).mpr
  intro s hs
  rw [patternPoint_highSet] at hs
  rw [patternPoint_zeroSet]
  simpa only [patternPoint_surplus] using p.hall s hs

noncomputable def pointPattern (x : {x : E → ℕ // IsLatticePoint x}) : SurplusPattern E := by
  classical
  refine
    { zeros := zeroSet x.val
      high := highSet x.val
      disjoint := ?_
      demand := fun a => x.val a - 1
      positive_iff := ?_
      hall := (isLatticePoint_iff_surplusHall x.val).mp x.property }
  · apply Finset.disjoint_left.mpr
    intro a ha hb
    have hz := mem_zeroSet.mp ha
    have hh := mem_highSet.mp hb
    omega
  · intro a
    rw [mem_highSet]
    omega

theorem patternPoint_pointPattern (x : {x : E → ℕ // IsLatticePoint x}) :
    patternPoint (pointPattern x) = x.val := by
  classical
  funext a
  simp only [patternPoint, pointPattern]
  by_cases hz : x.val a = 0
  · simp [hz]
  · simp [hz]
    omega

theorem surplusPattern_ext {p q : SurplusPattern E}
    (hz : p.zeros = q.zeros) (hh : p.high = q.high) (hd : p.demand = q.demand) : p = q := by
  cases p
  cases q
  cases hz
  cases hh
  cases hd
  rfl

theorem pointPattern_patternPoint (p : SurplusPattern E) :
    pointPattern ⟨patternPoint p, patternPoint_isLatticePoint p⟩ = p := by
  apply surplusPattern_ext
  · exact patternPoint_zeroSet p
  · exact patternPoint_highSet p
  · funext a
    exact patternPoint_surplus p a

noncomputable def latticePointPatternEquiv :
    {x : E → ℕ // IsLatticePoint x} ≃ SurplusPattern E where
  toFun := pointPattern
  invFun := fun p => ⟨patternPoint p, patternPoint_isLatticePoint p⟩
  left_inv := fun x => Subtype.ext (patternPoint_pointPattern x)
  right_inv := pointPattern_patternPoint

theorem patternPoint_support_card (p : SurplusPattern E) :
    (Finset.univ.filter fun a => 0 < patternPoint p a).card =
      Fintype.card E - p.zeros.card := by
  classical
  have h : (Finset.univ.filter fun a => 0 < patternPoint p a) =
      Finset.univ \ p.zeros := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    by_cases hz : a ∈ p.zeros <;> simp [patternPoint, hz]
  rw [h, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]

end ResearchMain.PreorderGamma
