import MainTheorems.PreorderGamma.PatternEnumeration
import MainTheorems.PreorderGamma.RestrictedRelation
import MainTheorems.PreorderGamma.Enumerators

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {L R : Type*} [Fintype L] [Fintype R]

def PositiveDemand (r : L → R → Prop) :=
  {d : L → Fin (Fintype.card R + 1) //
    IsDemand r (fun a => (d a).val) ∧ ∀ a, 0 < (d a).val}

noncomputable instance (r : L → R → Prop) : Fintype (PositiveDemand r) := by
  classical
  unfold PositiveDemand
  infer_instance

theorem positiveDemand_count (r : L → R → Prop) :
    Fintype.card (PositiveDemand r) = (supportEnumerator r).coeff (Fintype.card L) := by
  classical
  rw [supportEnumerator_fullSupport_coeff]
  change Fintype.card
    {d : L → Fin (Fintype.card R + 1) //
      IsDemand r (fun a => (d a).val) ∧ ∀ a, 0 < (d a).val} = _
  rw [Fintype.card_subtype]
  congr 1
  ext d
  simp [demandVectors]

variable {E : Type*} [Fintype E] [DecidableEq E] [Preorder E]

noncomputable def extendDemand (j : Finset E) (d : j → ℕ) : E → ℕ :=
  fun a => if ha : a ∈ j then d ⟨a, ha⟩ else 0

omit [Fintype E] [Preorder E] in
@[simp] theorem extendDemand_mem (j : Finset E) (d : j → ℕ) (a : j) :
    extendDemand j d a.val = d a := by
  simp [extendDemand, a.property]

omit [Fintype E] [Preorder E] in
theorem extendDemand_not_mem (j : Finset E) (d : j → ℕ) {a : E} (ha : a ∉ j) :
    extendDemand j d a = 0 := by
  simp [extendDemand, ha]

abbrev FixedPattern (z j : Finset E) :=
  {p : SurplusPattern E // p.zeros = z ∧ p.high = j}

noncomputable instance (z j : Finset E) : Fintype (FixedPattern z j) := by
  classical
  unfold FixedPattern
  infer_instance

theorem fixedPattern_demand {z j : Finset E} (p : FixedPattern z j) :
    IsDemand (fun a : j => fun b : z => (b : E) ≤ (a : E))
      (fun a => p.val.demand a.val) := by
  apply (restrictedDemand_iff_subsetHall z j _).mpr
  intro s hs
  have h := p.val.hall s (by simpa only [p.property.2] using hs)
  simpa only [p.property.1] using h

noncomputable def positiveDemandOfPattern {z j : Finset E} (p : FixedPattern z j) :
    PositiveDemand (fun a : j => fun b : z => (b : E) ≤ (a : E)) := by
  let d : j → Fin (Fintype.card z + 1) := fun a =>
    ⟨p.val.demand a.val,
      Nat.lt_succ_of_le (demand_coordinate_bound (fixedPattern_demand p) a)⟩
  refine ⟨d, fixedPattern_demand p, ?_⟩
  intro a
  exact (p.val.positive_iff a.val).mpr (p.property.2.symm ▸ a.property)

noncomputable def patternOfPositiveDemand (z j : Finset E) (hdis : Disjoint z j)
    (d : PositiveDemand (fun a : j => fun b : z => (b : E) ≤ (a : E))) :
    FixedPattern z j := by
  let p : SurplusPattern E :=
    { zeros := z
      high := j
      disjoint := hdis
      demand := extendDemand j (fun a => (d.val a).val)
      positive_iff := by
        intro a
        by_cases ha : a ∈ j
        · simp [extendDemand, ha, d.property.2 ⟨a, ha⟩]
        · simp [extendDemand, ha]
      hall := by
        apply (restrictedDemand_iff_subsetHall z j _).mp
        simpa only [extendDemand_mem] using d.property.1 }
  exact ⟨p, rfl, rfl⟩

noncomputable def fixedPatternPositiveDemandEquiv (z j : Finset E) (hdis : Disjoint z j) :
    FixedPattern z j ≃
      PositiveDemand (fun a : j => fun b : z => (b : E) ≤ (a : E)) := by
  refine
    { toFun := positiveDemandOfPattern
      invFun := patternOfPositiveDemand z j hdis
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    apply Subtype.ext
    apply surplusPattern_ext
    · exact p.property.1.symm
    · exact p.property.2.symm
    · funext a
      by_cases ha : a ∈ j
      · simp [patternOfPositiveDemand, positiveDemandOfPattern, extendDemand, ha]
      · have hh : a ∉ p.val.high := by rwa [p.property.2]
        have hz : p.val.demand a = 0 :=
          Nat.eq_zero_of_not_pos (fun h => hh ((p.val.positive_iff a).mp h))
        simp [patternOfPositiveDemand, positiveDemandOfPattern, extendDemand, ha, hz]
  · intro d
    apply Subtype.ext
    funext a
    apply Fin.ext
    simp [patternOfPositiveDemand, positiveDemandOfPattern, extendDemand]

theorem patternCount_eq_restricted_fullSupport_coeff (z j : Finset E)
    (hdis : Disjoint z j) :
    patternCount z j =
      (supportEnumerator (fun a : j => fun b : z => (b : E) ≤ (a : E))).coeff j.card := by
  classical
  calc
    patternCount z j = Fintype.card (FixedPattern z j) := by
      unfold patternCount FixedPattern
      rw [Fintype.card_subtype]
    _ = Fintype.card
        (PositiveDemand (fun a : j => fun b : z => (b : E) ≤ (a : E))) :=
      Fintype.card_congr (fixedPatternPositiveDemandEquiv z j hdis)
    _ = _ := by
      simpa using positiveDemand_count (fun a : j => fun b : z => (b : E) ≤ (a : E))

end ResearchMain.PreorderGamma
