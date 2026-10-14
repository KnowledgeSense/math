import MainTheorems.PreorderGamma.IndicatorDemands
import MainTheorems.PreorderGamma.Enumerators

namespace ResearchMain.PreorderGamma

variable {L R : Type*} [Fintype L] [Fintype R]

omit [Fintype L] [Fintype R] in
noncomputable def indicatorVector (n : ℕ) (s : Finset L) (hs : s.card ≤ n) :
    L → Fin (n + 1) := by
  classical
  intro a
  refine ⟨if a ∈ s then 1 else 0, ?_⟩
  split_ifs with ha
  · have hp : 0 < s.card := Finset.card_pos.mpr ⟨a, ha⟩
    omega
  · omega

omit [Fintype L] [Fintype R] in
theorem indicatorVector_le_one (n : ℕ) (s : Finset L) (hs : s.card ≤ n) :
    ∀ a, (indicatorVector n s hs a).val ≤ 1 := by
  classical
  intro a
  simp only [indicatorVector]
  split_ifs <;> omega

omit [Fintype R] in
theorem indicatorVector_support (n : ℕ) (s : Finset L) (hs : s.card ≤ n) :
    demandSupport (fun a => (indicatorVector n s hs a).val) = s := by
  classical
  ext a
  change a ∈ Finset.univ.filter (fun a => 0 < (indicatorVector n s hs a).val) ↔ a ∈ s
  rw [Finset.mem_filter]
  simp only [Finset.mem_univ, true_and]
  change (0 < if a ∈ s then 1 else 0) ↔ a ∈ s
  by_cases ha : a ∈ s <;> simp [ha]

def MaxSupportDemand (r : L → R → Prop) :=
  {d : L → Fin (Fintype.card R + 1) //
    IsDemand r (fun a => (d a).val) ∧
      (demandSupport fun a => (d a).val).card = Fintype.card R}

def MatchedSupport (r : L → R → Prop) :=
  {s : Finset L // s.card = Fintype.card R ∧
    ∃ f : s ≃ R, ∀ a : s, r a.val (f a)}

noncomputable instance (r : L → R → Prop) : Fintype (MaxSupportDemand r) := by
  classical
  unfold MaxSupportDemand
  infer_instance

noncomputable instance (r : L → R → Prop) : Fintype (MatchedSupport r) := by
  classical
  unfold MatchedSupport
  infer_instance

noncomputable def maxDemandToMatchedSupport (r : L → R → Prop) :
    MaxSupportDemand r → MatchedSupport r :=
  fun d => ⟨demandSupport (fun a => (d.val a).val), d.property.2,
    maximal_support_hasPerfectMatching d.property.1 d.property.2⟩

noncomputable def matchedSupportToMaxDemand (r : L → R → Prop) :
    MatchedSupport r → MaxSupportDemand r := by
  classical
  intro s
  let d := indicatorVector (Fintype.card R) s.val s.property.1.le
  have hsupp : demandSupport (fun a => (d a).val) = s.val :=
    indicatorVector_support _ _ _
  have hd : IsDemand r (fun a => (d a).val) := by
    apply (binary_demand_iff_support_transversal r _ (indicatorVector_le_one _ _ _)).mpr
    rw [hsupp]
    obtain ⟨f, hf⟩ := s.property.2
    exact ⟨f, f.injective, hf⟩
  refine ⟨d, hd, ?_⟩
  rw [hsupp]
  exact s.property.1

noncomputable def maxDemandMatchedSupportEquiv (r : L → R → Prop) :
    MaxSupportDemand r ≃ MatchedSupport r := by
  classical
  refine
    { toFun := maxDemandToMatchedSupport r
      invFun := matchedSupportToMaxDemand r
      left_inv := ?_
      right_inv := ?_ }
  · intro d
    apply Subtype.ext
    funext a
    apply Fin.ext
    have h := maximal_support_is_indicator d.property.1 d.property.2 a
    simpa [maxDemandToMatchedSupport, matchedSupportToMaxDemand, indicatorVector,
      demandSupport] using h.symm
  · intro s
    apply Subtype.ext
    change demandSupport (fun a =>
      (indicatorVector (Fintype.card R) s.val s.property.1.le a).val) = s.val
    exact indicatorVector_support _ _ s.property.1.le

theorem maximal_support_demand_count (r : L → R → Prop) :
    Fintype.card (MaxSupportDemand r) = Fintype.card (MatchedSupport r) :=
  Fintype.card_congr (maxDemandMatchedSupportEquiv r)

theorem supportEnumerator_maximal_coeff (r : L → R → Prop) :
    (supportEnumerator r).coeff (Fintype.card R) =
      Fintype.card (MatchedSupport r) := by
  classical
  calc
    (supportEnumerator r).coeff (Fintype.card R) =
        Fintype.card (MaxSupportDemand r) := by
      rw [supportEnumerator_coeff]
      change _ = Fintype.card
        {d : L → Fin (Fintype.card R + 1) //
          IsDemand r (fun a => (d a).val) ∧
            (demandSupport fun a => (d a).val).card = Fintype.card R}
      rw [Fintype.card_subtype]
      congr 1
      ext d
      simp [demandVectors]
    _ = Fintype.card (MatchedSupport r) := maximal_support_demand_count r

end ResearchMain.PreorderGamma
