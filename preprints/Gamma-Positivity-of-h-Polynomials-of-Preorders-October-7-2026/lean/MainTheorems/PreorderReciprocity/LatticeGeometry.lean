import MainTheorems.PreorderReciprocity.IntegerTranslation
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Lean.Elab.Tactic.NormCast
import Mathlib.Tactic.Linarith

namespace ResearchMain.PreorderReciprocity

variable {E : Type*} [Fintype E] [Preorder E]

noncomputable def validIdeals : Finset (Finset E) := by
  classical
  exact Finset.univ.filter fun I => I.Nonempty ∧ IsIdeal I

theorem mem_validIdeals (I : Finset E) :
    I ∈ validIdeals ↔ I.Nonempty ∧ IsIdeal I := by
  classical
  simp [validIdeals]

noncomputable def idealSum (I : Finset E) : (E → ℝ) →L[ℝ] ℝ :=
  ∑ e ∈ I, ContinuousLinearMap.proj e

omit [Fintype E] [Preorder E] in
theorem idealSum_apply (I : Finset E) (x : E → ℝ) :
    idealSum I x = ∑ e ∈ I, x e := by
  simp [idealSum, _root_.sum_apply]

omit [Fintype E] [Preorder E] in
theorem idealSum_surjective (I : Finset E) (hI : I.Nonempty) :
    Function.Surjective (idealSum I) := by
  classical
  obtain ⟨e, he⟩ := hI
  intro t
  refine ⟨Pi.single e t, ?_⟩
  simp [idealSum_apply, Pi.single_apply, he]

noncomputable def polytope (r s : ℝ) : Set (E → ℝ) :=
  (⋂ e : E, (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ) ⁻¹' Set.Ici 0) ∩
    ⋂ I ∈ validIdeals, idealSum I ⁻¹' Set.Iic (r * I.card + s)

theorem mem_polytope (r s : ℝ) (x : E → ℝ) :
    x ∈ polytope r s ↔ (∀ e, 0 ≤ x e) ∧
      ∀ I : Finset E, I.Nonempty → IsIdeal I →
        ∑ e ∈ I, x e ≤ r * I.card + s := by
  simp only [polytope, Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage,
    Set.mem_Ici, Set.mem_Iic, ContinuousLinearMap.proj_apply, idealSum_apply]
  constructor
  · rintro ⟨hp, hb⟩
    exact ⟨hp, fun I hI hIdeal => hb I ((mem_validIdeals I).2 ⟨hI, hIdeal⟩)⟩
  · rintro ⟨hp, hb⟩
    exact ⟨hp, fun I hI => hb I ((mem_validIdeals I).1 hI).1
      ((mem_validIdeals I).1 hI).2⟩

omit [Preorder E] in
theorem interior_coordinate (e : E) :
    interior ((ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ) ⁻¹' Set.Ici 0) =
      {x : E → ℝ | 0 < x e} := by
  have hs : Function.Surjective (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ) :=
    fun t => ⟨fun _ => t, rfl⟩
  rw [ContinuousLinearMap.interior_preimage _ hs, interior_Ici]
  rfl

omit [Preorder E] in
theorem interior_ideal_bound (I : Finset E) (hI : I.Nonempty) (c : ℝ) :
    interior (idealSum I ⁻¹' Set.Iic c) = {x : E → ℝ | ∑ e ∈ I, x e < c} := by
  rw [ContinuousLinearMap.interior_preimage _ (idealSum_surjective I hI), interior_Iic]
  ext x
  simp [idealSum_apply]

theorem mem_interior_polytope (r s : ℝ) (x : E → ℝ) :
    x ∈ interior (polytope r s) ↔ (∀ e, 0 < x e) ∧
      ∀ I : Finset E, I.Nonempty → IsIdeal I →
        ∑ e ∈ I, x e < r * I.card + s := by
  rw [polytope, interior_inter, interior_iInter_of_finite, Finset.interior_iInter]
  simp only [Set.mem_inter_iff, Set.mem_iInter, interior_coordinate, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨hp, ?_⟩
    intro I hI hIdeal
    have h := hb I ((mem_validIdeals I).2 ⟨hI, hIdeal⟩)
    simpa only [interior_ideal_bound I hI, Set.mem_ofPred_eq] using h
  · rintro ⟨hp, hb⟩
    refine ⟨hp, ?_⟩
    intro I hI
    have hn := ((mem_validIdeals I).1 hI).1
    have hIdeal := ((mem_validIdeals I).1 hI).2
    simpa only [interior_ideal_bound I hn, Set.mem_ofPred_eq] using hb I hn hIdeal

theorem integer_mem_polytope (r s : ℤ) (x : E → ℤ) :
    (fun e => (x e : ℝ)) ∈ polytope (r : ℝ) (s : ℝ) ↔ ClosedIntegerPoints r s x := by
  rw [mem_polytope]
  simp only [ClosedIntegerPoints]
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨fun e => by exact_mod_cast hp e, ?_⟩
    intro I hI hIdeal
    exact_mod_cast hb I hI hIdeal
  · rintro ⟨hp, hb⟩
    refine ⟨fun e => by exact_mod_cast hp e, ?_⟩
    intro I hI hIdeal
    exact_mod_cast hb I hI hIdeal

theorem integer_mem_interior (r s : ℤ) (x : E → ℤ) :
    (fun e => (x e : ℝ)) ∈ interior (polytope (r : ℝ) (s : ℝ)) ↔
      StrictIntegerPoints r s x := by
  rw [mem_interior_polytope]
  simp only [StrictIntegerPoints]
  constructor
  · rintro ⟨hp, hb⟩
    refine ⟨fun e => by exact_mod_cast hp e, ?_⟩
    intro I hI hIdeal
    exact_mod_cast hb I hI hIdeal
  · rintro ⟨hp, hb⟩
    refine ⟨fun e => by exact_mod_cast hp e, ?_⟩
    intro I hI hIdeal
    exact_mod_cast hb I hI hIdeal

theorem real_coordinate_bound {r s : ℝ} {x : E → ℝ}
    (hx : x ∈ polytope r s) (e : E) :
    x e ≤ r * Fintype.card E + s := by
  obtain ⟨hp, hb⟩ := (mem_polytope r s x).1 hx
  have he : (Finset.univ : Finset E).Nonempty := ⟨e, Finset.mem_univ e⟩
  have hs := hb Finset.univ he univ_isIdeal
  have hle : x e ≤ ∑ i : E, x i :=
    Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ e)
  simpa using hle.trans hs

theorem box_subset_polytope (r s : ℝ) (hs : 0 ≤ s) :
    {x : E → ℝ | ∀ e, 0 ≤ x e ∧ x e ≤ r} ⊆ polytope r s := by
  intro x hx
  apply (mem_polytope r s x).2
  refine ⟨fun e => (hx e).1, ?_⟩
  intro I _ _
  calc
    ∑ e ∈ I, x e ≤ ∑ _ ∈ I, r := Finset.sum_le_sum fun e _ => (hx e).2
    _ = r * I.card := by simp [mul_comm]
    _ ≤ r * I.card + s := le_add_of_nonneg_right hs

theorem interior_nonempty (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) :
    (interior (polytope (E := E) r s)).Nonempty := by
  refine ⟨fun _ => r / 2, (mem_interior_polytope r s _).2 ⟨?_, ?_⟩⟩
  · intro e
    linarith
  · intro I hI _
    have hc : 0 < (I.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hI
    calc
      ∑ _ ∈ I, r / 2 = (r / 2) * I.card := by simp [mul_comm]
      _ < r * I.card := mul_lt_mul_of_pos_right (by linarith) hc
      _ ≤ r * I.card + s := le_add_of_nonneg_right hs

theorem polytope_isClosed (r s : ℝ) : IsClosed (polytope (E := E) r s) := by
  apply IsClosed.inter
  · exact isClosed_iInter fun e => isClosed_Ici.preimage
      (ContinuousLinearMap.proj e : (E → ℝ) →L[ℝ] ℝ).continuous
  · exact isClosed_iInter fun I => isClosed_iInter fun _ =>
      isClosed_Iic.preimage (idealSum I).continuous

theorem zero_polytope : polytope (E := E) 0 0 = {0} := by
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.2
    funext e
    have hb := real_coordinate_bound hx e
    have hp := ((mem_polytope 0 0 x).1 hx).1 e
    simp only [zero_mul, add_zero] at hb
    exact le_antisymm hb hp
  · rintro rfl
    simp [mem_polytope]

end ResearchMain.PreorderReciprocity
