import GenericValueSemigroups.WeightEnumeration
import GenericValueSemigroups.DigitWeights
import Mathlib.Data.Fintype.Sort
import Mathlib.Data.Fintype.Fin
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.NormNum

namespace GenericValueSemigroups
open scoped BigOperators Classical

/-- An integer linear functional that orders by weight and separates ties. -/
def orderedWeightKey {d : ℕ} (r : Fin d → ℕ) (N : ℕ) (α : Fin d → ℕ) : ℕ :=
  (N + 2) ^ d * weight r α + digitWeight (N + 2) α

theorem digitWeight_lt_window {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (N : ℕ) (α : weightSet r N) : digitWeight (N+2) α.val < (N+2)^d := by
  apply digitWeight_lt _ (by omega)
  intro i
  have hi := coordinate_le_weight r α.val hr i
  have hw := (mem_weightSet r hr N α.val).mp α.property
  omega

theorem orderedWeightKey_lt_of_weight_lt {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (N : ℕ) (α β : weightSet r N)
    (h : weight r α.val < weight r β.val) :
    orderedWeightKey r N α.val < orderedWeightKey r N β.val := by
  have ha := digitWeight_lt_window r hr N α
  unfold orderedWeightKey
  calc
    (N + 2)^d * weight r α.val + digitWeight (N+2) α.val <
        (N+2)^d * weight r α.val + (N+2)^d := Nat.add_lt_add_left ha _
    _ = (N+2)^d * (weight r α.val + 1) := by ring
    _ ≤ (N+2)^d * weight r β.val := Nat.mul_le_mul_left _ h
    _ ≤ (N+2)^d * weight r β.val + digitWeight (N+2) β.val := Nat.le_add_right _ _

theorem orderedWeightKey_injective {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (N : ℕ) :
    Function.Injective (fun α : weightSet r N => orderedWeightKey r N α.val) := by
  intro α β h
  change orderedWeightKey r N α.val = orderedWeightKey r N β.val at h
  have hw : weight r α.val = weight r β.val := by
    rcases lt_trichotomy (weight r α.val) (weight r β.val) with hl | he | hg
    · have := orderedWeightKey_lt_of_weight_lt r hr N α β hl; omega
    · exact he
    · have := orderedWeightKey_lt_of_weight_lt r hr N β α hg; omega
  apply Subtype.ext
  apply digitWeight_injective_on_bounded (N+2) (by omega)
  · intro i
    have hi := coordinate_le_weight r α.val hr i
    have hh := (mem_weightSet r hr N α.val).mp α.property
    omega
  · intro i
    have hi := coordinate_le_weight r β.val hr i
    have hh := (mem_weightSet r hr N β.val).mp β.property
    omega
  · simpa only [orderedWeightKey, hw, Nat.add_right_inj] using h

/-- The finite monomials, sorted by weight with an injective digit tie-breaker. -/
noncomputable def orderedWeightEquiv {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (N : ℕ) : Fin (weightCount r N) ≃ weightSet r N := by
  let : LinearOrder (weightSet r N) := LinearOrder.lift' (fun α : weightSet r N => orderedWeightKey r N α.val)
    (orderedWeightKey_injective r hr N)
  exact (monoEquivOfFin (weightSet r N) (by simp [weightCount])).toEquiv

theorem orderedWeightEquiv_key_strictMono {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (N : ℕ) :
    StrictMono (fun j => orderedWeightKey r N (orderedWeightEquiv r hr N j).val) := by
  let : LinearOrder (weightSet r N) := LinearOrder.lift' (fun α : weightSet r N => orderedWeightKey r N α.val)
    (orderedWeightKey_injective r hr N)
  have h := @OrderIso.strictMono _ _ inferInstance this.toPartialOrder.toPreorder
    (monoEquivOfFin (weightSet r N) (k := weightCount r N) (by simp [weightCount]))
  exact h

theorem orderedWeightEquiv_weight_mono {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (N : ℕ) :
    Monotone (fun j => weight r (orderedWeightEquiv r hr N j).val) := by
  intro i j hij
  by_contra hw
  have hk := orderedWeightKey_lt_of_weight_lt r hr N
    (orderedWeightEquiv r hr N j) (orderedWeightEquiv r hr N i) (Nat.lt_of_not_ge hw)
  have hm := (orderedWeightEquiv_key_strictMono r hr N).monotone hij
  omega

theorem weightCount_eq_card_enumeration_filter {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (N n : ℕ) (hn : n ≤ N)
    (e : Fin (weightCount r N) ≃ weightSet r N) :
    weightCount r n = (Finset.univ.filter (fun j => weight r (e j).val < n)).card := by
  have hi : Function.Injective (fun j => (e j).val) := Subtype.val_injective.comp e.injective
  have he : (Finset.univ.filter (fun j => weight r (e j).val < n)).image
      (fun j => (e j).val) = weightSet r n := by
    ext α
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact (mem_weightSet r hr n _).mpr hj
    · intro hα
      have hαN : α ∈ weightSet r N := (mem_weightSet r hr N α).mpr
        (lt_of_lt_of_le ((mem_weightSet r hr n α).mp hα) hn)
      refine ⟨e.symm ⟨α, hαN⟩, ?_, ?_⟩
      · simpa using (mem_weightSet r hr n α).mp hα
      · simp
  rw [← Finset.card_image_of_injective _ hi, he]
  rfl

/-- Every finite sorted enumeration agrees with the multiplicity-sensitive weight sequence. -/
theorem enumeration_weight_eq_weightAt {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (N : ℕ)
    (e : Fin (weightCount r N) ≃ weightSet r N)
    (hm : Monotone (fun j => weight r (e j).val)) (j : Fin (weightCount r N)) :
    weight r (e j).val = weightAt r hr hd j.val := by
  have hwN := (mem_weightSet r hr N (e j).val).mp (e j).property
  have hlower : weightCount r (weight r (e j).val) ≤ j.val := by
    rw [weightCount_eq_card_enumeration_filter r hr N _ (by omega) e]
    calc
      _ ≤ (Finset.univ.filter (fun i : Fin (weightCount r N) => i.val < j.val)).card := by
        apply Finset.card_le_card
        intro i hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
        by_contra hij
        have hh := hm (show j ≤ i by exact Nat.le_of_not_gt hij)
        exact (Nat.not_lt_of_ge hh) hi
      _ = j.val := by rw [Fin.card_filter_val_lt, Nat.min_eq_right (Nat.le_of_lt j.isLt)]
  have hupper : j.val < weightCount r (weight r (e j).val + 1) := by
    rw [weightCount_eq_card_enumeration_filter r hr N (weight r (e j).val + 1) (by omega) e]
    have hc : (Finset.univ.filter (fun i : Fin (weightCount r N) => i.val < j.val+1)).card ≤
        (Finset.univ.filter (fun i => weight r (e i).val < weight r (e j).val+1)).card := by
      apply Finset.card_le_card
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have hh := hm (show i ≤ j by exact Nat.le_of_lt_succ hi)
      exact Nat.lt_succ_of_le hh
    rw [Fin.card_filter_val_lt, Nat.min_eq_right j.isLt] at hc
    omega
  have hle : weightAt r hr hd j.val ≤ weight r (e j).val :=
    Nat.lt_succ_iff.mp ((weightAt_lt_iff r hr hd j.val _).mpr hupper)
  have hge : weight r (e j).val ≤ weightAt r hr hd j.val := by
    by_contra hh
    have hc := (weightAt_lt_iff r hr hd j.val _).mp (Nat.lt_of_not_ge hh)
    omega
  exact Nat.le_antisymm hge hle

theorem orderedWeightEquiv_weight {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (N : ℕ) (j : Fin (weightCount r N)) :
    weight r (orderedWeightEquiv r hr N j).val = weightAt r hr hd j.val :=
  enumeration_weight_eq_weightAt r hr hd N _ (orderedWeightEquiv_weight_mono r hr N) j

/-- The positive coordinate parameters of the exponential witness. -/
noncomputable def orderedWeightCoefficient {d : ℕ} (r : Fin d → ℕ) (N : ℕ)
    (i : Fin d) : ℝ := (((N+2)^d * r i + (N+2)^i.val : ℕ) : ℝ)

theorem orderedWeightCoefficient_pos {d : ℕ} (r : Fin d → ℕ) (N : ℕ)
    (i : Fin d) : 0 < orderedWeightCoefficient r N i := by
  unfold orderedWeightCoefficient
  exact_mod_cast (Nat.add_pos_right ((N+2)^d * r i) (Nat.pow_pos (by omega)))

theorem orderedWeightKey_eq_sum {d : ℕ} (r α : Fin d → ℕ) (N : ℕ) :
    orderedWeightKey r N α = ∑ i, α i * ((N+2)^d * r i + (N+2)^i.val) := by
  simp only [orderedWeightKey, weight, digitWeight, Finset.mul_sum,
    Nat.mul_add, Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem orderedWeightCoefficient_dot {d : ℕ} (r α : Fin d → ℕ) (N : ℕ) :
    (∑ i, (α i : ℝ) * orderedWeightCoefficient r N i) = (orderedWeightKey r N α : ℝ) := by
  rw [orderedWeightKey_eq_sum]
  simp [orderedWeightCoefficient]

/-- The exponential node of each enumerated monomial is its coordinate dot product. -/
noncomputable def orderedWeightNode {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (N : ℕ) (j : Fin (weightCount r N)) : ℝ :=
  ∑ i, ((orderedWeightEquiv r hr N j).val i : ℝ) * orderedWeightCoefficient r N i

theorem orderedWeightNode_eq_key {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (N : ℕ) (j : Fin (weightCount r N)) :
    orderedWeightNode r hr N j = (orderedWeightKey r N (orderedWeightEquiv r hr N j).val : ℝ) :=
  orderedWeightCoefficient_dot r _ N

theorem orderedWeightNode_strictMono {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (N : ℕ) : StrictMono (orderedWeightNode r hr N) := by
  intro i j hij
  rw [orderedWeightNode_eq_key, orderedWeightNode_eq_key]
  exact_mod_cast (orderedWeightEquiv_key_strictMono r hr N hij)

theorem weightCount_pos {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    {N : ℕ} (hN : 0 < N) : 0 < weightCount r N := by
  apply Finset.card_pos.mpr
  refine ⟨fun _ => 0, (mem_weightSet r hr N _).mpr ?_⟩
  simpa [weight] using hN

theorem orderedWeightEquiv_zero {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (N : ℕ)
    (j : Fin (weightCount r N)) (hj : j.val = 0) :
    (orderedWeightEquiv r hr N j).val = fun _ => 0 := by
  funext i
  have h := coordinate_le_weight r (orderedWeightEquiv r hr N j).val hr i
  rw [orderedWeightEquiv_weight r hr hd, hj, weightAt_zero] at h
  exact Nat.eq_zero_of_le_zero h

theorem orderedWeightNode_zero {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (N : ℕ)
    (j : Fin (weightCount r N)) (hj : j.val = 0) : orderedWeightNode r hr N j = 0 := by
  simp [orderedWeightNode, orderedWeightEquiv_zero r hr hd N j hj]

theorem orderedWeightNode_pos {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (N : ℕ)
    (j : Fin (weightCount r N)) (hj : 0 < j.val) : 0 < orderedWeightNode r hr N j := by
  let z : Fin (weightCount r N) := ⟨0, lt_trans hj j.isLt⟩
  have hz := orderedWeightNode_zero r hr hd N z rfl
  have hlt := orderedWeightNode_strictMono r hr N (show z < j from hj)
  rwa [hz] at hlt

end GenericValueSemigroups
