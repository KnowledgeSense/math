import MainTheorems.SIBOProximity
import MainTheorems.BasisPairing
import MainTheorems.RadixLabels

namespace ResearchMain.SIBO

open scoped BigOperators

def sideBasis (r : ℕ) (b : Bool) : Finset (Fin r × Bool) := Finset.univ ×ˢ {b}

@[simp] theorem sideBasis_card (r : ℕ) (b : Bool) : (sideBasis r b).card = r := by
  simp [sideBasis]

theorem sideBasis_disjoint (r : ℕ) : Disjoint (sideBasis r false) (sideBasis r true) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [sideBasis, Finset.mem_product, Finset.mem_singleton] at hx hy
  exact Bool.false_ne_true (hx.2.symm.trans hy.2)

noncomputable def sharpUniform (qs : List ℕ) : Matroid (Fin (radixSize qs - 1) × Bool) :=
  uniformMatroid (radixSize qs - 1) (by simp; omega)

theorem sharp_label_group_finite (qs : List ℕ) (t : Fin qs.length) :
    Finite (ZMod (radixPrefix qs (t.val + 1))) := by
  let _ : NeZero (radixPrefix qs (t.val + 1)) := ⟨Nat.ne_of_gt (radixSize_pos _)⟩
  infer_instance

def sharpLabel (qs : List ℕ) (t : Fin qs.length)
    (e : Fin (radixSize qs - 1) × Bool) : ZMod (radixPrefix qs (t.val + 1)) :=
  if e.2 then 1 else 0

theorem sharp_forbidden_bound (qs : List ℕ) :
    (∏ t : Fin qs.length, ((radixForbidden qs t).card + 1)) = radixSize qs := by
  simp only [radixForbidden_card, radixSize]
  exact Fin.prod_univ_fun_getElem qs (fun q => q + 1)

theorem sharpLabel_sum (qs : List ℕ) (t : Fin qs.length)
    (X : Finset (Fin (radixSize qs - 1) × Bool)) :
    (∑ e ∈ X, sharpLabel qs t e) =
      ((X ∩ sideBasis (radixSize qs - 1) true).card : ZMod (radixPrefix qs (t.val + 1))) := by
  have hf : X.filter (fun e => e.2 = true) = X ∩ sideBasis (radixSize qs - 1) true := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_inter, sideBasis, Finset.mem_product,
      Finset.mem_univ, Finset.mem_singleton, true_and]
  rw [← hf]
  simp only [sharpLabel, ← Finset.sum_filter]
  simp

theorem sharpUniform_isBase (qs : List ℕ) (X : Finset (Fin (radixSize qs - 1) × Bool)) :
    (sharpUniform qs).IsBase (X : Set _) ↔ X.card = radixSize qs - 1 := by
  simp [sharpUniform]

theorem sharpLabel_feasible (qs : List ℕ) :
    Feasible (sharpLabel qs) (radixForbidden qs) (sideBasis (radixSize qs - 1) true) := by
  intro t
  rw [sharpLabel_sum, Finset.inter_self, sideBasis_card]
  exact maximal_occupancy_feasible qs t

theorem sharpLabel_unique (qs : List ℕ) (X : Finset (Fin (radixSize qs - 1) × Bool))
    (hX : (sharpUniform qs).IsBase (X : Set _))
    (hF : Feasible (sharpLabel qs) (radixForbidden qs) X) :
    X = sideBasis (radixSize qs - 1) true := by
  have hcard := (sharpUniform_isBase qs X).mp hX
  let B := sideBasis (radixSize qs - 1) true
  have hle : (X ∩ B).card ≤ radixSize qs - 1 := by
    simpa [hcard] using Finset.card_le_card (Finset.inter_subset_left (s₁ := X) (s₂ := B))
  have heqcard : (X ∩ B).card = radixSize qs - 1 := by
    by_contra hne
    have hlt : (X ∩ B).card < radixSize qs - 1 := by omega
    obtain ⟨t, ht⟩ := smaller_occupancy_forbidden qs (X ∩ B).card hlt
    apply hF t
    rw [sharpLabel_sum]
    exact ht
  have hIB : X ∩ B = B := Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    (by simpa only [B, sideBasis_card] using heqcard.ge)
  have hsub : B ⊆ X := by rw [← hIB]; exact Finset.inter_subset_left
  exact (Finset.eq_of_subset_of_card_le hsub (by simp [B, hcard])).symm

/-- The product bound is attained for every finite tuple, including zero entries and the empty tuple. -/
theorem sharp_proximity_example (qs : List ℕ) :
    IsSIBO (sharpUniform qs) ∧
    (sharpUniform qs).IsBase (sideBasis (radixSize qs - 1) false : Set _) ∧
    (sharpUniform qs).IsBase (sideBasis (radixSize qs - 1) true : Set _) ∧
    (∀ t, (radixForbidden qs t).card = qs[t]) ∧
    Feasible (sharpLabel qs) (radixForbidden qs) (sideBasis (radixSize qs - 1) true) ∧
    (∀ X : Finset (Fin (radixSize qs - 1) × Bool),
      (sharpUniform qs).IsBase (X : Set _) →
      Feasible (sharpLabel qs) (radixForbidden qs) X →
      X = sideBasis (radixSize qs - 1) true) ∧
    (sideBasis (radixSize qs - 1) false \ sideBasis (radixSize qs - 1) true).card =
      radixSize qs - 1 := by
  refine ⟨uniformMatroid_sibo _ _, ?_, ?_, radixForbidden_card qs,
    sharpLabel_feasible qs, sharpLabel_unique qs, ?_⟩
  · simp [sharpUniform]
  · simp [sharpUniform]
  · rw [Finset.sdiff_eq_self_iff_disjoint.mpr (sideBasis_disjoint _), sideBasis_card]

end ResearchMain.SIBO
