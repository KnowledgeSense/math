import MainTheorems.AHOConstants.Circulation
import Mathlib.Data.Finset.Card

namespace ResearchMain.AHOConstants

open scoped BigOperators

variable {m : ℕ}

def aEndpoint (e : Fin (m + 1) × Bool) : Fin (m + 1) :=
  if e.2 then finRotate (m + 1) e.1 else e.1

noncomputable def edgeValue (a b : Fin (m + 1) → ℝ) (e : Fin (m + 1) × Bool) : ℝ :=
  if e.2 then b e.1 else a e.1

noncomputable def cutMass (p : Fin (m + 1) → ℝ) (S : Finset (Fin (m + 1))) : ℝ :=
  ∑ i, if i ∈ S then p i else 0

def cutEdges (S T : Finset (Fin (m + 1))) : Finset (Fin (m + 1) × Bool) :=
  Finset.univ.filter (fun e => aEndpoint e ∈ S ∧ e.1 ∈ T)

noncomputable def cutCapacity (p q : Fin (m + 1) → ℝ)
    (S T : Finset (Fin (m + 1))) : ℝ :=
  2 - cutMass p S - cutMass q T + (cutEdges S T).card / 2

theorem Circulation.a_cut_mass {p q a b : Fin (m + 1) → ℝ}
    (h : Circulation p q a b) (S : Finset (Fin (m + 1))) :
    (∑ e : Fin (m + 1) × Bool,
      if aEndpoint e ∈ S then edgeValue a b e else 0) = cutMass p S := by
  have hs := Equiv.sum_comp (finRotate (m + 1))
    (fun i => if i ∈ S then p i else 0)
  have ha := Equiv.sum_comp (finRotate (m + 1))
    (fun i => if i ∈ S then a i else 0)
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, aEndpoint, edgeValue, Bool.false_eq_true, ite_false, ite_true]
  have hp :
      (∑ i, if finRotate (m + 1) i ∈ S then p (finRotate (m + 1) i) else 0) =
      ∑ i, ((if finRotate (m + 1) i ∈ S then a (finRotate (m + 1) i) else 0) +
        (if finRotate (m + 1) i ∈ S then b i else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : finRotate (m + 1) i ∈ S
    · simp only [hi, ite_true]
      exact (h.2.2 i).symm
    · simp only [hi, ite_false, zero_add]
  simp only [Finset.sum_add_distrib] at hp ⊢
  rw [ha, hs] at hp
  dsimp [cutMass] at hp ⊢
  linarith

theorem Circulation.b_cut_mass {p q a b : Fin (m + 1) → ℝ}
    (h : Circulation p q a b) (T : Finset (Fin (m + 1))) :
    (∑ e : Fin (m + 1) × Bool, if e.1 ∈ T then edgeValue a b e else 0) =
      cutMass q T := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, edgeValue, Bool.false_eq_true, ite_false, ite_true]
  unfold cutMass
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ T
  · simp only [hi, ite_true]
    linarith [h.2.1 i]
  · simp [hi]

theorem Circulation.edge_total {p q a b : Fin (m + 1) → ℝ}
    (h : Circulation p q a b) :
    (∑ e : Fin (m + 1) × Bool, edgeValue a b e) = ∑ i, q i := by
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, edgeValue, Bool.false_eq_true, ite_false, ite_true]
  apply Finset.sum_congr rfl
  intro i _
  linarith [h.2.1 i]

theorem Circulation.edge_bounds {p q a b : Fin (m + 1) → ℝ}
    (h : Circulation p q a b) (e : Fin (m + 1) × Bool) :
    0 ≤ edgeValue a b e ∧ edgeValue a b e ≤ 1 / 2 := by
  have hb := h.1 e.1
  cases he : e.2 <;> simp only [edgeValue, he, Bool.false_eq_true, ite_false, ite_true]
  · exact ⟨hb.1, hb.2.1⟩
  · exact ⟨hb.2.2.1, hb.2.2.2⟩

theorem Circulation.cut_lower_bound {p q a b : Fin (m + 1) → ℝ}
    (h : Circulation p q a b) (hq : (∑ i, q i) = 1)
    (S T : Finset (Fin (m + 1))) : 1 ≤ cutCapacity p q S T := by
  have hedge : ∀ e : Fin (m + 1) × Bool,
      (if aEndpoint e ∈ S then edgeValue a b e else 0) +
        (if e.1 ∈ T then edgeValue a b e else 0) - edgeValue a b e ≤
        if aEndpoint e ∈ S ∧ e.1 ∈ T then (1 / 2 : ℝ) else 0 := by
    intro e
    have hb := h.edge_bounds e
    by_cases hS : aEndpoint e ∈ S <;> by_cases hT : e.1 ∈ T <;>
      simp only [hS, hT, ite_true, ite_false, and_true, and_false] <;> linarith
  have hs := Finset.sum_le_sum (fun e (_ : e ∈ Finset.univ) => hedge e)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, h.a_cut_mass S,
    h.b_cut_mass T, h.edge_total, hq] at hs
  have hcount :
      (∑ e : Fin (m + 1) × Bool,
        if aEndpoint e ∈ S ∧ e.1 ∈ T then (1 / 2 : ℝ) else 0) =
      (cutEdges S T).card / 2 := by
    rw [← Finset.sum_filter]
    simp [cutEdges, div_eq_mul_inv]
  rw [hcount] at hs
  unfold cutCapacity
  linarith

theorem cutMass_nonnegative {p : Fin (m + 1) → ℝ}
    (hp : ∀ i, 0 ≤ p i) (S : Finset (Fin (m + 1))) : 0 ≤ cutMass p S := by
  unfold cutMass
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hp i
  · exact le_rfl

theorem cutMass_le_total {p : Fin (m + 1) → ℝ}
    (hp : ∀ i, 0 ≤ p i) (S : Finset (Fin (m + 1))) : cutMass p S ≤ ∑ i, p i := by
  unfold cutMass
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact hp i

theorem strict_cut_has_at_most_one_edge {p q : Fin (m + 1) → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i)
    (hp₁ : (∑ i, p i) = 1) (hq₁ : (∑ i, q i) = 1)
    {S T : Finset (Fin (m + 1))} (hcut : cutCapacity p q S T < 1) :
    (cutEdges S T).card ≤ 1 := by
  have hS := cutMass_le_total hp S
  have hT := cutMass_le_total hq T
  rw [hp₁] at hS
  rw [hq₁] at hT
  unfold cutCapacity at hcut
  have hcard : ((cutEdges S T).card : ℝ) < 2 := by linarith
  have hcardNat : (cutEdges S T).card < 2 := by exact_mod_cast hcard
  omega

end ResearchMain.AHOConstants
