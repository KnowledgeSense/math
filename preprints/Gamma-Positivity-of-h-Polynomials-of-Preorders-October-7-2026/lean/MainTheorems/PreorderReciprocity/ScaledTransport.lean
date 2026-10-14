import MainTheorems.PreorderGamma.Transport
import MainTheorems.PreorderGamma.DemandMatching
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Cast.Basic

namespace ResearchMain.PreorderReciprocity

variable {L R : Type*} [Fintype L] [Fintype R]

def augmentedRelation (r : L → R → Prop) : Option L → R → Prop
  | none, _ => True
  | some a, b => r a b

def scaledDemand (k : ℕ) (x : L → ℕ) : Option L → ℕ
  | none => k * (Fintype.card R - ∑ a, x a) + Fintype.card L
  | some a => k * x a - 1

omit [Fintype L] [Fintype R] in
theorem weighted_injection_fiber_bound {C : Type*} [Fintype C] [DecidableEq R]
    (f : C → R) (hf : Function.Injective f) (w : C → ℕ) (k : ℕ)
    (hw : ∀ c, w c ≤ k) (b : R) :
    (∑ c, if f c = b then w c else 0) ≤ k := by
  classical
  by_cases hc : ∃ c, f c = b
  · obtain ⟨c, hc⟩ := hc
    have hsum : (∑ t, if f t = b then w t else 0) = w c := by
      calc
        _ = if f c = b then w c else 0 := by
          apply Finset.sum_eq_single c
          · intro t ht htc
            have hne : f t ≠ b := fun h => htc (hf (h.trans hc.symm))
            simp only [ite_eq_right hne]
          · simp
        _ = w c := by simp only [ite_eq_left hc]
    rw [hsum]
    exact hw c
  · have hsum : (∑ t, if f t = b then w t else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t ht
      have hne : f t ≠ b := fun h => hc ⟨t, h⟩
      simp only [ite_eq_right hne]
    rw [hsum]
    exact Nat.zero_le k

omit [Fintype L] [Fintype R] in
def scaledCellWeight {x : L → ℕ} (k : ℕ) (c : PreorderGamma.DemandCells x) : ℕ :=
  k - if c.2.val = 0 then 1 else 0

omit [Fintype L] [Fintype R] in
theorem scaledCellWeight_le {x : L → ℕ} (k : ℕ) (c : PreorderGamma.DemandCells x) :
    scaledCellWeight k c ≤ k := Nat.sub_le _ _

omit [Fintype L] [Fintype R] in
theorem scaledCellWeight_row {x : L → ℕ} (k : ℕ) (hk : 0 < k)
    (a : L) (ha : 0 < x a) :
    (∑ c : Fin (x a), scaledCellWeight k ⟨a, c⟩) = k * x a - 1 := by
  classical
  have hdelta : (∑ c : Fin (x a), if c.val = 0 then 1 else 0) = 1 := by
    calc
      _ = if (⟨0, ha⟩ : Fin (x a)).val = 0 then 1 else 0 := by
        apply Finset.sum_eq_single (s := Finset.univ)
          (f := fun c : Fin (x a) => if c.val = 0 then (1 : ℕ) else 0) ⟨0, ha⟩
        · intro c hc hne
          have hv : c.val ≠ 0 := fun h => hne (Fin.ext h)
          simp only [ite_eq_right hv]
        · simp
      _ = 1 := by simp
  change (∑ c : Fin (x a), (k - (if c.val = 0 then 1 else 0))) = _
  rw [Finset.sum_tsub_distrib _ (by
    intro c hc
    split_ifs <;> omega), hdelta]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_id]
  rw [Nat.mul_comm]

theorem scaled_positive_transport_exists (r : L → R → Prop) (x : L → ℕ)
    (hx : PreorderGamma.IsDemand r x) (hpos : ∀ a, 0 < x a)
    (k : ℕ) (hk : 0 < k) :
    Nonempty (PreorderGamma.NaturalTransport (augmentedRelation r)
      (scaledDemand (R := R) k x) (fun _ : R => k)) := by
  classical
  obtain ⟨f, hf, hrel⟩ := (PreorderGamma.demand_iff_cell_transversal r x).mp hx
  let A : L → R → ℕ := fun a b =>
    ∑ c : Fin (x a), if f ⟨a, c⟩ = b then scaledCellWeight k ⟨a, c⟩ else 0
  have hrow : ∀ a, ∑ b, A a b = k * x a - 1 := by
    intro a
    dsimp only [A]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    exact scaledCellWeight_row k hk a (hpos a)
  have hcol : ∀ b, ∑ a, A a b ≤ k := by
    intro b
    change (∑ a, ∑ c : Fin (x a),
      if f ⟨a, c⟩ = b then scaledCellWeight k ⟨a, c⟩ else 0) ≤ k
    rw [← Fintype.sum_sigma']
    exact weighted_injection_fiber_bound f hf (scaledCellWeight k) k
      (scaledCellWeight_le k) b
  have hleft : ∀ a b, ¬r a b → A a b = 0 := by
    intro a b hab
    apply Finset.sum_eq_zero
    intro c hc
    have hne : f ⟨a, c⟩ ≠ b := by
      intro h
      exact hab (h ▸ hrel ⟨a, c⟩)
    exact ite_eq_right hne
  have htotal := PreorderGamma.demand_total_bound hx
  have hmass : Fintype.card L ≤ ∑ a, x a := by
    calc
      _ = ∑ _ : L, 1 := by simp
      _ ≤ _ := Finset.sum_le_sum fun a ha => hpos a
  have hmassk : Fintype.card L ≤ k * ∑ a, x a := by
    apply hmass.trans
    have h1 : 1 ≤ k := by omega
    simpa only [one_mul] using Nat.mul_le_mul_right (∑ a, x a) h1
  have htotalK := Nat.mul_le_mul_left k htotal
  have hdummy : (∑ b, (k - (∑ a, A a b))) =
      k * (Fintype.card R - ∑ a, x a) + Fintype.card L := by
    rw [Finset.sum_tsub_distrib _ (fun b hb => hcol b)]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_comm]
    simp_rw [hrow]
    rw [Finset.sum_tsub_distrib _ (by
      intro a ha
      have h1 : 1 ≤ k := by omega
      have h2 : 1 ≤ x a := hpos a
      have h := Nat.mul_le_mul h1 h2
      simpa only [one_mul] using h)]
    rw [← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_id]
    rw [Nat.mul_sub_left_distrib, Nat.mul_comm (Fintype.card R) k]
    omega
  let F : Option L → R → ℕ
    | none, b => k - ∑ a, A a b
    | some a, b => A a b
  refine ⟨⟨F, ?_, ?_, ?_⟩⟩
  · intro a b hab
    cases a with
    | none => exact False.elim (hab trivial)
    | some a => exact hleft a b hab
  · intro a
    cases a with
    | none => exact hdummy
    | some a => exact hrow a
  · intro b
    rw [Fintype.sum_option]
    exact Nat.sub_add_cancel (hcol b)

end ResearchMain.PreorderReciprocity
