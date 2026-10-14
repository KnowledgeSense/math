import MainTheorems.PreorderGamma.ScaledRecovery
import MainTheorems.PreorderGamma.TransportPotentials

namespace ResearchMain.PreorderGamma

open scoped BigOperators Classical
open PreorderReciprocity

variable {L R : Type*} [Fintype L] [Fintype R]

noncomputable def scaledCoreTransport (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (htree : (transportSupportGraph p).IsTree) :
    NaturalTransport (augmentedRelation (fun a b => r a b ∧ b ∈ transportSplitColumns p))
      (scaledDemand (R := R) k (fun _ => 1)) (fun _ : R => k) := by
  classical
  let B := transportSplitColumns p
  let F : Option L → R → ℕ := fun a b => if b ∈ B then p.flow a b else a.elim k (fun _ => 0)
  have hmargin := scaled_split_row_flow r x hpos k hk p htree
  have hBcard : B.card = Fintype.card L := scaled_split_columns_card r x hpos k hk p htree
  refine ⟨F, ?_, ?_, ?_⟩
  · intro a b hab
    cases a with
    | none => exact False.elim (hab trivial)
    | some a =>
      by_cases hb : b ∈ B
      · have hnot : ¬r a b := fun h => hab ⟨h, hb⟩
        simp only [F, ite_eq_left hb, p.supported (some a) b hnot]
      · simp only [F, ite_eq_right hb, Option.elim_some]
  · intro a
    cases a with
    | none =>
      have hsplit : (∑ b ∈ B, F none b) = transportSplitRowFlow p none := by
        apply Finset.sum_congr rfl
        intro b hb
        simp only [F, ite_eq_left hb]
      have hcomp : (∑ b ∈ Bᶜ, F none b) = (Fintype.card R - Fintype.card L) * k := by
        calc
          _ = ∑ _ ∈ Bᶜ, k := by
            apply Finset.sum_congr rfl
            intro b hb
            simp only [F, ite_eq_right (Finset.mem_compl.mp hb), Option.elim_none]
          _ = _ := by simp [Finset.card_compl, hBcard]
      calc
        _ = (∑ b ∈ B, F none b) + ∑ b ∈ Bᶜ, F none b :=
          (Finset.sum_add_sum_compl B (F none)).symm
        _ = Fintype.card L + (Fintype.card R - Fintype.card L) * k := by
          rw [hsplit, hcomp, hmargin.2]
        _ = _ := by simp [scaledDemand, Nat.mul_comm, Nat.add_comm]
    | some a =>
      have hsum : (∑ b, F (some a) b) = transportSplitRowFlow p (some a) := by
        calc
          _ = ∑ b ∈ B, F (some a) b := by
            symm
            apply Finset.sum_subset (Finset.subset_univ B)
            intro b hb hnot
            simp only [F, ite_eq_right hnot, Option.elim_some]
          _ = _ := by
            apply Finset.sum_congr rfl
            intro b hb
            simp only [F, ite_eq_left hb]
      rw [hsum, hmargin.1 a]
      simp only [scaledDemand, Nat.mul_one]
  · intro b
    by_cases hb : b ∈ B
    · have hpoint : ∀ a, F a b = p.flow a b := by intro a; simp only [F, ite_eq_left hb]
      simp_rw [hpoint]
      exact p.column_sum b
    · rw [Fintype.sum_option]
      simp only [F, ite_eq_right hb, Option.elim_none, Option.elim_some,
        Finset.sum_const_zero, Nat.add_zero]

theorem scaledCoreTransport_flow (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k)) (htree : (transportSupportGraph p).IsTree) (a : Option L) (b : R) :
    (scaledCoreTransport r x hpos k hk p htree).flow a b =
      if b ∈ transportSplitColumns p then p.flow a b else a.elim k (fun _ => 0) := rfl

theorem scaledCoreTransport_minimum (r : L → R → Prop) (x : L → ℕ)
    (hpos : ∀ a, 0 < x a) (k : ℕ) (hk : Fintype.card L < k)
    (p : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k))
    (hp : ∀ q : NaturalTransport (augmentedRelation r) (scaledDemand (R := R) k x)
      (fun _ : R => k), transportCost p ≤ transportCost q)
    (htree : (transportSupportGraph p).IsTree) :
    ∀ q : NaturalTransport
      (augmentedRelation (fun a b => r a b ∧ b ∈ transportSplitColumns p))
      (scaledDemand (R := R) k (fun _ => 1)) (fun _ : R => k),
      transportCost (scaledCoreTransport r x hpos k hk p htree) ≤ transportCost q := by
  classical
  let root : Option L ⊕ R := Sum.inl none
  let α : Option L → ℤ := fun a => transportTreeVertexPotential p htree root (Sum.inl a)
  let β : R → ℤ := fun b => if b ∈ transportSplitColumns p then
    transportTreeVertexPotential p htree root (Sum.inr b) else
      (transportEdgeWeight (fun _ : R => k) (none : Option L) b : ℤ) + α none
  apply transport_potential_certificate_minimum _ α β
  · intro a b hab
    cases a with
    | none =>
      by_cases hb : b ∈ transportSplitColumns p
      · simp only [β, ite_eq_left hb, α]
        exact minimum_transport_tree_potential_dual p hp htree root none b trivial
      · simp only [β, ite_eq_right hb, le_refl]
    | some a =>
      have hb : b ∈ transportSplitColumns p := hab.2
      simp only [β, ite_eq_left hb, α]
      exact minimum_transport_tree_potential_dual p hp htree root (some a) b hab.1
  · intro a b hflow
    rw [scaledCoreTransport_flow] at hflow
    by_cases hb : b ∈ transportSplitColumns p
    · simp only [ite_eq_left hb] at hflow
      simp only [β, ite_eq_left hb, α]
      exact minimum_transport_tree_potential_tight p htree root a b hflow
    · simp only [ite_eq_right hb] at hflow
      cases a with
      | none => simp only [β, ite_eq_right hb]
      | some a => simp only [Option.elim_some] at hflow; omega

end ResearchMain.PreorderGamma
