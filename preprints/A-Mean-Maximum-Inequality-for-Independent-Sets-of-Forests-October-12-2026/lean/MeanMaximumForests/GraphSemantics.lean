import MeanMaximumForests.GraphUnion
import Mathlib.Tactic.Linarith

namespace MeanMaximumForests
open Finset
variable {V : Type*} [DecidableEq V] (G : SimpleGraph V)

/-- A rooted forest expression realized by vertices and edges of a simple graph.
The constructors assert only vertex disjointness and adjacency, not any counting inequality. -/
inductive ForestRealization : Finset V → Finset V → ForestExpr → Prop
  | empty : ForestRealization ∅ ∅ .empty
  | union {a b ra rb A B} : Disjoint a b → Separated G a b →
      ForestRealization a ra A → ForestRealization b rb B →
      ForestRealization (a ∪ b) (ra ∪ rb) (.union A B)
  | root {s rs A} (r : V) : r ∉ s →
      (∀ v ∈ s, G.Adj r v ↔ v ∈ rs) → ForestRealization s rs A →
      ForestRealization (insert r s) {r} (.root A)

theorem ForestRealization.roots_subset {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) : rs ⊆ s := by
  induction h with
  | empty => exact Subset.rfl
  | union _ _ _ _ ha hb => exact union_subset_union ha hb
  | root r _ _ _ _ => exact singleton_subset_iff.mpr (mem_insert_self _ _)

omit [DecidableEq V] in
theorem independenceNumber_mono {s t : Finset V} (h : s ⊆ t) :
    independenceNumber G s ≤ independenceNumber G t := by
  obtain ⟨u, hu, hi, he⟩ := exists_maximum_independentSet G s
  rw [← he]
  exact independent_card_le G t (Subset.trans hu h) hi

theorem roots_deleted_union {a b ra rb : Finset V} (hd : Disjoint a b)
    (ha : ra ⊆ a) (hb : rb ⊆ b) :
    (a ∪ b) \ (ra ∪ rb) = (a \ ra) ∪ (b \ rb) := by
  ext v
  simp only [mem_sdiff, mem_union, not_or]
  constructor
  · rintro ⟨hav | hbv, hnr, hns⟩
    · exact Or.inl ⟨hav, hnr⟩
    · exact Or.inr ⟨hbv, hns⟩
  · rintro (⟨hav, hnr⟩ | ⟨hbv, hns⟩)
    · exact ⟨Or.inl hav, hnr, fun h => disjoint_left.mp hd hav (hb h)⟩
    · exact ⟨Or.inr hbv, fun h => disjoint_left.mp hd (ha h) hbv, hns⟩

omit [DecidableEq V] in
theorem Separated.mono {a b s t : Finset V} (h : Separated G a b)
    (hs : s ⊆ a) (ht : t ⊆ b) : Separated G s t := fun u hu v hv => h u (hs hu) v (ht hv)

theorem compatibleVertices_root {s rs : Finset V} {r : V} (hr : r ∉ s)
    (he : ∀ v ∈ s, G.Adj r v ↔ v ∈ rs) :
    compatibleVertices G (insert r s) r = s \ rs := by
  ext v
  simp only [mem_compatibleVertices, mem_insert, mem_sdiff]
  constructor
  · rintro ⟨hne, hvr | hv, hna⟩
    · exact False.elim (hne hvr)
    · exact ⟨hv, fun h => hna ((he v hv).mpr h)⟩
  · rintro ⟨hv, hnr⟩
    exact ⟨fun h => hr (h ▸ hv), Or.inr hv, fun h => hnr ((he v hv).mp h)⟩

/-- Direct counting vector: every entry comes from independent vertex sets. -/
noncomputable def graphVector (c : ℝ) (s rs : Finset V) : ConeVector :=
  ⟨independentSetCount G s, independentSetCount G (s \ rs),
    independentSetSizeSum G s - c * independenceNumber G s * independentSetCount G s,
    independentSetSizeSum G (s \ rs) - c * independenceNumber G s * independentSetCount G (s \ rs)⟩

theorem graphVector_union (c : ℝ) {a b ra rb : Finset V}
    (hd : Disjoint a b) (he : Separated G a b) (ha : ra ⊆ a) (hb : rb ⊆ b) :
    graphVector G c (a ∪ b) (ra ∪ rb) = product (graphVector G c a ra) (graphVector G c b rb) := by
  have hd' : Disjoint (a \ ra) (b \ rb) := hd.mono sdiff_subset sdiff_subset
  have he' := he.mono G (sdiff_subset (s := a) (t := ra)) (sdiff_subset (s := b) (t := rb))
  unfold graphVector product
  rw [roots_deleted_union hd ha hb, independentSetCount_union G hd he,
    independentSetCount_union G hd' he', independentSetSizeSum_union G hd he,
    independentSetSizeSum_union G hd' he', independenceNumber_union G hd he]
  ext <;> simp only [Nat.cast_add, Nat.cast_mul] <;> ring

theorem ForestRealization.flag_semantics {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) :
    if flag A then independenceNumber G (s \ rs) < independenceNumber G s
    else independenceNumber G (s \ rs) = independenceNumber G s := by
  induction h with
  | empty => simp [flag]
  | @union a b ra rb A B hd he hA hB ihA ihB =>
    have hd' : Disjoint (a \ ra) (b \ rb) := hd.mono sdiff_subset sdiff_subset
    have he' := he.mono G (sdiff_subset (s := a) (t := ra)) (sdiff_subset (s := b) (t := rb))
    rw [roots_deleted_union hd (hA.roots_subset G) (hB.roots_subset G),
      independenceNumber_union G hd he, independenceNumber_union G hd' he']
    simp only [flag]
    by_cases hfA : flag A = true <;> by_cases hfB : flag B = true <;> simp_all
    all_goals omega
  | @root s rs A r hr he hA ih =>
    have hd : insert r s \ {r} = s := by rw [sdiff_singleton_eq_erase, erase_insert hr]
    have hrec := independenceNumber_recursion G (insert r s) r (mem_insert_self _ _)
    rw [erase_insert hr, compatibleVertices_root G hr he] at hrec
    rw [hd, hrec]
    simp only [flag]
    by_cases hf : flag A = true <;> simp_all
    all_goals omega

theorem ForestRealization.root_independenceNumber {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) {r : V} (hr : r ∉ s)
    (he : ∀ v ∈ s, G.Adj r v ↔ v ∈ rs) :
    independenceNumber G (insert r s) = independenceNumber G s + (if flag A then 0 else 1) := by
  have hf := h.flag_semantics G
  have hrec := independenceNumber_recursion G (insert r s) r (mem_insert_self _ _)
  rw [erase_insert hr, compatibleVertices_root G hr he] at hrec
  by_cases hh : flag A = true <;> simp_all
  all_goals omega

theorem graphVector_root (c : ℝ) {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) {r : V} (hr : r ∉ s)
    (he : ∀ v ∈ s, G.Adj r v ↔ v ∈ rs) :
    graphVector G c (insert r s) {r} = plant c (flag A) (graphVector G c s rs) := by
  have hd : insert r s \ {r} = s := by rw [sdiff_singleton_eq_erase, erase_insert hr]
  have hc := independentSetCount_recursion G (insert r s) r (mem_insert_self _ _)
  have hs := independentSetSizeSum_recursion G (insert r s) r (mem_insert_self _ _)
  rw [erase_insert hr, compatibleVertices_root G hr he] at hc hs
  unfold graphVector plant
  rw [hd, hc, hs, h.root_independenceNumber G hr he]
  cases hh : flag A <;> ext <;>
    simp only [Bool.false_eq_true, ↓reduceIte, Nat.cast_add, Nat.cast_zero, Nat.cast_one] <;> ring

/-- Exact semantic bridge from graph-independent-set counting to cone recursion. -/
theorem ForestRealization.vector_eq (c : ℝ) {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) : graphVector G c s rs = vector c A := by
  induction h with
  | empty => simp [graphVector, vector, unitVector]
  | union hd he hA hB ihA ihB =>
    rw [graphVector_union G c hd he (hA.roots_subset G) (hB.roots_subset G), ihA, ihB]
    rfl
  | root r hr he hA ih =>
    rw [graphVector_root G c hA hr he, ih]
    rfl

/-- The graph-theoretic consequence of the invariant-cone criterion. -/
theorem ForestRealization.mean_bound {c : ℝ} {C : Bool → Set ConeVector}
    (hc : InvariantConditions c C) {s rs : Finset V} {A : ForestExpr}
    (h : ForestRealization G s rs A) :
    c * independenceNumber G s ≤ meanIndependentSetSize G s := by
  induction h with
  | empty => simp [meanIndependentSetSize]
  | union hd he hA hB ihA ihB =>
    rw [independenceNumber_union G hd he, meanIndependentSetSize_union G hd he]
    push_cast
    nlinarith
  | @root s rs A r hr he hA ih =>
    have hv := (ForestRealization.root r hr he hA).vector_eq G c
    have hx := root_nonnegative hc A
    rw [← hv] at hx
    have hp : (0 : ℝ) < independentSetCount G (insert r s) :=
      Nat.cast_pos.mpr (independentSetCount_pos G _)
    exact (centered_nonnegative_iff c _ _ _ hp).mp hx

end MeanMaximumForests
