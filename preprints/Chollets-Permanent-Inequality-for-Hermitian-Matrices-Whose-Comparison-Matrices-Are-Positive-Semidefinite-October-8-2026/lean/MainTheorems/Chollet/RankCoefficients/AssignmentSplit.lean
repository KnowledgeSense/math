import MainTheorems.Chollet.Basic
import Mathlib.Data.Fintype.Powerset

noncomputable section

namespace ResearchMain.Chollet.RankCoefficients

variable {I J K : Type*} [Fintype I] [instI : DecidableEq I]

def edgePositions (f : I → J ⊕ K) : Finset I := by
  classical
  let : DecidableEq I := instI
  exact Finset.univ.filter (fun i => ∃ j, f i = Sum.inl j)

abbrev SplitAssignment (I J K : Type*) :=
  Σ s : Finset I, (s → J) × ({i : I // i ∉ s} → K)

def assembleAssignment (q : SplitAssignment I J K) : I → J ⊕ K :=
  fun i => if hi : i ∈ q.1 then Sum.inl (q.2.1 ⟨i, hi⟩) else Sum.inr (q.2.2 ⟨i, hi⟩)

theorem edgePositions_assemble (q : SplitAssignment I J K) :
    edgePositions (assembleAssignment q) = q.1 := by
  classical
  let : DecidableEq I := instI
  ext i
  change (i ∈ Finset.univ.filter (fun i => ∃ j, assembleAssignment q i = Sum.inl j)) ↔ i ∈ q.1
  constructor
  · intro hi
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hi).2
    by_contra hn
    simp only [assembleAssignment, dite_eq_right hn] at hj
    cases hj
  · intro hi
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, q.2.1 ⟨i, hi⟩, ?_⟩
    simp only [assembleAssignment, dite_eq_left hi]

theorem assembleAssignment_injective :
    Function.Injective (assembleAssignment (I := I) (J := J) (K := K)) := by
  classical
  let : DecidableEq I := instI
  rintro ⟨s, l, r⟩ ⟨t, l', r'⟩ h
  have hs := congrArg edgePositions h
  rw [edgePositions_assemble, edgePositions_assemble] at hs
  change s = t at hs
  subst t
  have hl : l = l' := by
    funext i
    have hi := congrFun h i
    simpa only [assembleAssignment, dite_eq_left i.property, Sum.inl.injEq] using hi
  have hr : r = r' := by
    funext i
    have hi := congrFun h i
    simpa only [assembleAssignment, dite_eq_right i.property, Sum.inr.injEq] using hi
  cases hl
  cases hr
  rfl

theorem assembleAssignment_surjective :
    Function.Surjective (assembleAssignment (I := I) (J := J) (K := K)) := by
  classical
  let : DecidableEq I := instI
  intro f
  let s := edgePositions f
  have hl : ∀ i : s, ∃ j : J, f i = Sum.inl j := by
    intro i
    exact (Finset.mem_filter.mp i.property).2
  have hr : ∀ i : {i : I // i ∉ s}, ∃ k : K, f i = Sum.inr k := by
    intro i
    cases hf : f i with
    | inl j =>
      have his : (i : I) ∈ s := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨j, hf⟩⟩
      exact False.elim (i.property his)
    | inr k => exact ⟨k, rfl⟩
  let l : s → J := fun i => Classical.choose (hl i)
  let r : {i : I // i ∉ s} → K := fun i => Classical.choose (hr i)
  refine ⟨⟨s, l, r⟩, ?_⟩
  funext i
  change (if hi : i ∈ s then Sum.inl (l ⟨i, hi⟩) else Sum.inr (r ⟨i, hi⟩)) = f i
  split_ifs with hi
  · exact (Classical.choose_spec (hl ⟨i, hi⟩)).symm
  · exact (Classical.choose_spec (hr ⟨i, hi⟩)).symm

def assignmentEquiv : SplitAssignment I J K ≃ (I → J ⊕ K) :=
  Equiv.ofBijective assembleAssignment ⟨assembleAssignment_injective, assembleAssignment_surjective⟩

theorem sum_assignments_split [Fintype J] [Fintype K] {R : Type*} [AddCommMonoid R]
    (F : (I → J ⊕ K) → R) :
    (∑ f : I → J ⊕ K, F f) =
      ∑ s : Finset I, ∑ l : s → J, ∑ r : {i : I // i ∉ s} → K,
        F (assembleAssignment ⟨s, l, r⟩) := by
  classical
  let : DecidableEq I := instI
  have h := Fintype.sum_equiv (assignmentEquiv (I := I) (J := J) (K := K))
    (fun q => F (assembleAssignment q)) F (fun _ => rfl)
  rw [Fintype.sum_sigma] at h
  simpa only [Fintype.sum_prod_type] using h.symm

end ResearchMain.Chollet.RankCoefficients

