import BuchweitzProfiles.Counting
import BuchweitzProfiles.CountDifferences
import Mathlib.Data.Finset.Card

open scoped Pointwise

namespace BuchweitzProfiles

/-- Below the cutoff, every sum has either no large summand or exactly one.
This is an equality of actual sumsets, with no representation hypothesis. -/
theorem truncated_union_large (U V : Finset Nat) (m n : Nat) (hn : 1 ≤ n)
    (hlarge : ∀ v ∈ V, ∀ w ∈ V, m ≤ v + w) :
    (sumset (U ∪ V) n).filter (· < m) =
      (sumset U n ∪ (V + sumset U (n - 1))).filter (· < m) := by
  induction n, hn using Nat.le_induction with
  | base =>
    ext x
    simp [sumset_zero, Finset.mem_add]
  | succ n hn ih =>
    ext x
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hx, hxm⟩
      obtain ⟨a, ha, b, hb, he⟩ := mem_sumset_succ.mp hx
      have ha' : a ∈ (sumset (U ∪ V) n).filter (· < m) :=
        Finset.mem_filter.mpr ⟨ha, by omega⟩
      rw [ih] at ha'
      obtain ⟨ha', _⟩ := Finset.mem_filter.mp ha'
      refine ⟨?_, hxm⟩
      simp only [Nat.add_sub_cancel, Finset.mem_union] at *
      rcases ha' with ha' | ha' <;> rcases hb with hb | hb
      · exact Or.inl (mem_sumset_succ.mpr ⟨a, ha', b, hb, he⟩)
      · exact Or.inr (Finset.mem_add.mpr ⟨b, hb, a, ha', by omega⟩)
      · obtain ⟨v, hv, u, hu, heu⟩ := Finset.mem_add.mp ha'
        right
        apply Finset.mem_add.mpr
        refine ⟨v, hv, u + b, ?_, by omega⟩
        have hn' : n - 1 + 1 = n := by omega
        rw [← hn']
        exact mem_sumset_succ.mpr ⟨u, hu, b, hb, rfl⟩
      · obtain ⟨v, hv, u, _, heu⟩ := Finset.mem_add.mp ha'
        have hh := hlarge v hv b hb
        omega
    · rintro ⟨hx, hxm⟩
      refine ⟨?_, hxm⟩
      simp only [Finset.mem_union, Nat.add_sub_cancel] at hx
      rcases hx with hx | hx
      · exact sumset_mono Finset.subset_union_left (n + 1) hx
      · obtain ⟨v, hv, u, hu, heu⟩ := Finset.mem_add.mp hx
        exact mem_sumset_succ.mpr ⟨u, sumset_mono Finset.subset_union_left n hu,
          v, Finset.mem_union_right _ hv, by omega⟩

/-- Every small sum stays in the zero residue class. -/
theorem small_sum_divisible (K M n : Nat) {x : Nat}
    (hx : x ∈ sumset (insert 0 (smallGenerators ((2*K+1)*M) M)) n) : M ∣ x := by
  rw [sumset_insert_zero] at hx
  obtain ⟨l, _, hx⟩ := Finset.mem_biUnion.mp hx
  rw [sumset_smallGenerators] at hx
  obtain ⟨b, _, rfl⟩ := mem_row.mp hx
  exact ⟨l * (2*K+1) + b, by ring⟩

/-- The admitted sums containing a specified large generator. -/
def largeContribution (U : Finset Nat) (v m n : Nat) : Finset Nat :=
  ((sumset U (n - 1)).image (v + ·)).filter (· < m)

lemma mem_largeContribution {U : Finset Nat} {v m n x : Nat} :
    x ∈ largeContribution U v m n ↔
      (∃ y ∈ sumset U (n - 1), v + y = x) ∧ x < m := by
  simp [largeContribution]

/-- The filtered sumset is the disjoint union that will be counted. -/
theorem truncated_indexed_union {ι : Type*} (J : Finset ι) (v : ι → Nat)
    (U : Finset Nat) (m n : Nat) (hn : 1 ≤ n)
    (hlarge : ∀ i ∈ J, ∀ j ∈ J, m ≤ v i + v j) :
    (sumset (U ∪ J.image v) n).filter (· < m) =
      (sumset U n).filter (· < m) ∪ J.biUnion (fun j => largeContribution U (v j) m n) := by
  rw [truncated_union_large U (J.image v) m n hn]
  · ext x
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_add, Finset.mem_image,
      Finset.mem_biUnion, mem_largeContribution]
    constructor
    · rintro ⟨hx, hxm⟩
      rcases hx with hx | ⟨w, ⟨j, hj, rfl⟩, y, hy, he⟩
      · exact Or.inl ⟨hx, hxm⟩
      · exact Or.inr ⟨j, hj, ⟨y, hy, he⟩, hxm⟩
    · rintro (⟨hx, hxm⟩ | ⟨j, hj, ⟨y, hy, he⟩, hxm⟩)
      · exact ⟨Or.inl hx, hxm⟩
      · exact ⟨Or.inr ⟨v j, ⟨j, hj, rfl⟩, y, hy, he⟩, hxm⟩
  · intro a ha b hb
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    exact hlarge i hi j hj

/-- Cardinality of the actual truncated sumset, using distinct nonzero residues. -/
theorem truncatedCount_indexed_union {ι : Type*} (J : Finset ι) (v : ι → Nat)
    (U : Finset Nat) (m M n : Nat) (hn : 1 ≤ n)
    (hlarge : ∀ i ∈ J, ∀ j ∈ J, m ≤ v i + v j)
    (hdiv : ∀ k x, x ∈ sumset U k → M ∣ x)
    (hres0 : ∀ j ∈ J, v j % M ≠ 0)
    (hresinj : ∀ i ∈ J, ∀ j ∈ J, v i % M = v j % M → i = j) :
    truncatedCount (U ∪ J.image v) m n = truncatedCount U m n +
      ∑ j ∈ J, (largeContribution U (v j) m n).card := by
  have hres (j : ι) (x : Nat) (hx : x ∈ largeContribution U (v j) m n) :
      x % M = v j % M := by
    obtain ⟨⟨y, hy, rfl⟩, _⟩ := mem_largeContribution.mp hx
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (hdiv _ _ hy), Nat.add_zero, Nat.mod_mod]
  unfold truncatedCount
  rw [truncated_indexed_union J v U m n hn hlarge, Finset.card_union_of_disjoint]
  · congr 1
    apply Finset.card_biUnion
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact hij (hresinj i hi j hj ((hres i x hx).symm.trans (hres j x hy)))
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨j, hj, hy⟩ := Finset.mem_biUnion.mp hy
    have hz := Nat.mod_eq_zero_of_dvd (hdiv _ _ (Finset.mem_filter.mp hx).1)
    exact hres0 j hj ((hres j x hy).symm.trans hz)

/-- Translation converts the actual large-generator contribution into the
admitted arithmetic rows counted in Proposition 4.3. -/
theorem largeContribution_card (K M d t j v m n : Nat)
    (hK : d ≤ K) (hM : 0 < M) (hd : 2 ≤ d) (ht : t ≤ 2*d-2)
    (hj0 : 0 < j) (hj : j < M) (hn : 1 ≤ n)
    (hv : (v : Int) + digitRho K M d t j = (m : Int) - 1) :
    ((largeContribution (insert 0 (smallGenerators ((2*K+1)*M) M)) v m n).card : Int) =
      largeRowCount d t n := by
  let U := insert 0 (smallGenerators ((2*K+1)*M) M)
  have hrows : sumset U (n - 1) = (Finset.range n).biUnion (row ((2*K+1)*M) M) := by
    dsimp [U]
    rw [sumset_insert_zero]
    simp_rw [sumset_smallGenerators]
    have he : n - 1 + 1 = n := by omega
    rw [he]
  have he : largeContribution U v m n =
      ((((Finset.range n).biUnion (row ((2*K+1)*M) M)).filter
        (fun x : Nat => (x : Int) ≤ digitRho K M d t j)).image (v + ·)) := by
    ext x
    rw [mem_largeContribution, hrows]
    simp only [Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨⟨y, hy, hxy⟩, hxm⟩
      exact ⟨y, ⟨hy, by omega⟩, hxy⟩
    · rintro ⟨y, ⟨hy, hycut⟩, hxy⟩
      exact ⟨⟨y, hy, hxy⟩, by omega⟩
  change ((largeContribution U v m n).card : Int) = _
  rw [he, Finset.card_image_of_injective _ (by intro a b he; dsimp at he; omega)]
  rw [card_admitted_rows K M d t j n hK hM hd ht hj0 hj]
  unfold largeRowCount
  have hemin : min n (d - 1) = min (n - 1) (d - 2) + 1 := by omega
  rw [hemin]
  by_cases hdn : d ≤ n <;> simp [hdn]

lemma indexed_union_card {ι : Type*} (J : Finset ι) (v : ι → Nat)
    (U : Finset Nat) (M : Nat) (hdiv : ∀ x ∈ U, M ∣ x)
    (hres0 : ∀ j ∈ J, v j % M ≠ 0)
    (hresinj : ∀ i ∈ J, ∀ j ∈ J, v i % M = v j % M → i = j) :
    (U ∪ J.image v).card = U.card + J.card := by
  rw [Finset.card_union_of_disjoint]
  · congr 1
    apply Finset.card_image_of_injOn
    intro i hi j hj he
    exact hresinj i hi j hj (congrArg (· % M) he)
  · apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
    exact hres0 j hj (Nat.mod_eq_zero_of_dvd (hdiv _ hx))

lemma smallGenerators_zero_not_mem (u M : Nat) (hu : 0 < u) :
    0 ∉ smallGenerators u M := by
  intro hx
  obtain ⟨b, _, hb⟩ := mem_row.mp hx
  omega

lemma padded_small_card (K M : Nat) (hM : 0 < M) :
    (insert 0 (smallGenerators ((2*K+1)*M) M)).card = 4 := by
  rw [Finset.card_insert_of_notMem (smallGenerators_zero_not_mem _ _ (by positivity))]
  change (row ((2*K+1)*M) M 1).card + 1 = 4
  rw [card_row _ _ _ hM]

end BuchweitzProfiles
