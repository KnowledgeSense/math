import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic

namespace ResearchMain.SIBO

open scoped BigOperators

variable {E : Type*} [DecidableEq E]

def indexInterval (n lo hi : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun i => lo ≤ i.val ∧ i.val < hi)

@[simp] theorem mem_indexInterval {n lo hi : ℕ} (i : Fin n) :
    i ∈ indexInterval n lo hi ↔ lo ≤ i.val ∧ i.val < hi := by
  simp [indexInterval]

structure BasisOrders (A B : Finset E) where
  n : ℕ
  a : Fin n → E
  b : Fin n → E
  a_injective : Function.Injective a
  b_injective : Function.Injective b
  a_range : Finset.univ.image a = A
  b_range : Finset.univ.image b = B

namespace BasisOrders

variable {A B : Finset E} (o : BasisOrders A B)

def exchange (lo hi : ℕ) : Finset E :=
  (B \ (indexInterval o.n lo hi).image o.b) ∪ (indexInterval o.n lo hi).image o.a

def Valid (M : Matroid E) : Prop :=
  ∀ lo hi, lo ≤ hi → hi ≤ o.n → M.IsBase (o.exchange lo hi : Set E)

theorem a_mem (i : Fin o.n) : o.a i ∈ A := by
  simpa only [o.a_range] using
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩ : o.a i ∈ Finset.univ.image o.a)

theorem b_mem (i : Fin o.n) : o.b i ∈ B := by
  simpa only [o.b_range] using
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩ : o.b i ∈ Finset.univ.image o.b)

theorem singleton_interval (i : Fin o.n) :
    indexInterval o.n i.val (i.val + 1) = {i} := by
  ext j
  simp only [mem_indexInterval, Finset.mem_singleton]
  constructor
  · intro h; apply Fin.ext; omega
  · rintro rfl; omega

/-- The singleton exchange forces every common element to occupy matching positions. -/
theorem common_aligned (M : Matroid E) (hB : M.IsBase (B : Set E))
    (hv : o.Valid M) (i : Fin o.n) (ha : o.a i ∈ B) : o.a i = o.b i := by
  by_contra hne
  have hb := o.b_mem i
  have hvalid := hv i.val (i.val + 1) (by omega) (by omega)
  have hswap : o.exchange i.val (i.val + 1) = B.erase (o.b i) := by
    rw [exchange, o.singleton_interval]
    simp only [Finset.image_singleton, Finset.sdiff_singleton_eq_erase]
    apply Finset.union_eq_left.mpr
    simpa using Finset.mem_erase.mpr ⟨hne, ha⟩
  rw [hswap] at hvalid
  exact hB.not_isBase_of_ssubset (by
    simp only [Finset.coe_erase]
    exact Set.ssubset_iff_subset_ne.mpr ⟨Set.sdiff_subset, by
      intro heq
      have : o.b i ∈ (B : Set E) \ {o.b i} := by rw [heq]; exact hb
      simp at this⟩) hvalid

theorem common_aligned_reverse (M : Matroid E) (hB : M.IsBase (B : Set E))
    (hv : o.Valid M) (i : Fin o.n) (hb : o.b i ∈ A) : o.a i = o.b i := by
  have hb' : o.b i ∈ Finset.univ.image o.a := by simpa only [o.a_range] using hb
  obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hb'
  have heq := o.common_aligned M hB hv j (hj ▸ o.b_mem i)
  have hji : j = i := o.b_injective (heq.symm.trans hj)
  simpa [hji] using heq

theorem closer_subset (M : Matroid E) (hB : M.IsBase (B : Set E))
    (hv : o.Valid M) (lo hi : ℕ) : A \ o.exchange lo hi ⊆ A \ B := by
  intro e he
  obtain ⟨heA, heX⟩ := Finset.mem_sdiff.mp he
  refine Finset.mem_sdiff.mpr ⟨heA, ?_⟩
  intro heB
  apply heX
  by_cases heI : e ∈ (indexInterval o.n lo hi).image o.b
  · obtain ⟨i, hiI, hie⟩ := Finset.mem_image.mp heI
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    exact ⟨i, hiI, (o.common_aligned_reverse M hB hv i (hie ▸ heA)).trans hie⟩
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨heB, heI⟩)

theorem exchange_closer (M : Matroid E) (hB : M.IsBase (B : Set E))
    (hv : o.Valid M) (lo hi : ℕ) (i : Fin o.n)
    (hiI : i ∈ indexInterval o.n lo hi) (hiB : o.a i ∉ B) :
    (A \ o.exchange lo hi).card < (A \ B).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨o.closer_subset M hB hv lo hi, ?_⟩
  intro heq
  have hmem : o.a i ∈ A \ B := Finset.mem_sdiff.mpr ⟨o.a_mem i, hiB⟩
  rw [← heq] at hmem
  have hnot := (Finset.mem_sdiff.mp hmem).2
  exact hnot (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hiI, rfl⟩))

theorem exchange_label {G : Type*} [AddCommGroup G]
    (M : Matroid E) (hB : M.IsBase (B : Set E)) (hv : o.Valid M)
    (ψ : E → G) (lo hi : ℕ) :
    (∑ e ∈ o.exchange lo hi, ψ e) =
      (∑ e ∈ B, ψ e) + ∑ i ∈ indexInterval o.n lo hi, (ψ (o.a i) - ψ (o.b i)) := by
  classical
  let I := indexInterval o.n lo hi
  have hbsub : I.image o.b ⊆ B := by
    intro e he
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact o.b_mem i
  have hd : Disjoint (B \ I.image o.b) (I.image o.a) := by
    apply Finset.disjoint_left.mpr
    intro e he he'
    obtain ⟨heB, heI⟩ := Finset.mem_sdiff.mp he
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp he'
    apply heI
    exact Finset.mem_image.mpr ⟨i, hiI, (o.common_aligned M hB hv i heB).symm⟩
  rw [exchange, Finset.sum_union hd, Finset.sum_sdiff_eq_sub hbsub]
  rw [Finset.sum_image (fun i _ j _ h => o.b_injective h),
    Finset.sum_image (fun i _ j _ h => o.a_injective h), Finset.sum_sub_distrib]
  abel

end BasisOrders

/-- Subsequence interchangeability uses intervals in suitable orderings of each pair of bases. -/
def IsSIBO (M : Matroid E) : Prop :=
  ∀ A B : Finset E, M.IsBase (A : Set E) → M.IsBase (B : Set E) →
    ∃ o : BasisOrders A B, o.Valid M

end ResearchMain.SIBO
