import MainTheorems.SIOrders

namespace ResearchMain.SIBO

open scoped BigOperators

theorem interval_as_prefix_difference {n lo hi : ℕ} (_h : lo ≤ hi) :
    indexInterval n lo hi = indexInterval n 0 hi \ indexInterval n 0 lo := by
  ext i
  simp only [Finset.mem_sdiff, mem_indexInterval]
  omega

theorem interval_sum {n lo hi : ℕ} {G : Type*} [AddCommGroup G]
    (d : Fin n → G) (h : lo ≤ hi) :
    (∑ i ∈ indexInterval n lo hi, d i) =
      (∑ i ∈ indexInterval n 0 hi, d i) - ∑ i ∈ indexInterval n 0 lo, d i := by
  rw [interval_as_prefix_difference h, Finset.sum_sdiff_eq_sub]
  intro i hi
  simp only [mem_indexInterval] at hi ⊢
  omega

namespace BasisOrders

variable {E : Type*} [DecidableEq E] {A B : Finset E} (o : BasisOrders A B)

def distinctIndices : Finset (Fin o.n) := Finset.univ.filter (fun i => o.a i ∉ B)

theorem distinct_image : o.distinctIndices.image o.a = A \ B := by
  ext e
  simp only [distinctIndices, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_sdiff]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact ⟨o.a_mem i, hi⟩
  · rintro ⟨heA, heB⟩
    have he : e ∈ Finset.univ.image o.a := by simpa only [o.a_range] using heA
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he
    exact ⟨i, heB, rfl⟩

theorem distinct_card : o.distinctIndices.card = (A \ B).card := by
  have h := Finset.card_image_of_injective o.distinctIndices o.a_injective
  rw [o.distinct_image] at h
  exact h.symm

noncomputable def distinctOrder : Fin (A \ B).card ↪o Fin o.n :=
  o.distinctIndices.orderEmbOfFin o.distinct_card

theorem distinctOrder_mem (i : Fin (A \ B).card) : o.a (o.distinctOrder i) ∉ B := by
  have h : o.distinctOrder i ∈ o.distinctIndices :=
    o.distinctIndices.orderEmbOfFin_mem o.distinct_card i
  exact (Finset.mem_filter.mp h).2

noncomputable def prefixBoundary (i : Fin ((A \ B).card + 1)) : ℕ :=
  if h : i.val = 0 then 0 else (o.distinctOrder ⟨i.val - 1, by omega⟩).val + 1

theorem prefixBoundary_le (i : Fin ((A \ B).card + 1)) : o.prefixBoundary i ≤ o.n := by
  simp only [prefixBoundary]
  split_ifs with h
  · omega
  · have := (o.distinctOrder ⟨i.val - 1, by omega⟩).isLt; omega

theorem prefixBoundary_strictMono : StrictMono o.prefixBoundary := by
  intro i j hij
  have hv : i.val < j.val := hij
  simp only [prefixBoundary]
  split_ifs with hi hj
  · omega
  · omega
  · omega
  · have hlt : (⟨i.val - 1, by omega⟩ : Fin (A \ B).card) < ⟨j.val - 1, by omega⟩ := by
      change i.val - 1 < j.val - 1
      omega
    have := o.distinctOrder.strictMono hlt
    exact Nat.add_lt_add_right this 1

theorem interval_contains_distinct {i j : Fin ((A \ B).card + 1)} (hij : i < j) :
    ∃ t ∈ indexInterval o.n (o.prefixBoundary i) (o.prefixBoundary j), o.a t ∉ B := by
  have hj : j.val ≠ 0 := by have : i.val < j.val := hij; omega
  let t := o.distinctOrder ⟨j.val - 1, by omega⟩
  refine ⟨t, ?_, o.distinctOrder_mem _⟩
  rw [mem_indexInterval]
  have hb := o.prefixBoundary_strictMono hij
  have heq : o.prefixBoundary j = t.val + 1 := by simp [prefixBoundary, hj, t]
  omega

end BasisOrders

end ResearchMain.SIBO
