import SumsetRanges.Kneser.MulStab
import SumsetRanges.OrdinaryLowerBound
import SumsetRanges.LevFiberGrowth
import Mathlib.Tactic.Linarith

open Finset
open scoped Pointwise Classical
namespace SumsetRanges

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem quotient_fiber_eq_vadd (H : AddSubgroup G) [DecidableEq (G ⧸ H)] (K S : Finset G)
    (hK : (K : Set G) = H) (hS : S + K = S) {a : G} (ha : a ∈ S) :
    S.filter (fun x => QuotientAddGroup.mk (s := H) x = QuotientAddGroup.mk a) = a +ᵥ K := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨_, he⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_vadd_finset.mpr ⟨x-a, ?_, by simp⟩
    change x-a ∈ (K : Set G)
    rw [hK]
    exact QuotientAddGroup.eq_iff_sub_mem.mp he
  · intro hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_vadd_finset.mp hx
    apply Finset.mem_filter.mpr
    constructor
    · rw [← hS]
      exact Finset.add_mem_add ha hk
    · have hkH : k ∈ H := by change k ∈ (K : Set G) at hk; rwa [hK] at hk
      change QuotientAddGroup.mk (s := H) (a+k) = QuotientAddGroup.mk a
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff k).mpr hkH, add_zero]

theorem card_quotient_fiber (H : AddSubgroup G) [DecidableEq (G ⧸ H)] (K S : Finset G)
    (hK : (K : Set G) = H) (hS : S + K = S) {q : G ⧸ H}
    (hq : q ∈ S.image (QuotientAddGroup.mk (s := H))) :
    (S.filter (fun x => QuotientAddGroup.mk (s := H) x = q)).card = K.card := by
  classical
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
  rw [quotient_fiber_eq_vadd H K S hK hS ha, Finset.card_vadd_finset]

theorem card_eq_card_quotient_mul (H : AddSubgroup G) [DecidableEq (G ⧸ H)] (K S : Finset G)
    (hK : (K : Set G) = H) (hS : S + K = S) :
    S.card = (S.image (QuotientAddGroup.mk (s := H))).card * K.card := by
  classical
  calc
    S.card = ∑ q ∈ S.image (QuotientAddGroup.mk (s := H)),
        (S.filter (fun x => QuotientAddGroup.mk (s := H) x = q)).card :=
      Finset.card_eq_sum_card_image _ _
    _ = ∑ _q ∈ S.image (QuotientAddGroup.mk (s := H)), K.card := by
      apply Finset.sum_congr rfl
      intro q hq
      exact card_quotient_fiber H K S hK hS hq
    _ = _ := by simp

/-- The number of missing points in one coset is at most the total number of holes. -/
theorem card_fiber_lower (H : AddSubgroup G) [DecidableEq (G ⧸ H)] (K S : Finset G)
    (hK : (K : Set G) = H) {a : G} (ha : a ∈ S) :
    S.card + K.card ≤ (S+K).card +
      (S.filter (fun x => QuotientAddGroup.mk (s := H) x = QuotientAddGroup.mk a)).card := by
  classical
  have hzero : (0:G) ∈ K := by change (0:G) ∈ (K:Set G); rw [hK]; exact H.zero_mem
  have hsub : S ∪ (a +ᵥ K) ⊆ S+K := by
    apply Finset.union_subset
    · exact Finset.subset_add_left S hzero
    · intro x hx
      obtain ⟨k,hk,rfl⟩ := Finset.mem_vadd_finset.mp hx
      exact Finset.add_mem_add ha hk
  have hinter : S ∩ (a +ᵥ K) =
      S.filter (fun x => QuotientAddGroup.mk (s := H) x = QuotientAddGroup.mk a) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter]
    constructor
    · rintro ⟨hx, hcos⟩
      obtain ⟨k, hk, rfl⟩ := Finset.mem_vadd_finset.mp hcos
      refine ⟨hx, ?_⟩
      apply QuotientAddGroup.eq_iff_sub_mem.mpr
      change a+k-a ∈ H
      have hkH : k ∈ H := by
        change k ∈ (K : Set G) at hk
        rwa [hK] at hk
      simpa only [add_sub_cancel_left] using hkH
    · rintro ⟨hx, he⟩
      refine ⟨hx, Finset.mem_vadd_finset.mpr ⟨x-a, ?_, by simp⟩⟩
      change x-a ∈ (K : Set G)
      rw [hK]
      exact QuotientAddGroup.eq_iff_sub_mem.mp he
  have hc := Finset.card_le_card hsub
  have he := Finset.card_union_add_card_inter S (a +ᵥ K)
  rw [Finset.card_vadd_finset, hinter] at he
  omega

/-- Cauchy-Davenport applied inside the fibers of a homomorphism. -/
theorem integer_sum_fiber_card_lower (A : Finset ℤ) (f : ℤ →+ G)
    (h : ℕ) (v : Fin h → ℤ) (hv : ∀ i, v i ∈ A) :
    (∑ i, (A.filter (fun a => f a = f (v i))).card) + 1 ≤
      ((ordinarySums A h).filter (fun x => f x = ∑ i, f (v i))).card + h := by
  induction h with
  | zero =>
    have hz : 0 ∈ (ordinarySums A 0).filter (fun x => f x = ∑ i : Fin 0, f (v i)) := by
      apply Finset.mem_filter.mpr
      exact ⟨by simp [ordinarySums], by simp⟩
    have hc := Finset.card_pos.mpr ⟨0, hz⟩
    have hn : (∑ i : Fin 0, (A.filter (fun a => f a = f (v i))).card) = 0 := by simp
    omega
  | succ h ih =>
    have hi := ih (fun i => v i.succ) (fun i => hv i.succ)
    let X := A.filter (fun a => f a = f (v 0))
    let Y := (ordinarySums A h).filter (fun x => f x = ∑ i : Fin h, f (v i.succ))
    have hX : X.Nonempty := ⟨v 0, Finset.mem_filter.mpr ⟨hv 0, rfl⟩⟩
    have hY : Y.Nonempty := by
      refine ⟨∑ i : Fin h, v i.succ, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact (mem_ordinarySums A h _).mpr ⟨fun i => v i.succ, fun i => hv i.succ, rfl⟩
      · exact map_sum f _ _
    have hs : X+Y ⊆ (ordinarySums A (h+1)).filter (fun x => f x = ∑ i, f (v i)) := by
      intro z hz
      obtain ⟨x,hx,y,hy,rfl⟩ := Finset.mem_add.mp hz
      obtain ⟨hxA,hxf⟩ := Finset.mem_filter.mp hx
      obtain ⟨hyA,hyf⟩ := Finset.mem_filter.mp hy
      refine Finset.mem_filter.mpr ⟨Finset.mem_add.mpr ⟨x,hxA,y,hyA,rfl⟩, ?_⟩
      rw [map_add, hxf, hyf, Fin.sum_univ_succ]
    have hc := integer_sumset_card_lower X Y hX hY
    have hd := Finset.card_le_card hs
    rw [Fin.sum_univ_succ]
    change X.card + (∑ i : Fin h, (A.filter (fun a => f a = f (v i.succ))).card) + 1 ≤ _
    change (∑ i : Fin h, (A.filter (fun a => f a = f (v i.succ))).card) + 1 ≤ Y.card+h at hi
    omega


theorem image_filter_comp_eq {α β γ : Type*} [DecidableEq α] [DecidableEq β]
    [DecidableEq γ] (S : Finset α) (f : α → β) (g : β → γ) (q : γ) :
    (S.filter (fun x => g (f x) = q)).image f =
      (S.image f).filter (fun y => g y = q) := by
  ext y
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨x, ⟨hx, hq⟩, rfl⟩
    exact ⟨⟨x,hx,rfl⟩, hq⟩
  · rintro ⟨⟨x,hx,rfl⟩,hq⟩
    exact ⟨x,⟨hx,hq⟩,rfl⟩

theorem card_fiber_growth_of_shift {Q : Type*} [DecidableEq Q]
    (f : ℤ →+ G) (g : G → Q) (d : ℤ) (hd : 0 < d) (hfd : f d = 0)
    (T U : Finset ℤ) (hTU : T ⊆ U) (hshift : ∀ x ∈ T, x+d ∈ U) (q : Q) :
    (T.filter (fun x => g (f x) = q)).card +
      ((U.image f).filter (fun y => g y = q)).card ≤
      (U.filter (fun x => g (f x) = q)).card := by
  rw [← image_filter_comp_eq]
  apply card_add_image_le_of_shift f d hd hfd
  · intro x hx
    obtain ⟨hx,hq⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hTU hx,hq⟩
  · intro x hx
    obtain ⟨hx,hq⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr ⟨hshift x hx, by simpa only [map_add,hfd,add_zero] using hq⟩

theorem sum_representative_nonzero_of_new_fiber (A : Finset ℤ) (f : ℤ →+ G)
    (n : ℕ) (v : Fin (n+1) → ℤ) (hv : ∀ i, v i ∈ A)
    (hq : (∑ i, f (v i)) ∉ (ordinarySums A n).image f) :
    ∀ i, f (v i) ≠ 0 := by
  intro i hi
  apply hq
  refine Finset.mem_image.mpr ⟨∑ j : Fin n, v (i.succAbove j), ?_, ?_⟩
  · exact (mem_ordinarySums A n _).mpr
      ⟨fun j => v (i.succAbove j), fun j => hv (i.succAbove j), rfl⟩
  · rw [map_sum, Fin.sum_univ_succAbove (fun j => f (v j)) i, hi, zero_add]


end SumsetRanges
