import SumsetRanges.OrdinaryImages
import SumsetRanges.DenseRestricted

open Finset
open scoped Pointwise
namespace SumsetRanges

theorem nat_Icc_zero_add (a b : ℕ) : Icc 0 a+Icc 0 b=Icc 0 (a+b) := by
  ext x
  simp only [Finset.mem_add,mem_Icc,Nat.zero_le,true_and]
  constructor
  · rintro ⟨u,hu,v,hv,rfl⟩; omega
  · intro hx
    exact ⟨min x a,by omega,x-min x a,by omega,by omega⟩

theorem ordinarySums_nat_Icc (L q : ℕ) : ordinarySums (Icc 0 L) q=Icc 0 (q*L) := by
  induction q with
  | zero => simp [ordinarySums]
  | succ q ih => rw [ordinarySums,ih,nat_Icc_zero_add]; congr 1; ring

theorem ordinarySums_singleton {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (x : α) (q : ℕ) : ordinarySums {x} q={q • x} := by
  ext z
  rw [mem_ordinarySums]
  simp only [Finset.mem_singleton]
  constructor
  · rintro ⟨v,hv,rfl⟩; simp [hv]
  · rintro rfl
    exact ⟨fun _ => x,fun _ => rfl,by simp⟩

theorem ordinarySums_insert_succ {α : Type*} [AddCommMonoid α] [DecidableEq α]
    (A : Finset α) (x : α) (q : ℕ) :
    ordinarySums (insert x A) (q+1)=ordinarySums A (q+1) ∪
      (ordinarySums (insert x A) q).image (fun a => x+a) := by
  ext z
  constructor
  · intro hz
    have he : insert x A=A∪{x} := by ext y; simp
    rw [he,mem_ordinarySums_union] at hz
    obtain ⟨p,s,hps,a,ha,b,hb,rfl⟩ := hz
    rw [ordinarySums_singleton] at hb
    have hb' := Finset.mem_singleton.mp hb
    subst b
    cases s with
    | zero => simp only [zero_nsmul,add_zero]; exact Finset.mem_union_left _ (by simpa [show p=q+1 by omega] using ha)
    | succ s =>
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨a+s • x,?_,?_⟩
      · rw [show q=p+s by omega,ordinarySums_add]
        exact Finset.mem_add.mpr ⟨a,ordinarySums_mono (Finset.subset_insert _ _) p ha,
          s • x,ordinarySums_mono (by simp : ({x}:Finset α)⊆insert x A) s (by rw [ordinarySums_singleton]; simp),rfl⟩
      · simp [succ_nsmul,add_comm,add_left_comm]
  · intro hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact ordinarySums_mono (Finset.subset_insert _ _) (q+1) hz
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_add.mpr ⟨x,Finset.mem_insert_self _ _,a,ha,rfl⟩

theorem denseSet_interval (L x : ℕ) : denseSet (L+1) x=insert x (Icc 0 L) := by
  unfold denseSet
  congr 1
  ext y
  simp only [mem_range,mem_Icc,Nat.zero_le,true_and]
  omega

theorem dense_ordinary_intersection (L x q : ℕ) (hx : L≤x) :
    Icc 0 ((q+1)*L) ∩ (ordinarySums (denseSet (L+1) x) q).image (fun a => x+a)=
      Icc x ((q+1)*L) := by
  ext z
  simp only [Finset.mem_inter,Finset.mem_Icc,Finset.mem_image,Nat.zero_le,true_and]
  constructor
  · rintro ⟨hz,a,_,rfl⟩
    omega
  · rintro ⟨hxz,hz⟩
    refine ⟨hz,z-x,?_,by omega⟩
    have hzq : z-x≤q*L := by rw [Nat.add_mul,Nat.one_mul] at hz; omega
    apply ordinarySums_mono (show Icc 0 L⊆denseSet (L+1) x by rw [denseSet_interval]; exact Finset.subset_insert _ _) q
    rw [ordinarySums_nat_Icc]
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _,hzq⟩

theorem card_dense_ordinary_succ (L x q : ℕ) (hx : L≤x) :
    (ordinarySums (denseSet (L+1) x) (q+1)).card=
      (ordinarySums (denseSet (L+1) x) q).card+min x ((q+1)*L+1) := by
  have he : ordinarySums (denseSet (L+1) x) (q+1)=
      Icc 0 ((q+1)*L) ∪ (ordinarySums (denseSet (L+1) x) q).image (fun a => x+a) := by
    conv_lhs => rw [denseSet_interval,ordinarySums_insert_succ,ordinarySums_nat_Icc]
    rw [denseSet_interval]
  have hc := Finset.card_union_add_card_inter (Icc 0 ((q+1)*L))
    ((ordinarySums (denseSet (L+1) x) q).image (fun a => x+a))
  rw [dense_ordinary_intersection L x q hx,Finset.card_image_of_injective _
    (fun a b hab => Nat.add_left_cancel hab)] at hc
  simp only [Nat.card_Icc,Nat.sub_zero] at hc
  rw [he]
  omega

/-- Exact all-order count for the ordinary dense family. -/
theorem card_dense_ordinary (L x q : ℕ) (hx : L≤x) :
    (ordinarySums (denseSet (L+1) x) q).card=
      1+∑i∈range q,min x ((i+1)*L+1) := by
  induction q with
  | zero => simp [ordinarySums]
  | succ q ih => rw [card_dense_ordinary_succ L x q hx,ih,Finset.sum_range_succ,Nat.add_assoc]

end SumsetRanges
