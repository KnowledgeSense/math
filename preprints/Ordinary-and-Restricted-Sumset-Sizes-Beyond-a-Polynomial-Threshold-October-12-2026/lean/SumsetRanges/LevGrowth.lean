import SumsetRanges.LevKneser
import SumsetRanges.LevOuterFiber
import SumsetRanges.LevQuotientGrowth
import SumsetRanges.LevResidues

open Finset
open scoped Pointwise Classical
namespace SumsetRanges

set_option maxHeartbeats 400000

/-- Lev's growth mechanism in a finite quotient of the integers.  A single new
    stabilizer coset retains the extra integer points needed by Kneser's bound. -/
theorem lev_growth_in_finite_quotient {G : Type*} [AddCommGroup G] [DecidableEq G]
    [Fintype G] (A : Finset ℤ) (f : ℤ →+ G) (d : ℤ)
    (hd : 0 < d) (hfd : f d = 0) (hinj : Set.InjOn f (A.erase d))
    (hzero : 0 ∈ A) (hend : d ∈ A)
    (hgen : AddSubgroup.closure (A.image f : Set G) = ⊤) (n : ℕ) :
    (ordinarySums A n).card + min (Fintype.card G) ((n+1)*((A.image f).card-1)+1) ≤
      (ordinarySums A (n+1)).card := by
  let S := A.image f
  let P := ordinarySums A n
  let U := ordinarySums A (n+1)
  let T := ordinarySums S (n+1)
  have hS0 : 0 ∈ S := Finset.mem_image.mpr ⟨0,hzero,map_zero f⟩
  have hS : S.Nonempty := ⟨0,hS0⟩
  have hT : T.Nonempty := ordinarySums_nonempty_generic S hS _
  have hTu : T = U.image f := ordinarySums_image A f (n+1)
  have hPU : P ⊆ U := by
    intro x hx
    exact Finset.mem_add.mpr ⟨0,hzero,x,hx,zero_add x⟩
  have hshift : ∀ x ∈ P, x+d ∈ U := by
    intro x hx
    exact Finset.mem_add.mpr ⟨d,hend,x,hx,add_comm _ _⟩
  by_cases hfull : T = Finset.univ
  · have hg := ordinarySums_growth_ge_image A f d hd hfd hzero hend n
    change P.card + T.card ≤ U.card at hg
    rw [hfull,Finset.card_univ] at hg
    exact (Nat.add_le_add_left (min_le_left _ _) P.card).trans hg
  · let K := T.addStab
    let H := AddAction.stabilizer G T
    let : DecidableEq (G ⧸ H) := Classical.decEq _
    let π : G →+ G ⧸ H := QuotientAddGroup.mk' H
    let g : ℤ →+ G ⧸ H := π.comp f
    have hK : (K : Set G) = H := Finset.coe_addStab hT
    have hss := ordinarySums_stabilizer_image_ssubset S n hS0 hgen hfull
    change (ordinarySums S n).image π ⊂ T.image π at hss
    obtain ⟨q,hq,hnew⟩ := (Finset.ssubset_iff_of_subset hss.subset).mp hss
    have hUi : U.image g = T.image π := by
      calc
        U.image g = (U.image f).image π := by rw [Finset.image_image]; rfl
        _ = T.image π := congrArg (Finset.image π) hTu.symm
    have hPi : P.image g = (ordinarySums S n).image π := by
      rw [ordinarySums_image A f n,Finset.image_image]
      rfl
    have hqU : q ∈ U.image g := by rwa [hUi]
    have hqP : q ∉ P.image g := by rwa [hPi]
    let V := U.filter (fun x => g x = q)
    have hVU : V ⊆ U := Finset.filter_subset _ _
    have hPV : Disjoint P V := by
      apply Finset.disjoint_left.mpr
      intro x hx hxV
      exact hqP (Finset.mem_image.mpr ⟨x,hx,(Finset.mem_filter.mp hxV).2⟩)
    have havoid : ∀ x ∈ P, x+d ∉ V := by
      intro x hx hxV
      have hqxd := (Finset.mem_filter.mp hxV).2
      have hgd : g d = 0 := by simp [g,hfd]
      rw [map_add,hgd,add_zero] at hqxd
      exact hqP (Finset.mem_image.mpr ⟨x,hx,hqxd⟩)
    have hVimage : V.image f = T.filter (fun x => π x = q) := by
      calc
        V.image f = (U.image f).filter (fun x => π x = q) := image_filter_comp_eq U f π q
        _ = T.filter (fun x => π x = q) :=
          congrArg (fun Z : Finset G => Z.filter (fun x => π x = q)) hTu.symm
    have hVc : (V.image f).card = K.card := by
      rw [hVimage]
      exact card_quotient_fiber H K T hK (Finset.add_addStab T) hq
    have hshiftcard := card_add_image_add_fiber_le_of_shift f d hd hfd P U V
      hPU hVU hPV hshift havoid
    rw [← hTu,hVc] at hshiftcard
    have houter := ordinarySums_outer_fiber_lower A f d hfd hinj H K hK n q hqU hqP
    change (n+1)*S.card+(n+1)*K.card+1 ≤ V.card+(n+1)*(S+K).card+(n+1) at houter
    have hkneser := ordinarySums_card_kneser S hS (n+1) (Nat.succ_pos n)
    change (n+1)*(S+K).card ≤ T.card+(n+1-1)*K.card at hkneser
    rw [Nat.add_sub_cancel] at hkneser
    have hspos : 1 ≤ S.card := Finset.card_pos.mpr hS
    have hsminus : S.card-1+1 = S.card := Nat.sub_add_cancel hspos
    have hgrowth : P.card+((n+1)*(S.card-1)+1) ≤ U.card := by
      nlinarith only [hshiftcard,houter,hkneser,hsminus]
    exact (Nat.add_le_add_left (min_le_right _ _) P.card).trans hgrowth

/-- Lev's full integer sumset growth theorem for a normalized set. -/
theorem lev_growth (B : Finset ℤ) (d j : ℕ) (hcard : 2 ≤ B.card)
    (hzero : 0 ∈ B) (hend : (d : ℤ) ∈ B)
    (hbound : ∀ b ∈ B, 0 ≤ b ∧ b ≤ d) (hgcd : B.gcd id = 1)
    (hj : 2 ≤ j) :
    (ordinarySums B (j-1)).card + min d (j*(B.card-2)+1) ≤
      (ordinarySums B j).card := by
  have hd := normalized_diameter_pos B d hcard hbound
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have he := lev_growth_in_finite_quotient B (Int.castAddHom (ZMod d)) (d:ℤ)
    (by exact_mod_cast hd) (by simp) (normalized_cast_injOn_erase B d hbound)
    hzero hend (normalized_cast_closure B d hgcd) (j-1)
  rw [ZMod.card, normalized_cast_card B d hcard hzero hend hbound,
    Nat.sub_sub, Nat.sub_add_cancel (by omega : 1 ≤ j)] at he
  exact he

end SumsetRanges
