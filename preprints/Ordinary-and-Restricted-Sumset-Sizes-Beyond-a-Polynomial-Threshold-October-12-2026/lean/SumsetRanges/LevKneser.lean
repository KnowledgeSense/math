import SumsetRanges.Kneser.Kneser
import SumsetRanges.OrdinaryImages
import SumsetRanges.OrdinarySetOperations
import Mathlib.Tactic.Linarith

open Finset
open scoped Pointwise
namespace SumsetRanges

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem ordinarySums_nonempty_generic (S : Finset G) (hS : S.Nonempty) (h : ℕ) :
    (ordinarySums S h).Nonempty := by
  obtain ⟨a, ha⟩ := hS
  exact ⟨∑ _i : Fin h, a, (mem_ordinarySums S h _).mpr ⟨fun _ => a, fun _ => ha, rfl⟩⟩

theorem addStab_ordinarySums_mono (S : Finset G) (hS : S.Nonempty)
    {p q : ℕ} (hpq : p ≤ q) :
    (ordinarySums S p).addStab ⊆ (ordinarySums S q).addStab := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hpq
  rw [ordinarySums_add]
  exact Finset.subset_addStab_add_left (ordinarySums_nonempty_generic S hS r)

theorem ordinarySums_card_aperiodic (S : Finset G) (hS : S.Nonempty) (h : ℕ)
    (hh : 1 ≤ h) (hstab : (ordinarySums S h).addStab = 0) :
    h * S.card ≤ (ordinarySums S h).card + (h - 1) := by
  induction h, hh using Nat.le_induction with
  | base => simp [ordinarySums]
  | succ h hh ih =>
    have hst : (ordinarySums S h).addStab = 0 := by
      apply Finset.Subset.antisymm
      · rw [← hstab]
        exact addStab_ordinarySums_mono S hS (Nat.le_succ h)
      · exact Finset.zero_subset.mpr ((ordinarySums_nonempty_generic S hS h).zero_mem_addStab)
    have hk := Finset.add_kneser S (ordinarySums S h)
    change (ordinarySums S (h+1)).addStab = 0 at hstab
    change (S + (ordinarySums S (h+1)).addStab).card +
      (ordinarySums S h + (ordinarySums S (h+1)).addStab).card ≤
      (ordinarySums S (h+1)).card + (ordinarySums S (h+1)).addStab.card at hk
    simp only [hstab, add_zero, Finset.card_zero] at hk
    have hi := ih hst
    have hhsub : h - 1 + 1 = h := Nat.sub_add_cancel hh
    rw [Nat.add_mul, Nat.one_mul, Nat.add_sub_cancel]
    omega

theorem ordinarySums_card_kneser (S : Finset G) (hS : S.Nonempty) (h : ℕ)
    (hh : 1 ≤ h) :
    h * (S + (ordinarySums S h).addStab).card ≤
      (ordinarySums S h).card + (h - 1) * (ordinarySums S h).addStab.card := by
  classical
  let T := ordinarySums S h
  let Q := G ⧸ AddAction.stabilizer G T
  let f : G →+ Q := QuotientAddGroup.mk' _
  have hT : T.Nonempty := ordinarySums_nonempty_generic S hS h
  have himg : ordinarySums (S.image f) h = T.image f := ordinarySums_image S f h
  have hp := ordinarySums_card_aperiodic (S.image f) (hS.image f) h hh
    (by rw [himg]; exact Finset.addStab_image_coe_quotient hT)
  have hcS := Finset.card_addStab_add_card_image_coe' S T
  have hcT := Finset.card_addStab_add_card_image_coe' T T
  rw [Finset.add_addStab] at hcT
  rw [himg] at hp
  have hm := Nat.mul_le_mul_left T.addStab.card hp
  change T.addStab.card * (h * (S.image f).card) ≤
    T.addStab.card * ((T.image f).card + (h - 1)) at hm
  change T.addStab.card * (S.image f).card = (S + T.addStab).card at hcS
  change T.addStab.card * (T.image f).card = T.card at hcT
  rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm T.addStab.card h,
    Nat.mul_assoc, hcS, hcT, Nat.mul_comm T.addStab.card] at hm
  exact hm

end SumsetRanges
