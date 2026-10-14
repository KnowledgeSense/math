import Dowling.PartitionAppendEquiv
import Mathlib.Algebra.BigOperators.Fin

noncomputable section
namespace Dowling.GainPartition
open scoped Classical BigOperators
variable {G : Type*} [Group G] {n : ℕ}

theorem append_isRoot_old (p : GainPartition G n) (c : p.LastChoice) (i : Fin n) :
    (p.append c).IsRoot i.castSucc ↔ p.IsRoot i := by
  change p.appendCode c i.castSucc = some (i.castSucc,1) ↔ p.code i = some (i,1)
  rw [appendCode_old]
  exact ⟨fun h => oldCode_map_injective h,fun h => congrArg (Option.map _) h⟩

theorem append_isRoot_last (p : GainPartition G n) (c : p.LastChoice) :
    (p.append c).IsRoot (Fin.last n) ↔ c = none := by
  change p.appendCode c (Fin.last n) = some (Fin.last n,1) ↔ c = none
  rw [appendCode_last]
  cases c with
  | none => simp [lastCode]
  | some c =>
    cases c with
    | none => simp [lastCode]
    | some v =>
      have hne : v.1.val.castSucc ≠ Fin.last n := by
        intro h
        have he := congrArg Fin.val h
        have := v.1.val.isLt
        change v.1.val.val = n at he
        omega
      simp [lastCode,hne]

theorem append_roots_card (p : GainPartition G n) (c : p.LastChoice) :
    (p.append c).roots.card = p.roots.card + if c = none then 1 else 0 := by
  change (Finset.univ.filter (p.append c).IsRoot).card =
    (Finset.univ.filter p.IsRoot).card + _
  rw [Finset.card_filter,Finset.card_filter,Fin.sum_univ_castSucc]
  simp only [append_isRoot_old,append_isRoot_last]

@[simp] theorem append_new_roots_card (p : GainPartition G n) :
    (p.append none).roots.card = p.roots.card+1 := by rw [append_roots_card]; simp

@[simp] theorem append_existing_roots_card (p : GainPartition G n)
    (c : Option ({j // p.IsRoot j} × G)) : (p.append (some c)).roots.card = p.roots.card := by
  rw [append_roots_card]; simp

end Dowling.GainPartition
