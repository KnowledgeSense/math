import MainTheorems.PathCycleTuza.PathTheorem
import MainTheorems.PathCycleTuza.CycleTheorem
import MainTheorems.PathCycleTuza.DisjointUnion

namespace ResearchMain.PathCycleTuza

open Tuza

structure PowerComponent where
  order : ℕ
  exponent : ℕ
  cyclic : Bool

def PowerComponent.graph (c : PowerComponent) : SimpleGraph (Fin c.order) :=
  if c.cyclic then cyclePower c.order c.exponent else pathPower c.order c.exponent

theorem PowerComponent.inequality (c : PowerComponent) : Inequality c.graph := by
  cases h : c.cyclic
  · simpa [PowerComponent.graph, h] using path_inequality c.order c.exponent
  · simpa [PowerComponent.graph, h] using cycle_inequality c.order c.exponent

def UnionVertex : List PowerComponent → Type
  | [] => PEmpty
  | c :: cs => Fin c.order ⊕ UnionVertex cs

instance unionFintype : (cs : List PowerComponent) → Fintype (UnionVertex cs)
  | [] => inferInstanceAs (Fintype PEmpty)
  | c :: cs =>
    letI := unionFintype cs
    inferInstanceAs (Fintype (Fin c.order ⊕ UnionVertex cs))

instance unionDecidableEq : (cs : List PowerComponent) → DecidableEq (UnionVertex cs)
  | [] => inferInstanceAs (DecidableEq PEmpty)
  | c :: cs =>
    letI := unionDecidableEq cs
    inferInstanceAs (DecidableEq (Fin c.order ⊕ UnionVertex cs))

def unionGraph : (cs : List PowerComponent) → SimpleGraph (UnionVertex cs)
  | [] => ⊥
  | c :: cs => sumInternalGraph c.graph (unionGraph cs)

theorem unionGraph_inequality (cs : List PowerComponent) : Inequality (unionGraph cs) := by
  induction cs with
  | nil => exact bottom_inequality _
  | cons c cs ih => exact sum_inequality c.graph (unionGraph cs) c.inequality ih

def IsPowerUnion {V : Type*} (G : SimpleGraph V) : Prop :=
  ∃ cs : List PowerComponent, Nonempty (unionGraph cs ≃g G)

theorem powerUnion_inequality {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : IsPowerUnion G) : coverNumber G ≤ 2 * packingNumber G := by
  obtain ⟨cs, ⟨e⟩⟩ := hG
  exact (inequality_iso e).mp (unionGraph_inequality cs)

theorem path_cycle_sharpness : packingNumber (pathPower 4 3) = 1 ∧
    coverNumber (pathPower 4 3) = 2 ∧ coverNumber (pathPower 4 3) = 2 * packingNumber (pathPower 4 3) := by
  rw [pathPower_complete 4 3 (by decide), complete_four_packingNumber, complete_four_coverNumber]
  decide

theorem powers_tuza :
    (∀ n k : ℕ, Inequality (pathPower n k)) ∧ (∀ n k : ℕ, Inequality (cyclePower n k)) ∧
    (∀ cs : List PowerComponent, Inequality (unionGraph cs)) :=
  ⟨path_inequality, cycle_inequality, unionGraph_inequality⟩

end ResearchMain.PathCycleTuza
