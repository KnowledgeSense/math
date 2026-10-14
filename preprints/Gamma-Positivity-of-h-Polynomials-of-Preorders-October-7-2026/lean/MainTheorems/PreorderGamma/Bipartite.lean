import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {L R : Type*} [Fintype L] [Fintype R]

noncomputable def graphNeighbors (r : L → R → Prop) (s : Finset L) : Finset R := by
  classical
  exact Finset.univ.filter fun b => ∃ a ∈ s, r a b

def IsDemand (r : L → R → Prop) (d : L → ℕ) : Prop :=
  ∀ s : Finset L, ∑ a ∈ s, d a ≤ (graphNeighbors r s).card

def HasTransversal (r : L → R → Prop) : Prop :=
  ∃ f : L → R, Function.Injective f ∧ ∀ a, r a (f a)

noncomputable def demandSupport (d : L → ℕ) : Finset L := by
  classical
  exact Finset.univ.filter fun a => 0 < d a

omit [Fintype L] in
@[simp] theorem mem_graphNeighbors {r : L → R → Prop} {s : Finset L} {b : R} :
    b ∈ graphNeighbors r s ↔ ∃ a ∈ s, r a b := by
  classical
  simp [graphNeighbors]

omit [Fintype L] in
theorem graphNeighbors_mono (r : L → R → Prop) {s t : Finset L} (h : s ⊆ t) :
    graphNeighbors r s ⊆ graphNeighbors r t := by
  intro b hb
  obtain ⟨a, ha, hab⟩ := mem_graphNeighbors.mp hb
  exact mem_graphNeighbors.mpr ⟨a, h ha, hab⟩

omit [Fintype L] in
theorem hasTransversal_iff_hall (r : L → R → Prop) :
    HasTransversal r ↔ ∀ s : Finset L, s.card ≤ (graphNeighbors r s).card := by
  classical
  simpa [HasTransversal, graphNeighbors] using
    (Fintype.all_card_le_filter_rel_iff_exists_injective r).symm

omit [Fintype L] in
theorem positive_demand_hasTransversal {r : L → R → Prop} {d : L → ℕ}
    (hd : IsDemand r d) (hpos : ∀ a, 0 < d a) : HasTransversal r := by
  apply (hasTransversal_iff_hall r).mpr
  intro s
  have h : s.card ≤ ∑ a ∈ s, d a := by
    calc
      s.card = ∑ a ∈ s, 1 := by simp
      _ ≤ ∑ a ∈ s, d a := by
        apply Finset.sum_le_sum
        intro a ha
        exact hpos a
  exact h.trans (hd s)

theorem demand_total_bound {r : L → R → Prop} {d : L → ℕ} (hd : IsDemand r d) :
    ∑ a : L, d a ≤ Fintype.card R := by
  have h := hd Finset.univ
  have hc : (graphNeighbors r Finset.univ).card ≤ Fintype.card R :=
    Finset.card_le_univ _
  exact h.trans hc

theorem support_card_le_total (d : L → ℕ) :
    (demandSupport d).card ≤ ∑ a : L, d a := by
  classical
  calc
    (demandSupport d).card = ∑ a : L, if 0 < d a then 1 else 0 := by
      rw [demandSupport, Finset.card_filter]
    _ ≤ ∑ a : L, d a := by
      apply Finset.sum_le_sum
      intro a ha
      split_ifs <;> omega

theorem support_card_le_right {r : L → R → Prop} {d : L → ℕ}
    (hd : IsDemand r d) : (demandSupport d).card ≤ Fintype.card R :=
  (support_card_le_total d).trans (demand_total_bound hd)

theorem demand_coordinate_bound {r : L → R → Prop} {d : L → ℕ}
    (hd : IsDemand r d) (a : L) : d a ≤ Fintype.card R := by
  have ha : d a ≤ ∑ b : L, d b :=
    Finset.single_le_sum (fun b hb => Nat.zero_le (d b)) (Finset.mem_univ a)
  exact ha.trans (demand_total_bound hd)

theorem maximal_support_is_indicator {r : L → R → Prop} {d : L → ℕ}
    (hd : IsDemand r d) (hcard : (demandSupport d).card = Fintype.card R) :
    ∀ a, d a = if 0 < d a then 1 else 0 := by
  classical
  have hsmall : ∀ a ∈ (Finset.univ : Finset L),
      (if 0 < d a then 1 else 0) ≤ d a := by
    intro a ha
    split_ifs <;> omega
  have hsum : (∑ a : L, if 0 < d a then 1 else 0) = ∑ a : L, d a := by
    have hc : (demandSupport d).card =
        ∑ a : L, if 0 < d a then 1 else 0 := by
      rw [demandSupport, Finset.card_filter]
    have hlo := support_card_le_total d
    have hhi := demand_total_bound hd
    omega
  intro a
  have heq := (Finset.sum_eq_sum_iff_of_le hsmall).mp hsum a (Finset.mem_univ a)
  exact heq.symm

end ResearchMain.PreorderGamma
