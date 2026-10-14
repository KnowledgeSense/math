import MainTheorems.PreorderGamma.Transport
import MainTheorems.PreorderGamma.DemandMatching

namespace ResearchMain.PreorderGamma

open scoped BigOperators

variable {L R : Type*} [Fintype L] [Fintype R]

def IsSupplyDemand (r : L → R → Prop) (d : L → ℕ) (s : R → ℕ) : Prop :=
  ∀ A : Finset L, ∑ a ∈ A, d a ≤ ∑ b ∈ graphNeighbors r A, s b

omit [Fintype L] in
theorem supplyCell_neighbors (r : L → R → Prop) (s : R → ℕ) (A : Finset L) :
    graphNeighbors (fun a : L => fun c : DemandCells s => r a c.1) A =
      (graphNeighbors r A).sigma (fun b => (Finset.univ : Finset (Fin (s b)))) := by
  classical
  ext c
  simp only [mem_graphNeighbors, Finset.mem_sigma, Finset.mem_univ, and_true]

omit [Fintype L] in
theorem supplyCell_demand_iff (r : L → R → Prop) (d : L → ℕ) (s : R → ℕ) :
    IsDemand (fun a : L => fun c : DemandCells s => r a c.1) d ↔ IsSupplyDemand r d s := by
  classical
  unfold IsDemand IsSupplyDemand
  simp only [supplyCell_neighbors, Finset.card_sigma, Finset.card_univ, Fintype.card_fin]

theorem naturalTransport_supplyDemand (r : L → R → Prop) (d : L → ℕ) (s : R → ℕ)
    (hd : IsSupplyDemand r d s) (htotal : (∑ a, d a) = ∑ b, s b) :
    Nonempty (NaturalTransport r d s) := by
  classical
  have hc := (supplyCell_demand_iff r d s).mpr hd
  obtain ⟨f, hf, hrel⟩ := (demand_iff_cell_transversal _ d).mp hc
  have hcard : Fintype.card (DemandCells d) = Fintype.card (DemandCells s) := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using htotal
  let e : DemandCells d ≃ DemandCells s :=
    Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, hcard⟩)
  let F : L → R → ℕ := fun a b => ∑ c : Fin (d a), if (e ⟨a, c⟩).1 = b then 1 else 0
  refine ⟨⟨F, ?_, ?_, ?_⟩⟩
  · intro a b hab
    apply Finset.sum_eq_zero
    intro c hc
    have hne : (e ⟨a, c⟩).1 ≠ b := fun h => hab (h ▸ hrel ⟨a, c⟩)
    exact ite_eq_right hne
  · intro a
    dsimp only [F]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_id]
  · intro b
    change (∑ a, ∑ c : Fin (d a), if (e ⟨a, c⟩).1 = b then 1 else 0) = s b
    rw [← Fintype.sum_sigma']
    calc
      _ = ∑ c : DemandCells s, if c.1 = b then 1 else 0 := by
        apply Fintype.sum_equiv e
        intro c
        rfl
      _ = s b := by
        rw [Fintype.sum_sigma]
        calc
          _ = ∑ a : R, if a = b then s a else 0 := by
            apply Finset.sum_congr rfl
            intro a ha
            by_cases hab : a = b <;> simp [hab]
          _ = _ := by simp

theorem NaturalTransport.supplyDemand {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}
    (p : NaturalTransport r d s) : IsSupplyDemand r d s := by
  classical
  intro A
  let B := graphNeighbors r A
  have hrow : (∑ a ∈ A, d a) = ∑ a ∈ A, ∑ b ∈ B, p.flow a b := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [← p.row_sum a]
    symm
    apply Finset.sum_subset (Finset.subset_univ B)
    intro b hb hnot
    have hrel : ¬r a b := fun hab => hnot (mem_graphNeighbors.mpr ⟨a, ha, hab⟩)
    exact p.supported a b hrel
  rw [hrow, Finset.sum_comm]
  apply Finset.sum_le_sum
  intro b hb
  calc
    _ ≤ ∑ a, p.flow a b := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ A) (fun a ha hnot => Nat.zero_le _)
    _ = s b := p.column_sum b

theorem naturalTransport_nonempty_iff (r : L → R → Prop) (d : L → ℕ) (s : R → ℕ) :
    Nonempty (NaturalTransport r d s) ↔
      IsSupplyDemand r d s ∧ (∑ a, d a) = ∑ b, s b := by
  constructor
  · rintro ⟨p⟩
    exact ⟨p.supplyDemand, p.total_eq⟩
  · rintro ⟨hD, hT⟩
    exact naturalTransport_supplyDemand r d s hD hT

end ResearchMain.PreorderGamma
