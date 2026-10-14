import GenericValueSemigroups.WeightCounting
import GenericValueSemigroups.GreedySequence

namespace GenericValueSemigroups
open scoped Classical

theorem weightAt_le_index_above_cutoff {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (i j : Fin d) (hij : i ≠ j)
    {k : ℕ} (hk : weightCount r (4*r i*r j) ≤ k) : weightAt r hr hd k ≤ k := by
  have hc := weightAt_unbounded r hr hd (4*r i*r j) k hk
  exact le_trans (weightCount_ge_above_cutoff r hr i j hij hc)
    (weightCount_at_weightAt r hr hd k)

/-- The largest weight deficit is attained, using the actual two-coordinate monomial count. -/
theorem exists_weight_deficit_maximum {d : ℕ} (r : Fin d → ℕ)
    (hr : ∀ i, 0 < r i) (hd : 0 < d) (i j : Fin d) (hij : i ≠ j) :
    ∃ D J : ℕ, (∀ k, weightAt r hr hd k ≤ k+D) ∧ weightAt r hr hd J = J+D := by
  let B := weightCount r (4*r i*r j)
  let D := (Finset.range (B+1)).sup (fun k => weightAt r hr hd k-k)
  have hbound : ∀ k, weightAt r hr hd k ≤ k+D := by
    intro k
    by_cases hk : k ≤ B
    · have hh : weightAt r hr hd k-k ≤ D :=
        Finset.le_sup (f := fun k => weightAt r hr hd k-k) (Finset.mem_range.mpr (by omega))
      omega
    · have hh := weightAt_le_index_above_cutoff r hr hd i j hij (k := k) (by omega)
      omega
  by_cases hD : D=0
  · exact ⟨D, 0, hbound, by simp [hD]⟩
  · obtain ⟨J, hJ, he⟩ := Finset.exists_mem_eq_sup (Finset.range (B+1))
      (by simp) (fun k => weightAt r hr hd k-k)
    change D = weightAt r hr hd J-J at he
    exact ⟨D,J,hbound,by omega⟩

/-- The counting deficit never exceeds the maximum weight deficit. -/
theorem count_deficit_bound {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) (D : ℕ) (h : ∀ k, weightAt r hr hd k ≤ k+D) (n : ℕ) :
    n ≤ weightCount r n + D := by
  have hw := weightAt_unbounded r hr hd n (weightCount r n) (le_refl _)
  exact le_trans hw (h _)

theorem count_deficit_attained {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) (D J : ℕ) (h : ∀ k, weightAt r hr hd k ≤ k+D)
    (hJ : weightAt r hr hd J = J+D) : weightCount r (weightAt r hr hd J) = J := by
  have hu := weightCount_at_weightAt r hr hd J
  have hl := count_deficit_bound r hr hd D h (weightAt r hr hd J)
  omega

/-- Cofiniteness and genus for the greedy sequence of actual monomial weights. -/
theorem actual_greedy_gaps {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0 < r i)
    (hd : 0 < d) (i j : Fin d) (hij : i ≠ j) :
    ∃ D J : ℕ, ∃ gaps : Finset ℕ,
      (∀ n, n ∈ gaps ↔ n ∉ Set.range (greedy (weightAt r hr hd))) ∧
      gaps.card = D ∧ (∀ n, n ≤ weightCount r n + D) ∧
      weightAt r hr hd J = J+D ∧ weightCount r (weightAt r hr hd J) = J := by
  obtain ⟨D,J,h,hJ⟩ := exists_weight_deficit_maximum r hr hd i j hij
  obtain ⟨gaps,hg,hcard⟩ := greedy_gaps_finite_card (weightAt r hr hd) D J h hJ
  exact ⟨D,J,gaps,hg,hcard,count_deficit_bound r hr hd D h,hJ,
    count_deficit_attained r hr hd D J h hJ⟩

end GenericValueSemigroups
