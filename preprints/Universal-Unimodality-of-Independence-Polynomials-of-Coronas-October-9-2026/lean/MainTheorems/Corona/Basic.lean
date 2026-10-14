import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic

namespace ResearchMain.Corona

open Classical Polynomial

variable {V : Type} [Fintype V] [DecidableEq V]

omit [Fintype V] in
theorem independent_iff (G : SimpleGraph V) (S : Finset V) :
    G.IsIndepSet (S : Set V) ↔ ∀ u ∈ S, ∀ v ∈ S, ¬G.Adj u v := by
  constructor
  · intro h u hu v hv
    by_cases huv : u = v
    · subst v
      exact G.irrefl
    · exact h hu hv huv
  · intro h u hu v hv _
    exact h u hu v hv

omit [Fintype V] in
theorem independent_empty (G : SimpleGraph V) : G.IsIndepSet (∅ : Finset V) := by
  rw [independent_iff]
  simp

omit [Fintype V] in
theorem independent_singleton (G : SimpleGraph V) (v : V) : G.IsIndepSet ({v} : Finset V) := by
  rw [independent_iff]
  intro u hu w hw
  obtain rfl := Finset.mem_singleton.mp hu
  obtain rfl := Finset.mem_singleton.mp hw
  exact G.irrefl

omit [Fintype V] [DecidableEq V] in
theorem independent_mono (G : SimpleGraph V) {S T : Finset V} (hT : G.IsIndepSet (T : Set V))
    (hST : S ⊆ T) : G.IsIndepSet (S : Set V) := by
  exact fun u hu v hv hne => hT (hST hu) (hST hv) hne

noncomputable def independentSets (G : SimpleGraph V) : Finset (Finset V) :=
  Finset.univ.filter (fun S => G.IsIndepSet (S : Set V))

noncomputable def independentCount (G : SimpleGraph V) (k : ℕ) : ℕ :=
  ((independentSets G).filter (fun S => S.card = k)).card

noncomputable def independencePolynomial (G : SimpleGraph V) : ℝ[X] :=
  ∑ S ∈ independentSets G, X ^ S.card

theorem mem_independentSets (G : SimpleGraph V) (S : Finset V) : S ∈ independentSets G ↔
    G.IsIndepSet (S : Set V) := by simp only [independentSets, Finset.mem_filter, Finset.mem_univ, true_and]

theorem independencePolynomial_coeff (G : SimpleGraph V) (k : ℕ) :
    (independencePolynomial G).coeff k = independentCount G k := by
  unfold independencePolynomial independentCount
  simp only [finsetSum_coeff, coeff_X_pow]
  rw [← Finset.sum_filter]
  simp [eq_comm]

theorem independentCount_zero (G : SimpleGraph V) : independentCount G 0 = 1 := by
  have he : (independentSets G).filter (fun S => S.card = 0) = {∅} := by
    ext S
    simp only [Finset.mem_filter, mem_independentSets, Finset.mem_singleton, Finset.card_eq_zero]
    constructor
    · exact And.right
    · intro h
      subst S
      exact ⟨independent_empty G, rfl⟩
  unfold independentCount
  rw [he, Finset.card_singleton]

theorem independentCount_above_order (G : SimpleGraph V) {k : ℕ} (hk : Fintype.card V < k) :
    independentCount G k = 0 := by
  unfold independentCount
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hcard := (Finset.mem_filter.mp hS).2
  have hbound := Finset.card_le_card (Finset.subset_univ S)
  rw [Finset.card_univ, hcard] at hbound
  omega

theorem independencePolynomial_nonnegative (G : SimpleGraph V) (k : ℕ) :
    0 ≤ (independencePolynomial G).coeff k := by
  rw [independencePolynomial_coeff]
  positivity

theorem independencePolynomial_constant (G : SimpleGraph V) :
    (independencePolynomial G).coeff 0 = 1 := by
  rw [independencePolynomial_coeff, independentCount_zero, Nat.cast_one]

theorem independencePolynomial_eval_one (G : SimpleGraph V) :
    (independencePolynomial G).eval 1 = (independentSets G).card := by
  simp [independencePolynomial, eval_finsetSum]

theorem independencePolynomial_derivative_one (G : SimpleGraph V) :
    (independencePolynomial G).derivative.eval 1 = ∑ S ∈ independentSets G, (S.card : ℝ) := by
  simp [independencePolynomial, derivative_X_pow, eval_finsetSum]

end ResearchMain.Corona
