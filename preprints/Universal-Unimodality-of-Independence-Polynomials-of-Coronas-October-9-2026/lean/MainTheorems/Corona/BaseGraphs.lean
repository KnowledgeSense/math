import MainTheorems.Corona.Counting
import MainTheorems.Corona.Joins
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace ResearchMain.Corona

open Classical Polynomial

theorem subset_power_sum {V : Type} [Fintype V] [DecidableEq V] (a b : ℝ[X]) :
    ∑ S : Finset V, a ^ S.card * b ^ (Fintype.card V - S.card) =
      (a + b) ^ Fintype.card V := by
  have h := Fintype.prod_add (fun _ : V => a) (fun _ : V => b)
  simp only [Finset.prod_const, Finset.card_univ, Finset.card_compl] at h
  exact h.symm

theorem independentSets_bottom {V : Type} [Fintype V] [DecidableEq V] :
    independentSets (⊥ : SimpleGraph V) = Finset.univ := by
  ext S
  simp only [mem_independentSets, independent_iff, SimpleGraph.bot_adj, not_false_eq_true,
    implies_true, Finset.mem_univ]

theorem independencePolynomial_bottom {V : Type} [Fintype V] [DecidableEq V] :
    independencePolynomial (⊥ : SimpleGraph V) = (1 + X) ^ Fintype.card V := by
  rw [independencePolynomial, independentSets_bottom]
  have h := subset_power_sum (V := V) X 1
  simpa only [one_pow, mul_one, add_comm X 1] using h

def matchingGraph (m : ℕ) : SimpleGraph (Fin m ⊕ (Fin m × Unit)) :=
  corona (⊥ : SimpleGraph (Fin m)) (⊥ : SimpleGraph Unit)

theorem independencePolynomial_matching (m : ℕ) :
    independencePolynomial (matchingGraph m) = (1 + C 2 * X) ^ m := by
  rw [matchingGraph, independencePolynomial_corona, independentSets_bottom,
    independencePolynomial_bottom]
  simp only [Fintype.card_unique, pow_one, Fintype.card_fin]
  have hs := subset_power_sum (V := Fin m) X (1 + X)
  simp only [Fintype.card_fin] at hs
  rw [hs]
  congr 1
  simp only [map_ofNat]
  ring

def baseGraph (a m : ℕ) : SimpleGraph (Fin a ⊕ (Fin m ⊕ (Fin m × Unit))) :=
  join (⊥ : SimpleGraph (Fin a)) (matchingGraph m)

theorem baseGraph_order (a m : ℕ) : Fintype.card (Fin a ⊕ (Fin m ⊕ (Fin m × Unit))) = a + 2 * m := by
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unique, mul_one]
  omega

theorem independencePolynomial_baseGraph (a m : ℕ) :
    independencePolynomial (baseGraph a m) = (1 + X) ^ a + (1 + C 2 * X) ^ m - 1 := by
  rw [baseGraph, independencePolynomial_join, independencePolynomial_bottom,
    independencePolynomial_matching, Fintype.card_fin]

theorem join_connected {V W : Type} [Nonempty V] [Nonempty W]
    (G : SimpleGraph V) (H : SimpleGraph W) : (join G H).Connected := by
  constructor
  · rintro (u | u) (v | v)
    · exact ((show (join G H).Adj (.inl u) (.inr (Classical.arbitrary W)) from trivial).reachable).trans
        (show (join G H).Adj (.inr (Classical.arbitrary W)) (.inl v) from trivial).reachable
    · exact (show (join G H).Adj (.inl u) (.inr v) from trivial).reachable
    · exact (show (join G H).Adj (.inr u) (.inl v) from trivial).reachable
    · exact ((show (join G H).Adj (.inr u) (.inl (Classical.arbitrary V)) from trivial).reachable).trans
        (show (join G H).Adj (.inl (Classical.arbitrary V)) (.inr v) from trivial).reachable

theorem baseGraph_connected {a m : ℕ} (ha : 1 ≤ a) (hm : 1 ≤ m) : (baseGraph a m).Connected := by
  let : Nonempty (Fin a) := ⟨⟨0, by omega⟩⟩
  let : Nonempty (Fin m) := ⟨⟨0, by omega⟩⟩
  exact join_connected _ _

end ResearchMain.Corona
