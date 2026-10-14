import MainTheorems.DominationRoots.Reflection
import MainTheorems.DominationRoots.LeafSelection
import Mathlib.Data.Nat.Choose.Cast

namespace ResearchMain.DominationRoots

open Polynomial ResearchMain.Domination

variable {V : Type*} [Fintype V]

def RealRooted (f : ℤ[X]) : Prop := (realPolynomial f).Splits

theorem realRoots_X_pow (k : ℕ) : realRoots (X ^ k) = Multiset.replicate k 0 := by
  simp [realRoots, realPolynomial, Multiset.nsmul_singleton]

theorem reflection_trace_X_power {p q : ℤ[X]} {k : ℕ} (hq : q.Monic)
    (he : p = X ^ k * q) :
    rootTrace (reflection q) = ((realRoots p).map (fun x => x ^ 2)).sum + (realRoots p).sum := by
  rw [reflection_trace, he, realRoots_mul (monic_X_pow k) hq, realRoots_X_pow]
  simp

theorem reflected_domination_trace {G : SimpleGraph V}
    (hs : RealRooted (dominationPolynomial G)) (hn : 2 ≤ Fintype.card V)
    {q : ℤ[X]} (hq : q.Monic) (he : dominationPolynomial G = X ^ dominationNumber G * q) :
    rootTrace (reflection q) = 2 * ((leafNeighborhoods G).card : ℝ) := by
  have hdegree : (realPolynomial (dominationPolynomial G)).natDegree = Fintype.card V := by
    rw [realPolynomial, natDegree_map_eq_of_injective Int.cast_injective,
      dominationPolynomial_natDegree]
  have hm : (realPolynomial (dominationPolynomial G)).Monic :=
    (dominationPolynomial_monic G).map (Int.castRingHom ℝ)
  have h1 := split_root_sum hm hs (by rw [hdegree]; omega)
  have h2 := split_root_square_sum hm hs (by rw [hdegree]; exact hn)
  rw [hdegree] at h1 h2
  have hc := dominationPolynomial_top_coefficients G hn
  have hc1 : (realPolynomial (dominationPolynomial G)).coeff (Fintype.card V - 1) =
      ((Fintype.card V - (isolatedVertices G).card : ℕ) : ℝ) := by
    rw [realPolynomial_coeff, hc.2.1]
    norm_cast
  have hc2 : (realPolynomial (dominationPolynomial G)).coeff (Fintype.card V - 2) =
      (Nat.choose (Fintype.card V - (isolatedVertices G).card) 2 : ℝ) -
        ((leafNeighborhoods G).card : ℝ) := by
    rw [realPolynomial_coeff, hc.2.2]
    push_cast
    rfl
  rw [hc1] at h1
  rw [hc1, hc2, Nat.cast_choose_two] at h2
  rw [reflection_trace_X_power hq he]
  change ((realPolynomial (dominationPolynomial G)).roots.map (fun x => x ^ 2)).sum +
    (realPolynomial (dominationPolynomial G)).roots.sum = _
  rw [h1, h2]
  ring

theorem graph_reflection {G : SimpleGraph V} (hs : RealRooted (dominationPolynomial G)) :
    ∃ q : ℤ[X], q.Monic ∧ dominationPolynomial G = X ^ dominationNumber G * q ∧
      q.natDegree = Fintype.card V - dominationNumber G ∧ TotallyPositive (reflection q) := by
  obtain ⟨q, hqm, hq, h0, hc, hd⟩ := dominationPolynomial_factor G
  have hmul : realPolynomial (dominationPolynomial G) =
      realPolynomial (X ^ dominationNumber G) * realPolynomial q := by
    rw [hq, realPolynomial_mul]
  have hsplit : (realPolynomial q).Splits := by
    apply hs.of_dvd ((dominationPolynomial_monic G).map (Int.castRingHom ℝ)).ne_zero
    exact ⟨realPolynomial (X ^ dominationNumber G), hmul.trans (mul_comm _ _)⟩
  have h1 : q.eval (-1) ≠ 0 := by
    intro he
    apply dominationPolynomial_not_root_minus_one G
    change (dominationPolynomial G).eval (-1) = 0
    rw [hq, eval_mul, he, mul_zero]
  exact ⟨q, hqm, hq, hd, reflection_totallyPositive hqm hsplit hc h0 h1⟩

theorem leaf_trace_equality {G : SimpleGraph V} (hs : RealRooted (dominationPolynomial G))
    (hn : 2 ≤ Fintype.card V) :
    dominationNumber G = Fintype.card V - (leafNeighborhoods G).card ∧
      ∃ q : ℤ[X], q.Monic ∧ dominationPolynomial G = X ^ dominationNumber G * q ∧
        TotallyPositive (reflection q) ∧ AllowedProduct (reflection q) := by
  obtain ⟨q, hqm, hq, hd, ht⟩ := graph_reflection hs
  obtain ⟨hb, he⟩ := rootTrace_classification (reflection_monic hqm) ht
  have htrace := reflected_domination_trace hs hn hqm hq
  rw [reflection_natDegree, hd, htrace] at hb
  have hbound : Fintype.card V - dominationNumber G ≤ (leafNeighborhoods G).card := by
    exact_mod_cast (show ((Fintype.card V - dominationNumber G : ℕ) : ℝ) ≤
      ((leafNeighborhoods G).card : ℝ) by linarith)
  have hupper := dominationNumber_le_leaf_bound G
  have hnle := dominationNumber_le_order G
  have hple : (leafNeighborhoods G).card ≤ Fintype.card V := by
    rw [← selectedLeaves_card]
    exact Finset.card_le_univ _
  have hgamma : dominationNumber G = Fintype.card V - (leafNeighborhoods G).card := by omega
  have heq : rootTrace (reflection q) = 2 * ((reflection q).natDegree : ℝ) := by
    rw [htrace, reflection_natDegree, hd]
    have hN : Fintype.card V - dominationNumber G = (leafNeighborhoods G).card := by omega
    rw [hN]
  exact ⟨hgamma, q, hqm, hq, ht, he.mp heq⟩

end ResearchMain.DominationRoots
