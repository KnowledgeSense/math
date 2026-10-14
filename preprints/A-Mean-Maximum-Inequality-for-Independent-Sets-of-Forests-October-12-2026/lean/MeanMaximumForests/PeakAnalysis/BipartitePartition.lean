import MeanMaximumForests.PeakAnalysis.BipartitePairs
import MeanMaximumForests.PeakAnalysis.BinomialMass

namespace MeanMaximumForests.PeakAnalysis
open HardCoreActivityThreshold Finset
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def twoColorActivity (L : Finset V) (z w : ℝ) (v : V) : ℝ := if v ∈ L then z else w

theorem finite_subtype_sum {Ω : Type*} [Fintype Ω] (P : Ω → Prop) [DecidablePred P] (f : Ω → ℝ) :
    (∑ x : {x : Ω // P x}, f x.val) = ∑ x : Ω, if P x then f x else 0 := by
  rw [← sum_filter, Finset.sum_subtype (p := P) _ (fun _ => by simp) f]

theorem sum_subsets (S : Finset V) (f : Finset V → ℝ) :
    (∑ s : Finset V, if s ⊆ S then f s else 0) = ∑ s ∈ S.powerset, f s := by
  rw [← sum_filter]
  have he : univ.filter (fun s : Finset V => s ⊆ S) = S.powerset := by ext s; simp
  rw [he]

theorem bipartite_pair_disjoint (G : SimpleGraph V) (L R r l : Finset V)
    (hd : Disjoint L R) (hr : r ⊆ R) (hl : l ⊆ availableIn G L r) : Disjoint r l := by
  apply disjoint_left.mpr
  intro v hvr hvl
  exact disjoint_left.mp hd ((availableIn_subset G L r) (hl hvl)) (hr hvr)

theorem bipartite_pair_weight (G : SimpleGraph V) (L R r l : Finset V) (z w : ℝ)
    (hd : Disjoint L R) (hr : r ⊆ R) (hl : l ⊆ availableIn G L r) :
    (∏ v ∈ r ∪ l, twoColorActivity L z w v) = w ^ r.card * z ^ l.card := by
  rw [prod_union (bipartite_pair_disjoint G L R r l hd hr hl)]
  have hleft : (∏ v ∈ r, twoColorActivity L z w v) = w ^ r.card := by
    have he : ∀ v ∈ r, twoColorActivity L z w v = w := by
      intro v hv
      exact ite_eq_right (fun hvL => disjoint_left.mp hd hvL (hr hv))
    simp only [prod_congr rfl he, prod_const]
  have hright : (∏ v ∈ l, twoColorActivity L z w v) = z ^ l.card := by
    have he : ∀ v ∈ l, twoColorActivity L z w v = z := by
      intro v hv
      exact ite_eq_left ((availableIn_subset G L r) (hl hv))
    simp only [prod_congr rfl he, prod_const]
  rw [hleft, hright]

/-- Exact weighted decomposition into a subset of one color and an arbitrary subset of available vertices of the other. -/
theorem bipartite_weighted_sum (G : SimpleGraph V) (L R : Finset V)
    (hL : Independent G L) (hR : Independent G R) (hd : Disjoint L R) (hc : L ∪ R = univ)
    (z w : ℝ) (f : ℕ → ℝ) :
    (∑ I : Finset V, configurationWeight G (twoColorActivity L z w) I * f I.card) =
      ∑ r ∈ R.powerset, w ^ r.card *
        ∑ l ∈ (availableIn G L r).powerset, z ^ l.card * f (r.card + l.card) := by
  let e := independentBipartiteEquiv G L R hL hR hd hc
  have he := e.symm.sum_comp (fun I : {I : Finset V // Independent G I} =>
    (∏ v ∈ I.val, twoColorActivity L z w v) * f I.val.card)
  have hleft : (∑ I : Finset V, configurationWeight G (twoColorActivity L z w) I * f I.card) =
      ∑ I : {I : Finset V // Independent G I}, (∏ v ∈ I.val, twoColorActivity L z w v) * f I.val.card := by
    rw [finite_subtype_sum (Independent G)
      (fun I : Finset V => (∏ v ∈ I, twoColorActivity L z w v) * f I.card)]
    apply sum_congr rfl
    intro I _
    simp only [configurationWeight, ite_mul, zero_mul]
  rw [hleft, ← he]
  change (∑ p : {p : Finset V × Finset V // p.1 ⊆ R ∧ p.2 ⊆ availableIn G L p.1},
      (∏ v ∈ p.val.1 ∪ p.val.2, twoColorActivity L z w v) * f (p.val.1 ∪ p.val.2).card) = _
  trans ∑ p : Finset V × Finset V, if p.1 ⊆ R ∧ p.2 ⊆ availableIn G L p.1 then
    (∏ v ∈ p.1 ∪ p.2, twoColorActivity L z w v) * f (p.1 ∪ p.2).card else 0
  · exact finite_subtype_sum (fun p : Finset V × Finset V => p.1 ⊆ R ∧ p.2 ⊆ availableIn G L p.1)
      (fun p => (∏ v ∈ p.1 ∪ p.2, twoColorActivity L z w v) * f (p.1 ∪ p.2).card)
  rw [Fintype.sum_prod_type]
  have hp : (∑ r : Finset V, ∑ l : Finset V,
      if r ⊆ R ∧ l ⊆ availableIn G L r then
        (∏ v ∈ r ∪ l, twoColorActivity L z w v) * f (r ∪ l).card else 0) =
      ∑ r : Finset V, if r ⊆ R then w ^ r.card *
        (∑ l : Finset V, if l ⊆ availableIn G L r then z ^ l.card * f (r.card + l.card) else 0) else 0 := by
    apply sum_congr rfl
    intro r _
    by_cases hr : r ⊆ R
    · simp only [hr, true_and, ↓reduceIte, mul_sum]
      apply sum_congr rfl
      intro l _
      by_cases hl : l ⊆ availableIn G L r
      · rw [ite_eq_left hl, ite_eq_left hl, bipartite_pair_weight G L R r l z w hd hr hl,
          card_union_of_disjoint (bipartite_pair_disjoint G L R r l hd hr hl)]
        ring
      · simp only [hl, ↓reduceIte, mul_zero]
    · simp only [hr, false_and, ↓reduceIte, sum_const_zero]
  rw [hp]
  simp_rw [sum_subsets]

/-- The actual partition function is a mixture of binomial partition functions. -/
theorem bipartite_partition (G : SimpleGraph V) (L R : Finset V)
    (hL : Independent G L) (hR : Independent G R) (hd : Disjoint L R) (hc : L ∪ R = univ)
    (z w : ℝ) :
    partitionFunction G (twoColorActivity L z w) =
      ∑ r ∈ R.powerset, w ^ r.card * (1 + z) ^ (availableIn G L r).card := by
  have h := bipartite_weighted_sum G L R hL hR hd hc z w (fun _ => 1)
  simp only [mul_one] at h
  change partitionFunction G (twoColorActivity L z w) = _ at h
  rw [h]
  apply sum_congr rfl
  intro r _
  congr 1
  rw [sum_powerset_apply_card]
  simp only [nsmul_eq_mul]
  rw [add_comm 1 z, add_pow]
  apply sum_congr rfl
  intro k _
  simp only [one_pow, mul_one, mul_comm]

end MeanMaximumForests.PeakAnalysis
