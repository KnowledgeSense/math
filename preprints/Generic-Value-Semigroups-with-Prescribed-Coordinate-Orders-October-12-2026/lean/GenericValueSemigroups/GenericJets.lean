import GenericValueSemigroups.MonomialJets
import GenericValueSemigroups.GreedyRank
import GenericValueSemigroups.FiniteWindow

namespace GenericValueSemigroups
open scoped BigOperators Classical

noncomputable def orderedMonomialFamily {d p : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (N : ℕ) (e : Fin p ≃ (weightSet r N)) : Fin p → PowerSeries ℂ :=
  fun j => coordinateMonomial f (e j).val

theorem polynomial_value_iff_ordered_span {d p : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (hr : ∀ i, 0<r i) (hf : ∀ i, PowerSeries.order (f i)=r i)
    (N : ℕ) (e : Fin p ≃ (weightSet r N)) (n : ℕ) (hn : n<N) :
    n ∈ polynomialValues f ↔
      ∃ c, PowerSeries.order (seriesCombination (orderedMonomialFamily f r N e) c)=n := by
  constructor
  · rintro ⟨P,hP⟩
    obtain ⟨c,hc⟩ := polynomial_jet_in_monomial_span f r hr hf N P
    refine ⟨c ∘ e, ?_⟩
    have he : seriesCombination (orderedMonomialFamily f r N e) (c ∘ e) =
        seriesCombination (monomialFamily f r N) c := by
      exact e.sum_comp (fun α => c α • coordinateMonomial f α.val)
    rw [he]
    exact (order_eq_of_jet_eq hc hn).mp hP
  · rintro ⟨c,hc⟩
    have he : seriesCombination (orderedMonomialFamily f r N e) c =
        seriesCombination (monomialFamily f r N) (c ∘ e.symm) := by
      simpa only [seriesCombination, orderedMonomialFamily, monomialFamily, Function.comp_apply, Equiv.symm_apply_apply] using
        e.sum_comp (fun α => c (e.symm α) • coordinateMonomial f α.val)
    obtain ⟨P,hP⟩ := monomial_combination_is_polynomial f r N (c ∘ e.symm)
    exact ⟨P,by rw [hP,← he]; exact hc⟩

/-- The explicit greedy minors control the entire value set below the finite cutoff. -/
theorem polynomial_values_of_greedy_minors {d p : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (hr : ∀ i, 0<r i) (hf : ∀ i, PowerSeries.order (f i)=r i)
    (N : ℕ) (e : Fin p ≃ (weightSet r N))
    (w : ℕ → ℕ) (hw : Monotone w)
    (he : ∀ j, weight r (e j).val=w j.val)
    (hm : ∀ (q : ℕ) (hq : q≤greedyPrefixCount w p N),
      (greedyMinor (orderedMonomialFamily f r N e) w q
        (hq.trans (greedyPrefixCount_le w p N))).det ≠ 0)
    (n : ℕ) (hn : n<N) :
    n ∈ polynomialValues f ↔ ∃ j<p, greedy w j=n := by
  rw [polynomial_value_iff_ordered_span f r hr hf N e n hn]
  apply finite_span_values_of_greedy_minors _ w hw _ N hm n hn
  intro j
  change PowerSeries.order (coordinateMonomial f (e j).val)=w j.val
  rw [order_coordinateMonomial f r _ hf]
  exact_mod_cast he j

theorem polynomial_values_below_cutoff {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (hr : ∀ i, 0<r i) (hd : 0<d)
    (hf : ∀ i, PowerSeries.order (f i)=r i)
    (N : ℕ) (e : Fin (weightCount r N) ≃ (weightSet r N))
    (he : ∀ j, weight r (e j).val=weightAt r hr hd j.val)
    (hm : ∀ (q : ℕ) (hq : q≤greedyPrefixCount (weightAt r hr hd) (weightCount r N) N),
      (greedyMinor (orderedMonomialFamily f r N e) (weightAt r hr hd) q
        (hq.trans (greedyPrefixCount_le _ _ N))).det ≠ 0)
    (n : ℕ) (hn : n<N) :
    n ∈ polynomialValues f ↔ n ∈ Set.range (greedy (weightAt r hr hd)) := by
  rw [polynomial_values_of_greedy_minors f r hr hf N e _ (weightAt_mono r hr hd) he hm n hn]
  constructor
  · rintro ⟨j,_,hj⟩; exact ⟨j,hj⟩
  · rintro ⟨j,hj⟩
    refine ⟨j,?_,hj⟩
    apply (weightAt_lt_iff r hr hd j N).mp
    have hh := weight_le_greedy (weightAt r hr hd) j
    omega

/-- A single conductor-length jet condition determines the full polynomial value semigroup. -/
theorem polynomial_values_eq_greedy_of_minors {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (hr : ∀ i, 0<r i) (hd : 0<d)
    (hf : ∀ i, PowerSeries.order (f i)=r i) (i : Fin d) (C : ℕ)
    (hC : ∀ n, C≤n → n ∈ Set.range (greedy (weightAt r hr hd)))
    (e : Fin (weightCount r (C+r i)) ≃ (weightSet r (C+r i)))
    (he : ∀ j, weight r (e j).val=weightAt r hr hd j.val)
    (hm : ∀ (q : ℕ)
      (hq : q≤greedyPrefixCount (weightAt r hr hd) (weightCount r (C+r i)) (C+r i)),
      (greedyMinor (orderedMonomialFamily f r (C+r i) e) (weightAt r hr hd) q
        (hq.trans (greedyPrefixCount_le _ _ (C+r i)))).det ≠ 0) :
    polynomialValues f=Set.range (greedy (weightAt r hr hd)) := by
  apply polynomialValues_eq_of_window f r hf i (hr i) _ C hC
  exact polynomial_values_below_cutoff f r hr hd hf (C+r i) e he hm

end GenericValueSemigroups
