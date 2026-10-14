import Dowling.OrderedWordWeights
import Mathlib.Data.Fintype.Perm

noncomputable section
namespace Dowling
open scoped Classical BigOperators
variable {G : Type*} [Group G] [Fintype G] {n k : ℕ}

instance : Fintype (OccupiedWord n k) :=
  inferInstanceAs (Fintype {w : Fin n → Option (Fin k) // ∀ c, ∃ i, w i=some c})
instance : Fintype (OrderedPartition G n k) :=
  inferInstanceAs (Fintype (Σ p : GainPartition G n, Fin k ≃ {i // p.IsRoot i}))
instance : Fintype (DecoratedWord G n k) :=
  inferInstanceAs (Fintype (Σ w : OccupiedWord n k, w.Labels G))

omit [Fintype G] in
theorem root_orderings_card (p : GainPartition G n) (k : ℕ) :
    Fintype.card (Fin k ≃ {i // p.IsRoot i})=
      if p.roots.card=k then k.factorial else 0 := by
  by_cases h : p.roots.card=k
  · simp only [h,ite_true]
    let e : Fin k ≃ {i // p.IsRoot i} := Fintype.equivOfCardEq (by
      rw [Fintype.card_fin,Fintype.card_subtype]
      exact h.symm)
    rw [Fintype.card_equiv e,Fintype.card_fin]
  · simp only [h,ite_false]
    let : IsEmpty (Fin k ≃ {i // p.IsRoot i}) := ⟨fun e => h (by
      have he := Fintype.card_congr e
      rw [Fintype.card_fin,Fintype.card_subtype] at he
      exact he.symm)⟩
    exact Fintype.card_eq_zero

theorem sum_ordered_partitions {R : Type*} [CommSemiring R]
    (f : GainPartition G n → R) (k : ℕ) :
    (∑ p : OrderedPartition G n k, f p.1) =
      (k.factorial : R)*∑ p : GainPartition G n with p.roots.card=k, f p := by
  change (∑ p : (Σ p : GainPartition G n, Fin k ≃ {i // p.IsRoot i}), f p.1)=_
  rw [Fintype.sum_sigma,Finset.mul_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  change (∑ _ : Fin k ≃ {i // p.IsRoot i}, f p)=_
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,root_orderings_card]
  split <;> simp_all

/-- The actual ordered-root bijection counts every normalized gain assignment
once, with no orbit division or commutativity assumption on the gain group. -/
theorem partitionZ_ordered_enumeration (n k : ℕ) :
    (k.factorial : Polynomial ℤ)*
      (∑ p : GainPartition G n with p.roots.card=k, partitionZ p) =
    ∑ w : OccupiedWord n k,
      (∏ c : Fin k, (Fintype.card G : Polynomial ℤ)^((w.fiber (some c)).card-1))*
        (fullZ G (w.fiber none).card *
          ∏ c : Fin k, fullZ Unit ((w.fiber (some c)).card-1)) := by
  rw [← sum_ordered_partitions]
  rw [← Equiv.sum_comp (decoratedWordEquiv (G := G) (n := n) (k := k))]
  change (∑ wl : (Σ w : OccupiedWord n k, w.Labels G), partitionZ (wl.1.partition wl.2))=_
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro w _
  simp only [w.partitionZ_weight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,OccupiedWord.labels_card G w]
  push_cast
  rfl

end Dowling
