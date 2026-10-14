import GenericValueSemigroups.FormalValues

namespace GenericValueSemigroups

/-- An additive value set containing a full residue window contains the entire tail. -/
theorem additive_tail_of_window (S : Set ℕ) {C m : ℕ} (hm : 0<m) (hmS : m ∈ S)
    (hadd : ∀ a ∈ S, ∀ b ∈ S, a+b ∈ S)
    (hwindow : ∀ n, C≤n → n<C+m → n ∈ S) : ∀ n, C≤n → n ∈ S := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hsmall : n<C+m
    · exact hwindow n hn hsmall
    · have hsub : n-m ∈ S := ih (n-m) (by omega) (by omega)
      have hh := hadd (n-m) hsub m hmS
      simpa only [Nat.sub_add_cancel (show m≤n by omega)] using hh

/-- Equality on the conductor window determines the entire additive value set. -/
theorem value_set_eq_of_window (S G : Set ℕ) {C m : ℕ} (hm : 0<m) (hmS : m ∈ S)
    (hadd : ∀ a ∈ S, ∀ b ∈ S, a+b ∈ S)
    (hG : ∀ n, C≤n → n ∈ G)
    (hwindow : ∀ n, n<C+m → (n ∈ S ↔ n ∈ G)) : S=G := by
  have htail := additive_tail_of_window S hm hmS hadd (fun n hn hnm =>
    (hwindow n hnm).mpr (hG n hn))
  ext n
  by_cases hn : n<C+m
  · exact hwindow n hn
  · exact iff_of_true (htail n (by omega)) (hG n (by omega))

theorem coordinate_order_mem_values {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (hf : ∀ i, PowerSeries.order (f i)=r i) (i : Fin d) :
    r i ∈ polynomialValues f := by
  exact ⟨MvPolynomial.X i, by simpa using hf i⟩

/-- The finite-window argument applied to actual polynomial algebras in coordinate series. -/
theorem polynomialValues_eq_of_window {d : ℕ} (f : Fin d → PowerSeries ℂ)
    (r : Fin d → ℕ) (hf : ∀ i, PowerSeries.order (f i)=r i)
    (i : Fin d) (hi : 0<r i) (G : Set ℕ) (C : ℕ)
    (hG : ∀ n, C≤n → n ∈ G)
    (hwindow : ∀ n, n<C+r i → (n ∈ polynomialValues f ↔ n ∈ G)) :
    polynomialValues f=G := by
  apply value_set_eq_of_window (polynomialValues f) G hi (coordinate_order_mem_values f r hf i)
  · intro a ha b hb
    exact add_mem_polynomialValues f ha hb
  · exact hG
  · exact hwindow

end GenericValueSemigroups
