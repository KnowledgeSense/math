import Dowling.RetainedRankBounds
import Dowling.TrivialJointlessIntervals

noncomputable section
namespace Dowling
open Finset Polynomial
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

theorem retained_constant_pos (hn : 2≤n) (X : Set (Fin n))
    (hX : Nontrivial G ∨ X.Nonempty) : 0<(configurationY (G := G) X).coeff 0 := by
  rw [retained_constant_product hn X hX]
  apply mul_pos
  · have hm : (1 : ℤ)≤Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
    have hn1 : (0 : ℤ)<(n-1 : ℕ) := by exact_mod_cast (show 0<n-1 by omega)
    rcases hX with hG | hx
    · have hmg : (1 : ℤ)<Fintype.card G := by exact_mod_cast Fintype.one_lt_card (α := G)
      have hp := mul_pos (sub_pos.mpr hmg) hn1
      have hk : (0 : ℤ)≤X.toFinset.card := by positivity
      omega
    · have hk : (0 : ℤ)<X.toFinset.card := by
        exact_mod_cast Finset.card_pos.mpr (by simpa using hx : X.toFinset.Nonempty)
      have hp := mul_nonneg (sub_nonneg.mpr hm) hn1.le
      omega
  · apply Finset.prod_pos
    intro j hj
    have hm : (0 : ℤ)≤Fintype.card G := by positivity
    have hj : (0 : ℤ)≤j := by positivity
    positivity

theorem retained_natDegree (hn : 2≤n) (X : Set (Fin n))
    (hX : Nontrivial G ∨ X.Nonempty) : (configurationY (G := G) X).natDegree=n := by
  apply le_antisymm
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mpr (fun k hk => retained_coeff_above hn X hX k hk)
  · apply Polynomial.le_natDegree_of_ne_zero
    have hs := retained_coeff_symm hn X hX 0 (Nat.zero_le _)
    simp only [Nat.sub_zero] at hs
    rw [← hs]
    exact ne_of_gt (retained_constant_pos hn X hX)

theorem trivial_jointless_main [Subsingleton G] (n : ℕ) :
    (configurationY (G := G) (∅ : Set (Fin (n+1)))).natDegree=n ∧
    (∀ k,k≤n → 0<(configurationY (G := G) (∅ : Set (Fin (n+1)))).coeff k) ∧
    (∀ k,k≤n → (configurationY (G := G) (∅ : Set (Fin (n+1)))).coeff k=
      (configurationY (G := G) (∅ : Set (Fin (n+1)))).coeff (n-k)) ∧
    (∀ k,1≤k → k<n →
      (configurationY (G := G) (∅ : Set (Fin (n+1)))).coeff (k-1)*
        (configurationY (G := G) (∅ : Set (Fin (n+1)))).coeff (k+1)<
      ((configurationY (G := G) (∅ : Set (Fin (n+1)))).coeff k)^2) := by
  rw [trivial_jointless_inverseZ]
  exact full_dowling_inverseZ n

end Dowling
