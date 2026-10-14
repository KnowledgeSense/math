import Dowling.ApexMain

noncomputable section
namespace Dowling
open scoped Classical
variable (G : Type*) [Group G] [Fintype G]

/-- Every finite gain group and every retained-joint subset satisfy the full
inverse-Z theorem at the genuine matroid rank. The order-one jointless case
and the one-vertex empty-ground case are included. -/
theorem retained_dowling_inverseZ (n : ℕ) (hn : 1≤n) (X : Set (Fin n)) :
    StrictInverseZRow (matroid G n X).eRank.toNat
      (MatroidInverseZ.matroidInverseZ (matroid G n X)) := by
  rw [actual_inverseZ_eq_configurationY]
  by_cases h1 : n=1
  · subst n
    exact retained_rank_one_main X
  have hn2 : 2≤n := by omega
  rcases subsingleton_or_nontrivial G with hG | hG
  · let := hG
    by_cases hX : X.Nonempty
    · exact apex_retained_main hn2 X hX
    · have hx : X=∅ := Set.not_nonempty_iff_eq_empty.mp hX
      subst X
      obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n≠0)
      exact trivial_jointless_actual_main r
  · let := hG
    exact nontrivial_retained_main hn2 X

/-- Literal all-index integer strict log-concavity of the original invariant. -/
theorem retained_dowling_strict_log_concave (n : ℕ) (hn : 1≤n) (X : Set (Fin n))
    (k : ℕ) (hk : 1≤k) (hkr : k<(matroid G n X).eRank.toNat) :
    (MatroidInverseZ.matroidInverseZ (matroid G n X)).coeff (k-1)*
      (MatroidInverseZ.matroidInverseZ (matroid G n X)).coeff (k+1)<
    ((MatroidInverseZ.matroidInverseZ (matroid G n X)).coeff k)^2 :=
  (retained_dowling_inverseZ G n hn X).2.2.2 k hk hkr

theorem retained_dowling_coeff_above (n : ℕ) (hn : 1≤n) (X : Set (Fin n))
    (k : ℕ) (hkr : (matroid G n X).eRank.toNat<k) :
    (MatroidInverseZ.matroidInverseZ (matroid G n X)).coeff k=0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [(retained_dowling_inverseZ G n hn X).1]
  exact hkr

end Dowling
