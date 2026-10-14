import Dowling.NontrivialMain
import Dowling.SourceIdentification

noncomputable section
namespace Dowling
open Polynomial
open scoped Classical

/-- The full inverse-Z coefficient conclusion at its actual matroid rank. -/
def StrictInverseZRow (r : ℕ) (p : Polynomial ℤ) : Prop :=
  p.natDegree=r ∧ (∀ k,k≤r → 0<p.coeff k) ∧
    (∀ k,k≤r → p.coeff k=p.coeff (r-k)) ∧
    (∀ k,1≤k → k<r → p.coeff (k-1)*p.coeff (k+1)<(p.coeff k)^2)

theorem strictInverseZRow_one : StrictInverseZRow 0 1 := by
  refine ⟨by simp,?_,?_,?_⟩
  · intro k hk
    have he : k=0 := by omega
    subst k
    norm_num [Polynomial.coeff_one]
  · intro k hk
    have he : k=0 := by omega
    subst k
    norm_num [Polynomial.coeff_one]
  · intro k hk hkr; omega

theorem strictInverseZRow_one_add_X : StrictInverseZRow 1 (1+Polynomial.X) := by
  refine ⟨?_,?_,?_,?_⟩
  · compute_degree; norm_num
  · intro k hk; interval_cases k <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
  · intro k hk; interval_cases k <;> norm_num [Polynomial.coeff_one,Polynomial.coeff_X]
  · intro k hk hkr; omega

variable {G : Type*} [Group G] [Fintype G]

theorem retained_rank_one_main (X : Set (Fin 1)) :
    StrictInverseZRow (matroid G 1 X).eRank.toNat (configurationY (G := G) X) := by
  by_cases hX : X.Nonempty
  · rw [matroid_eRank_marked X hX,configurationY_one_nonempty X hX]
    exact strictInverseZRow_one_add_X
  · have hx : X=∅ := Set.not_nonempty_iff_eq_empty.mp hX
    subst X
    rw [configurationY_one_empty,Matroid.eRank_def,matroid_ground,ground_one_empty,Matroid.eRk_empty]
    exact strictInverseZRow_one

theorem trivial_jointless_rank [Subsingleton G] (n : ℕ) :
    (matroid G (n+1) (∅ : Set (Fin (n+1)))).eRank.toNat=n := by
  have h := trivialJointlessOrderIso_rank (G := G)
    (⊤ : Configuration Unit (Set.univ : Set (Fin n)))
  rw [(trivialJointlessOrderIso (G := G) (n := n)).map_top,configurationRank_top,
    full_configurationRank_top] at h
  exact h

theorem trivial_jointless_actual_main [Subsingleton G] (n : ℕ) :
    StrictInverseZRow (matroid G (n+1) (∅ : Set (Fin (n+1)))).eRank.toNat
      (configurationY (G := G) (∅ : Set (Fin (n+1)))) := by
  rw [trivial_jointless_rank]
  exact trivial_jointless_main n

theorem nontrivial_retained_main [Nontrivial G] {n : ℕ} (hn : 2≤n) (X : Set (Fin n)) :
    StrictInverseZRow (matroid G n X).eRank.toNat (configurationY (G := G) X) := by
  rw [matroid_eRank_nontrivial X hn]
  refine ⟨retained_natDegree hn X (Or.inl inferInstance),?_,?_,?_⟩
  · exact retained_nontrivial_positive hn X
  · exact retained_coeff_symm hn X (Or.inl inferInstance)
  · exact retained_nontrivial_strict hn X

end Dowling
