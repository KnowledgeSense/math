import Dowling.RetainedEndpoints

noncomputable section
namespace MatroidInverseZ
open Finset Polynomial
variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α] [DecidableLE α]

omit [DecidableLE α] in
theorem inverseZ_coeff_above_rank (r : α→ℕ) (hr : Monotone r) (a b : α)
    (k : ℕ) (hk : r b-r a<k) : (inverseZ r a b).coeff k=0 := by
  rw [inverseZ,Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro x hx
  obtain ⟨hax,hxb⟩ := Finset.mem_Icc.mp hx
  rw [mul_assoc,coeff_C_mul,coeff_X_pow_mul']
  by_cases hd : r b-r x≤k
  · rw [ite_eq_left hd]
    have h1 := hr hax
    have h2 := hr hxb
    have ht : (inverseKL r a x).coeff (k-(r b-r x))=0 := by
      by_cases he : a=x
      · subst x
        rw [inverseKL_self]
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        simp only [Polynomial.natDegree_one]
        omega
      · exact inverseKL_high_coeff r hr a x hax he _ (by omega)
    rw [ht,mul_zero]
  · rw [ite_eq_right hd,mul_zero]

end MatroidInverseZ

namespace Dowling
open Polynomial MatroidInverseZ
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

theorem retained_configurationRank_top (hn : 2≤n) (X : Set (Fin n))
    (hX : Nontrivial G ∨ X.Nonempty) :
    configurationRank X (⊤ : Configuration G X)=n := by
  rw [configurationRank_top]
  rcases hX with hG | hx
  · rw [matroid_eRank_nontrivial X hn]
    simp
  · rw [matroid_eRank_marked X hx]
    simp

theorem retained_coeff_symm (hn : 2≤n) (X : Set (Fin n))
    (hX : Nontrivial G ∨ X.Nonempty) (k : ℕ) (hk : k≤n) :
    (configurationY (G := G) X).coeff k=(configurationY (G := G) X).coeff (n-k) := by
  have h := inverseZ_coeff_symm (configurationRank X) (configurationRank_strictMono X).monotone
    (⊥ : Configuration G X) ⊤ k
  have hb : k≤configurationRank X (⊤ : Configuration G X)-configurationRank X (⊥ : Configuration G X) := by
    simpa only [retained_configurationRank_top hn X hX,configurationRank_bot,Nat.sub_zero] using hk
  simpa only [configurationY,retained_configurationRank_top hn X hX,configurationRank_bot,Nat.sub_zero] using h hb

theorem retained_coeff_above (hn : 2≤n) (X : Set (Fin n))
    (hX : Nontrivial G ∨ X.Nonempty) (k : ℕ) (hk : n<k) :
    (configurationY (G := G) X).coeff k=0 := by
  apply inverseZ_coeff_above_rank (configurationRank X) (configurationRank_strictMono X).monotone
  simpa only [retained_configurationRank_top hn X hX,configurationRank_bot,Nat.sub_zero] using hk

end Dowling
