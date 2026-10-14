import Dowling.RankOneInvariant
import Dowling.FullInverseZStrict

noncomputable section
namespace Dowling
open Polynomial MatroidInverseZ
open scoped Classical
variable {G : Type*} [Group G] [Fintype G]

theorem fullY_one : fullY G 1=1+Polynomial.X := by
  have hd : configurationRank (Set.univ : Set (Fin 1)) (⊤ : Configuration G Set.univ)=
      configurationRank (Set.univ : Set (Fin 1)) (⊥ : Configuration G Set.univ)+1 := by
    rw [full_configurationRank_top,configurationRank_bot]
  change inverseZ (configurationRank Set.univ) (⊥ : Configuration G (Set.univ : Set (Fin 1))) ⊤=_
  rw [inverseZ_rank_one_split _ (configurationRank_strictMono _) _ _ bot_le hd,
    inverseKL_rank_one _ (configurationRank_strictMono _) _ _ bot_le hd]

theorem configurationY_of_rank_zero {n : ℕ} (X : Set (Fin n))
    (hr : (matroid G n X).eRank=0) : configurationY (G := G) X=1 := by
  have ht : configurationRank X (⊤ : Configuration G X)=0 := by rw [configurationRank_top,hr]; rfl
  have he : (⊥ : Configuration G X)=⊤ := by
    by_contra h
    have hh := configurationRank_strictMono X (lt_of_le_of_ne bot_le h)
    rw [configurationRank_bot,ht] at hh
    omega
  rw [configurationY,he,inverseZ_self]

omit [Group G] [Fintype G] in
theorem ground_one_empty : ground G 1 (∅ : Set (Fin 1))=∅ := by
  ext e
  simp only [Set.mem_empty_iff_false,iff_false]
  cases e with
  | inl i => exact fun h => h
  | inr e => exact fun _ => e.ordered.ne (Subsingleton.elim e.tail e.head)

theorem configurationY_one_empty : configurationY (G := G) (∅ : Set (Fin 1))=1 := by
  apply configurationY_of_rank_zero
  rw [Matroid.eRank_def,matroid_ground,ground_one_empty,Matroid.eRk_empty]

theorem configurationY_one_nonempty (X : Set (Fin 1)) (hX : X.Nonempty) :
    configurationY (G := G) X=1+Polynomial.X := by
  have he : X=Set.univ := by
    apply Set.eq_univ_of_forall
    obtain ⟨i,hi⟩ := hX
    intro j
    exact Subsingleton.elim i j ▸ hi
  rw [he]
  exact fullY_one

end Dowling
