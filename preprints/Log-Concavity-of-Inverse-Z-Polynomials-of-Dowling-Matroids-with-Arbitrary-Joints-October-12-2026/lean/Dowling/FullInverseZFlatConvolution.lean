import Dowling.LowerBlockEvaluation
import Dowling.FullZFlatSum
import BoseBurton.ZIncidenceConvolution

noncomputable section
namespace Dowling
open MatroidInverseZ Polynomial
open scoped Classical BigOperators
variable {G : Type*} [Group G] [Fintype G]

/-- The original incidence inverse relation, expressed through every actual
full-Dowling flat with its exact contraction sign. -/
theorem full_inverseZ_flat_convolution (n : ℕ) :
    (∑ p : GainPartition G n, partitionZ p *
      (C ((-1:ℤ)^p.roots.card)*fullY G p.roots.card)) = if n=0 then 1 else 0 := by
  have h := z_inverseZ_convolution (configurationRank (Set.univ : Set (Fin n)))
    (configurationRank_strictMono Set.univ).monotone
    (⊥ : Configuration G Set.univ) ⊤
  have hi : Finset.Icc (⊥ : Configuration G (Set.univ : Set (Fin n))) ⊤ = Finset.univ := by
    ext p
    simp
  rw [hi] at h
  have hb : ((⊥ : Configuration G (Set.univ : Set (Fin n)))=⊤) ↔ n=0 := by
    constructor
    · intro he
      have hr := congrArg (configurationRank Set.univ) he
      rw [configurationRank_bot,full_configurationRank_top] at hr
      exact hr.symm
    · intro hn
      subst n
      exact full_zero_bot_eq_top
  rw [hb] at h
  have he : (∑ p : Configuration G (Set.univ : Set (Fin n)),
      zKernel (configurationRank Set.univ) ⊥ p *
        (C ((-1:ℤ)^(configurationRank (G := G) (Set.univ : Set (Fin n)) ⊤-configurationRank Set.univ p))*
          inverseZ (configurationRank Set.univ) p ⊤)) =
      ∑ p : Configuration G (Set.univ : Set (Fin n)), partitionZ p.val *
        (C ((-1:ℤ)^p.val.roots.card)*fullY G p.val.roots.card) := by
    apply Finset.sum_congr rfl
    intro p _
    rw [configuration_lower_z,full_upper_inverseZ,full_configurationRank_top]
    have hp := p.val.roots_card_le
    have hr : n-configurationRank Set.univ p=p.val.roots.card := by
      change n-(n-p.val.roots.card)=p.val.roots.card
      omega
    rw [hr]
  rw [he] at h
  by_cases hn : n=0 <;> simp only [hn, ite_true, ite_false] at h ⊢
  all_goals exact ((fullConfigurationEquiv (G := G) n).sum_comp
    (fun p => partitionZ p*(C ((-1:ℤ)^p.roots.card)*fullY G p.roots.card))).symm.trans h

end Dowling
