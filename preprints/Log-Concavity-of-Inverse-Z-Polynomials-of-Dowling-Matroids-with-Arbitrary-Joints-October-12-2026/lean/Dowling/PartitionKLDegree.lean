import Dowling.LowerBlockKL

noncomputable section
namespace Dowling
open MatroidInverseZ
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

theorem partitionRank_strictMono : StrictMono (partitionRank (G := G) (n := n)) := by
  intro p q hpq
  exact configurationRank_strictMono Set.univ ((fullPartitionOrderIso n).strictMono hpq)

theorem partitionRank_bot : partitionRank (⊥ : GainPartition G n)=0 :=
  configurationRank_bot Set.univ

theorem partitionP_degree_strict (p : GainPartition G n) (hp : 0<partitionRank p) :
    2*(partitionP p).natDegree<partitionRank p := by
  have hne : (⊥ : GainPartition G n)≠p := by
    intro h
    rw [← h,partitionRank_bot] at hp
    omega
  by_cases hz : partitionP p=0
  · simp only [hz,Polynomial.natDegree_zero,mul_zero]
    exact hp
  · by_contra h
    have hc := kl_high_coeff partitionRank ⊥ p hne (partitionP p).natDegree (by omega)
    exact hz (Polynomial.leadingCoeff_eq_zero.mp (Polynomial.coeff_natDegree.symm.trans hc))

theorem partitionP_degree_le (p : GainPartition G n) :
    2*(partitionP p).natDegree≤partitionRank p := by
  by_cases hp : p=⊥
  · rw [hp,partitionP,intervalP_diag,partitionRank_bot]
    simp
  · have hr : 0<partitionRank p := by
      have h := partitionRank_strictMono (G := G) (n := n) (bot_lt_iff_ne_bot.mpr hp)
      rwa [partitionRank_bot] at h
    exact (partitionP_degree_strict p hr).le

end Dowling
