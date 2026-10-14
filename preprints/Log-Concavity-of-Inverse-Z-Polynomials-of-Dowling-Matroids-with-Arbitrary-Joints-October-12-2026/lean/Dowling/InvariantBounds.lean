import Dowling.Invariants
import BoseBurton.ZIncidenceConvolution

noncomputable section
namespace Dowling
open MatroidInverseZ Polynomial
open scoped Classical
variable {G : Type*} [Group G] [Fintype G]

theorem configurationRank_top {n : ℕ} (X : Set (Fin n)) :
    configurationRank X (⊤ : Configuration G X) = (matroid G n X).eRank.toNat := by
  rw [← configurationOrderIso_rank, configurationOrderIso_top]
  change ((matroid G n X).eRk (matroid G n X).E).toNat = _
  rw [← Matroid.eRank_def]

theorem full_configurationRank_top (n : ℕ) :
    configurationRank Set.univ (⊤ : Configuration G (Set.univ : Set (Fin n))) = n := by
  rw [configurationRank_top, full_matroid_eRank]
  simp

theorem full_bot_ne_top (n : ℕ) (hn : 0 < n) :
    (⊥ : Configuration G (Set.univ : Set (Fin n))) ≠ ⊤ := by
  intro h
  have h' := congrArg (configurationRank Set.univ) h
  rw [configurationRank_bot, full_configurationRank_top] at h'
  omega

theorem full_zero_bot_eq_top :
    (⊥ : Configuration G (Set.univ : Set (Fin 0))) = ⊤ := by
  by_contra h
  have hlt := configurationRank_strictMono Set.univ (lt_of_le_of_ne bot_le h)
  rw [configurationRank_bot, full_configurationRank_top] at hlt
  omega

theorem fullP_high_coeff (n k : ℕ) (hn : 0 < n) (hk : n ≤ 2*k) :
    (fullP G n).coeff k = 0 := by
  apply kl_high_coeff _ _ _ (full_bot_ne_top n hn)
  simpa only [full_configurationRank_top, configurationRank_bot, Nat.sub_zero] using hk

@[simp] theorem fullP_zero : fullP G 0 = 1 := by
  unfold fullP configurationP
  rw [full_zero_bot_eq_top, kl_self]

@[simp] theorem fullZ_zero : fullZ G 0 = 1 := by
  unfold fullZ configurationZ
  rw [full_zero_bot_eq_top, zKernel_diag]

@[simp] theorem fullY_zero : fullY G 0 = 1 := by
  unfold fullY configurationY
  rw [full_zero_bot_eq_top, inverseZ_self]

@[simp] theorem fullPSeries_constant : PowerSeries.coeff 0 (fullPSeries G) = 1 := by
  simp [fullPSeries]

@[simp] theorem fullZSeries_constant : PowerSeries.coeff 0 (fullZSeries G) = 1 := by
  simp [fullZSeries]

@[simp] theorem fullYSeries_constant : PowerSeries.coeff 0 (fullYSeries G) = 1 := by
  simp [fullYSeries]

theorem fullZ_coeff_symm (n k : ℕ) (hk : k ≤ n) :
    (fullZ G n).coeff k = (fullZ G n).coeff (n-k) := by
  have h := zKernel_coeff_symm (configurationRank (Set.univ : Set (Fin n)))
    (configurationRank_strictMono Set.univ).monotone
    (⊥ : Configuration G Set.univ) ⊤ k
  simp only [full_configurationRank_top, configurationRank_bot, Nat.sub_zero] at h
  exact h hk

theorem fullY_coeff_symm (n k : ℕ) (hk : k ≤ n) :
    (fullY G n).coeff k = (fullY G n).coeff (n-k) := by
  have h := inverseZ_coeff_symm (configurationRank (Set.univ : Set (Fin n)))
    (configurationRank_strictMono Set.univ).monotone
    (⊥ : Configuration G Set.univ) ⊤ k
  simp only [full_configurationRank_top, configurationRank_bot, Nat.sub_zero] at h
  exact h hk

end Dowling
