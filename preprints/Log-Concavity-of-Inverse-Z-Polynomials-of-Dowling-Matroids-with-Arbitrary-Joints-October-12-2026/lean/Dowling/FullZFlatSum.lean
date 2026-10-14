import Dowling.FullUpperIntervals
import Dowling.WhitneyRecurrence

noncomputable section
namespace Dowling
open scoped Classical BigOperators
open MatroidInverseZ Polynomial
variable {G : Type*} [Group G] [Fintype G]

def fullConfigurationEquiv (n : ℕ) : Configuration G (Set.univ : Set (Fin n)) ≃ GainPartition G n where
  toFun p := p.val
  invFun p := ⟨p,admissible_univ p⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The actual Z polynomial, obtained by summing the proved contraction
invariant over every genuine flat. -/
theorem fullZ_sum_partitions (n : ℕ) :
    fullZ G n = ∑ p : GainPartition G n, X^(n-p.roots.card)*fullP G p.roots.card := by
  unfold fullZ configurationZ
  rw [zKernel_apply]
  have hi : Finset.Icc (⊥ : Configuration G (Set.univ : Set (Fin n))) ⊤ = Finset.univ := by
    ext p
    simp
  rw [hi]
  simp only [configurationRank_bot,Nat.sub_zero,full_upper_kl]
  exact (fullConfigurationEquiv (G := G) n).sum_comp
    (fun p => X^(n-p.roots.card)*fullP G p.roots.card)

/-- Exact literal Whitney-number transform of the actual full-Dowling KL row. -/
theorem fullZ_whitney_transform (n : ℕ) :
    fullZ G n = ∑ k ∈ Finset.range (n+1),
      C (whitneyCount G n k : ℤ)*X^(n-k)*fullP G k := by
  rw [fullZ_sum_partitions,whitneyCount_sum (G := G) n (fun k => X^(n-k)*fullP G k)]
  apply Finset.sum_congr rfl
  intro k _
  rw [← mul_assoc]
  congr 1

end Dowling
