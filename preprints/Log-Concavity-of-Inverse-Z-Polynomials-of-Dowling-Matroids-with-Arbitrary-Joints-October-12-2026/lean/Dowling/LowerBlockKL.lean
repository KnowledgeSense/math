import Dowling.LowerProductKL
import Dowling.LowerBlockEvaluation

noncomputable section
namespace Dowling
open MatroidInverseZ
open scoped Classical BigOperators
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

theorem braidTop_partitionP (u : Fin (n+1) → G) :
    partitionP (GainPartition.braidTop u)=fullP Unit n := by
  have h := intervalP_transport (GainPartition.braidLowerEmbedding u)
    (GainPartition.braidLowerEmbedding_interval u) partitionRank partitionRank
    (fun a b => by rw [GainPartition.braidLowerEmbedding_rank,GainPartition.braidLowerEmbedding_rank]) ⊥ ⊤
  rw [GainPartition.braidLowerEmbedding_bot,GainPartition.braidLowerEmbedding_top] at h
  exact h.trans (partitionP_top n)

theorem GainPartition.SingleBalancedBlock.partitionP {p : GainPartition G n}
    (hp : p.SingleBalancedBlock) : Dowling.partitionP p=fullP Unit (n-1) := by
  cases n with
  | zero => obtain ⟨r,_⟩ := hp; exact Fin.elim0 r
  | succ n =>
    obtain ⟨u,rfl⟩ := hp.exists_potentials
    exact braidTop_partitionP u

theorem partitionP_of_size_zero (p : GainPartition G n) (hn : n=0) : partitionP p=1 := by
  subst n
  have hp : p=⊥ := by apply GainPartition.code_injective; funext i; exact Fin.elim0 i
  rw [hp,partitionP,intervalP_diag]

theorem partitionP_zero_fiber (p : GainPartition G n) :
    partitionP (p.fiberTop none)=fullP G (p.fiber none).card := by
  rw [p.fiberTop_zero]
  exact partitionP_top _

theorem partitionP_balanced_fiber (p : GainPartition G n) (r : Fin n) :
    partitionP (p.fiberTop (some r))=fullP Unit ((p.fiber (some r)).card-1) := by
  by_cases hc : (p.fiber (some r)).card=0
  · rw [partitionP_of_size_zero _ hc,hc,Nat.zero_sub,fullP_zero]
  · exact GainPartition.SingleBalancedBlock.partitionP (p.fiberTop_some_single r (Nat.pos_of_ne_zero hc))

theorem partitionP_block_formula (p : GainPartition G n) :
    partitionP p=fullP G (p.fiber none).card *
      ∏ r : Fin n, fullP Unit ((p.fiber (some r)).card-1) := by
  rw [partitionP_product,Fintype.prod_option,partitionP_zero_fiber]
  simp only [partitionP_balanced_fiber]

end Dowling
