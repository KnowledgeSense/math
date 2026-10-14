import Dowling.PartitionKLDegree
import Dowling.PolynomialProductDegree

noncomputable section
namespace Dowling
open MatroidInverseZ
open scoped Classical BigOperators
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

omit [Fintype G] in
theorem partitionRank_zeroPartition (n : ℕ) : partitionRank (zeroPartition : GainPartition G n)=n := by
  change n-(zeroPartition : GainPartition G n).roots.card=n
  rw [zeroPartition_roots,Finset.card_empty,Nat.sub_zero]

omit [Fintype G] in
theorem GainPartition.SingleBalancedBlock.rank {p : GainPartition G n}
    (hp : p.SingleBalancedBlock) : partitionRank p=n-1 := by
  cases n with
  | zero => obtain ⟨r,_⟩ := hp; exact Fin.elim0 r
  | succ n =>
    obtain ⟨u,rfl⟩ := hp.exists_potentials
    have h := GainPartition.braidLowerEmbedding_rank u (⊤ : GainPartition Unit n)
    rw [GainPartition.braidLowerEmbedding_top] at h
    exact h.trans (partitionRank_zeroPartition n)

omit [Fintype G] in
theorem partitionRank_zero_fiber (p : GainPartition G n) :
    partitionRank (p.fiberTop none)=(p.fiber none).card := by
  rw [p.fiberTop_zero,partitionRank_zeroPartition]

omit [Fintype G] in
theorem partitionRank_balanced_fiber (p : GainPartition G n) (r : Fin n) :
    partitionRank (p.fiberTop (some r))=(p.fiber (some r)).card-1 := by
  by_cases hc : (p.fiber (some r)).card=0
  · change (p.fiber (some r)).card-_= _
    omega
  · exact GainPartition.SingleBalancedBlock.rank (p.fiberTop_some_single r (Nat.pos_of_ne_zero hc))

omit [Fintype G] in
theorem partitionRank_sum_fibers (p : GainPartition G n) :
    partitionRank p=∑ c : Option (Fin n), partitionRank (p.fiberTop c) := by
  have h := p.glue_rank p.fiberTop
  rw [p.glue_fiberTop] at h
  exact h

omit [Fintype G] in
theorem partitionRank_block_formula (p : GainPartition G n) :
    partitionRank p=(p.fiber none).card+∑ r : Fin n, ((p.fiber (some r)).card-1) := by
  rw [partitionRank_sum_fibers,Fintype.sum_option,partitionRank_zero_fiber]
  simp only [partitionRank_balanced_fiber]

/-- An outside nonsingleton balanced block supplies the second positive-rank
factor and annihilates the odd top KL coefficient. -/
theorem partitionP_tau_zero (p : GainPartition G n) (k : ℕ)
    (hRank : partitionRank p=2*k+1) (hz : 0<(p.fiber none).card)
    (hb : ∃ r : Fin n, 2≤(p.fiber (some r)).card) : (partitionP p).coeff k=0 := by
  obtain ⟨r,hr⟩ := hb
  have h := polynomial_product_two_strict
    (fun c : Option (Fin n) => partitionP (p.fiberTop c))
    (fun c => partitionRank (p.fiberTop c))
    (fun c => partitionP_degree_le _) none (some r) (by simp)
    (partitionP_degree_strict _ (by rwa [partitionRank_zero_fiber]))
    (partitionP_degree_strict _ (by rw [partitionRank_balanced_fiber]; omega))
  rw [← partitionP_product,← partitionRank_sum_fibers,hRank] at h
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  omega

/-- With only outside singleton balanced blocks, no extra KL factor remains. -/
theorem partitionP_singleton_outside (p : GainPartition G n)
    (h : ∀ r : Fin n, (p.fiber (some r)).card≤1) :
    partitionP p=fullP G (p.fiber none).card := by
  rw [partitionP_block_formula]
  have he (r : Fin n) : (p.fiber (some r)).card-1=0 := Nat.sub_eq_zero_of_le (h r)
  simp only [he,fullP_zero,Finset.prod_const_one,mul_one]

omit [Fintype G] in
theorem partitionRank_singleton_outside (p : GainPartition G n)
    (h : ∀ r : Fin n, (p.fiber (some r)).card≤1) :
    partitionRank p=(p.fiber none).card := by
  rw [partitionRank_block_formula]
  have he (r : Fin n) : (p.fiber (some r)).card-1=0 := Nat.sub_eq_zero_of_le (h r)
  simp only [he,Finset.sum_const_zero,Nat.add_zero]

end Dowling
