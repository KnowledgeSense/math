import Dowling.JointCompressionFibers
import Dowling.PartitionTauFactors

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

theorem jointCompression_rank (p : GainPartition G n) (i : Fin n) (hi : p.code i=none) :
    partitionRank (jointCompression p i hi)=partitionRank p-1 := by
  change (jointPartition (G := G) i).roots.card-(jointCompression p i hi).roots.card=(n-p.roots.card)-1
  have h1 := jointPartition_roots_card (G := G) i
  have h2 := jointCompression_roots_card p i hi
  omega

omit [Fintype G] in
theorem nonempty_balanced_fiber_root (p : GainPartition G n) (r : Fin n)
    (hr : (p.fiber (some r)).Nonempty) : p.IsRoot r := by
  obtain ⟨j,hj⟩ := hr
  have hc := (Finset.mem_filter.mp hj).2
  cases he : p.code j with
  | none => simp [GainPartition.blockColor,he] at hc
  | some v =>
    rcases v with ⟨s,g⟩
    have hs : s=r := by simpa only [GainPartition.blockColor,he,Option.map_some,Option.some.injEq] using hc
    subst s
    exact p.rooted j r g he

/-- All outside nonsingleton blocks are excluded by the actual KL half-degree
bound, not by deleting them from the correction-flat set. -/
theorem joint_tau_zero_of_nonsingleton (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (k : ℕ) (hRank : partitionRank p=2*k+2) (hz : 2≤(p.fiber none).card)
    (hb : ∃ r : Fin n, 2≤(p.fiber (some r)).card) :
    (partitionP (jointCompression p i hi)).coeff k=0 := by
  apply partitionP_tau_zero
  · rw [jointCompression_rank,hRank]
    omega
  · have h := jointCompression_zero_card p i hi
    omega
  · obtain ⟨r,hr⟩ := hb
    have hroot := nonempty_balanced_fiber_root p r (Finset.card_pos.mp (by omega))
    have hri : r≠i := by
      intro h
      change p.code r=some (r,1) at hroot
      rw [h,hi] at hroot
      cases hroot
    obtain ⟨s,hs⟩ := joint_rootVertex_surjective (G := G) i r hri
    refine ⟨s,?_⟩
    rw [jointCompression_balanced_card,hs]
    exact hr

theorem joint_compression_singleton_P (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (hb : ∀ r : Fin n, (p.fiber (some r)).card≤1) :
    partitionP (jointCompression p i hi)=fullP G ((p.fiber none).card-1) := by
  rw [partitionP_singleton_outside _ (fun s => by rw [jointCompression_balanced_card]; exact hb _)]
  have hc := jointCompression_zero_card p i hi
  congr 1
  omega

theorem joint_tau_singletons (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (k : ℕ) (hRank : partitionRank p=2*k+2)
    (hb : ∀ r : Fin n, (p.fiber (some r)).card≤1) :
    (partitionP (jointCompression p i hi)).coeff k=(fullP G (2*k+1)).coeff k := by
  rw [joint_compression_singleton_P p i hi hb]
  have hr := partitionRank_singleton_outside p hb
  have hz : (p.fiber none).card-1=2*k+1 := by omega
  rw [hz]

end Dowling
