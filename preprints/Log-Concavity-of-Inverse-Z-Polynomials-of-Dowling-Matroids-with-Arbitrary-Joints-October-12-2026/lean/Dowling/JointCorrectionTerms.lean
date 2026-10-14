import Dowling.JointSurvivors
import Dowling.DeletionKLTau

noncomputable section
namespace Dowling
open Polynomial MatroidInverseZ
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ} {X : Set (Fin n)}

/-- The actual correction summand, before any family-specific elimination. -/
def jointCorrectionTerm (i : Fin n) (hiX : i∈X) (p : Configuration G X) : Polynomial ℤ :=
  C (deletionTau (configurationRank X) (jointConfiguration i hiX) p)*
    Polynomial.X^(configurationRank X p/2)*inverseZ (configurationRank X) p ⊤

omit [Fintype G] in
theorem jointConfiguration_le_iff (i : Fin n) (hiX : i∈X) (p : Configuration G X) :
    jointConfiguration (G := G) i hiX≤p ↔ p.val.code i=none :=
  jointPartition_le_iff i p.val

theorem jointTau_even_rank (i : Fin n) (hiX : i∈X) (p : Configuration G X)
    (hi : p.val.code i=none) (k : ℕ) (hr : configurationRank X p=2*k+2) :
    deletionTau (configurationRank X) (jointConfiguration i hiX) p=
      (partitionP (jointCompression p.val i hi)).coeff k := by
  rw [deletionTau,ite_eq_left ⟨(jointConfiguration_le_iff i hiX p).mpr hi,by
    rw [jointConfiguration_rank,hr]; omega⟩]
  rw [joint_restriction_kl p i hiX hi,jointConfiguration_rank,hr]
  congr 1
  omega

/-- The outside block exclusion is a consequence of the original KL degree
bound at the actual restriction-contraction interval. -/
theorem jointCorrectionTerm_nonsingleton (i : Fin n) (hiX : i∈X) (p : Configuration G X)
    (hi : p.val.code i=none) (hz : 2≤(p.val.fiber none).card)
    (hb : ∃ r : Fin n, 2≤(p.val.fiber (some r)).card) : jointCorrectionTerm i hiX p=0 := by
  have ht : deletionTau (configurationRank X) (jointConfiguration i hiX) p=0 := by
    by_cases hpar : (configurationRank X p-1)%2=1
    · let k := (configurationRank X p-1)/2
      have hr : configurationRank X p=2*k+2 := by omega
      rw [jointTau_even_rank i hiX p hi k hr]
      exact joint_tau_zero_of_nonsingleton p.val i hi k hr hz hb
    · simp [deletionTau,jointConfiguration_rank,hpar]
  simp [jointCorrectionTerm,ht]

/-- The surviving rank-r correction, expressed using actual full-Dowling KL
and inverse-Z polynomials. -/
def jointRankCorrection (G : Type*) [Group G] [Fintype G] (n r : ℕ) : Polynomial ℤ :=
  if r%2=0 ∧ 2≤r then C ((fullP G (r-1)).coeff ((r-1)/2))*
    Polynomial.X^(r/2)*fullY G (n-r) else 0

theorem jointCorrectionTerm_singleton (i : Fin n) (hiX : i∈X) (p : Configuration G X)
    (hi : p.val.code i=none) (hb : ∀ r : Fin n, (p.val.fiber (some r)).card≤1) :
    jointCorrectionTerm i hiX p=jointRankCorrection G n (p.val.fiber none).card := by
  have hr : configurationRank X p=(p.val.fiber none).card := partitionRank_singleton_outside p.val hb
  have hroot : p.val.roots.card=n-(p.val.fiber none).card := by
    have hle := p.val.roots_card_le
    change n-p.val.roots.card=(p.val.fiber none).card at hr
    omega
  rw [jointCorrectionTerm,zeroBlock_upper_inverseZ p ⟨i,hi⟩,hroot,hr]
  have ht : deletionTau (configurationRank X) (jointConfiguration i hiX) p=
      if (p.val.fiber none).card%2=0 ∧ 2≤(p.val.fiber none).card then
        (fullP G ((p.val.fiber none).card-1)).coeff (((p.val.fiber none).card-1)/2) else 0 := by
    rw [deletionTau,jointConfiguration_rank,hr]
    have hle := (jointConfiguration_le_iff i hiX p).mpr hi
    have hpar : ((p.val.fiber none).card-1)%2=1 ↔
        (p.val.fiber none).card%2=0 ∧ 2≤(p.val.fiber none).card := by omega
    simp only [hle,true_and,hpar]
    congr 1
    rw [joint_restriction_kl p i hiX hi,joint_compression_singleton_P p.val i hi hb]
  rw [ht]
  unfold jointRankCorrection
  split <;> simp

end Dowling
