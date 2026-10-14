import Dowling.BraidBlockSingle
import Dowling.FullInverseZIdentification

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Subsingleton G] [Fintype G] {n : ℕ}

omit [Fintype G] in
theorem empty_admissible_iff_no_zero (p : GainPartition G n) :
    Admissible ∅ p ↔ ∀ i, p.code i≠none := by
  constructor
  · intro hp i hi
    rcases hp i hi with ⟨j,hj,_⟩ | ⟨hG,_⟩
    · exact hj
    · obtain ⟨a,b,hab⟩ := hG.exists_pair_ne
      exact hab (Subsingleton.elim a b)
  · intro hp i hi
    exact False.elim (hp i hi)

omit [Fintype G] in
theorem no_zero_iff_le_braidTop (p : GainPartition G (n+1)) :
    (∀ i, p.code i≠none) ↔ p≤GainPartition.braidTop (fun _ => (1:G)) := by
  constructor
  · intro hp x hx
    apply (p.mem_solutionSet x).mpr
    constructor
    · intro i hi
      exact False.elim (hp i hi)
    · intro i r g _
      have htop := (GainPartition.mem_fromBlockRoots_solution _ _ _ _ x).mp hx
      have hi := htop i
      have hr := htop r
      simp only [inv_one,one_mul,gainAct_one] at hi hr
      rw [show g=1 from Subsingleton.elim _ _,gainAct_one]
      exact hi.trans hr.symm
  · intro hp i hi
    obtain ⟨r,hr⟩ := GainPartition.code_some_of_le_braidTop (fun _ => (1:G)) p hp i
    rw [hi] at hr
    cases hr

/-- For the order-one gain group with no retained joints, the literal actual
flat lattice is the braid lower interval, with its rank shift preserved. -/
def trivialJointlessEmbedding : Configuration Unit (Set.univ : Set (Fin n)) ↪o
    Configuration G (∅ : Set (Fin (n+1))) where
  toFun p := ⟨p.val.braidLift (fun _ => (1:G)),
    (empty_admissible_iff_no_zero _).mpr
      ((no_zero_iff_le_braidTop _).mpr (p.val.braidLift_le_braidTop _))⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    exact (GainPartition.braidLowerEmbedding (fun _ : Fin (n+1) => (1:G))).injective
      (congrArg Subtype.val h)
  map_rel_iff' := by
    intro a b
    change a.val.braidLift (fun _ => (1:G))≤b.val.braidLift (fun _ => (1:G)) ↔ a.val≤b.val
    exact GainPartition.braidLift_le_iff _ _ _

omit [Fintype G] in
theorem trivialJointlessEmbedding_surjective : Function.Surjective (trivialJointlessEmbedding (G := G) (n := n)) := by
  intro p
  have hp := (no_zero_iff_le_braidTop p.val).mp ((empty_admissible_iff_no_zero p.val).mp p.property)
  obtain ⟨q,hq⟩ := GainPartition.braidLift_surjective_below (fun _ => (1:G)) p.val hp
  exact ⟨⟨q,admissible_univ q⟩,Subtype.ext hq⟩

def trivialJointlessOrderIso : Configuration Unit (Set.univ : Set (Fin n)) ≃o
    Configuration G (∅ : Set (Fin (n+1))) :=
  OrderIso.ofSurjective trivialJointlessEmbedding trivialJointlessEmbedding_surjective

omit [Fintype G] in
theorem trivialJointlessOrderIso_rank (p : Configuration Unit (Set.univ : Set (Fin n))) :
    configurationRank ∅ (trivialJointlessOrderIso (G := G) p)=configurationRank Set.univ p :=
  p.val.braidLift_rank (fun _ => (1:G))

theorem trivial_jointless_inverseZ (n : ℕ) :
    configurationY (G := G) (∅ : Set (Fin (n+1)))=fullY Unit n := by
  let e := trivialJointlessOrderIso (G := G) (n := n)
  have h := MatroidInverseZ.inverseZ_interval_transport e.toOrderEmbedding
    (fun _ _ y _ _ => ⟨e.symm y,e.apply_symm_apply y⟩)
    (configurationRank Set.univ) (configurationRank ∅)
    (fun a b => by
      change configurationRank ∅ (trivialJointlessOrderIso (G := G) b)-
        configurationRank ∅ (trivialJointlessOrderIso (G := G) a)=_
      rw [trivialJointlessOrderIso_rank,trivialJointlessOrderIso_rank]) ⊥ ⊤
  change MatroidInverseZ.inverseZ (configurationRank ∅) (e ⊥) (e ⊤)=_ at h
  rw [e.map_bot,e.map_top] at h
  exact h

end Dowling
