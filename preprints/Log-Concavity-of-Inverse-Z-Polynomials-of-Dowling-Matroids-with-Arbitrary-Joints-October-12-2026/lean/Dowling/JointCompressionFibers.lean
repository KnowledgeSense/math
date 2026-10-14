import Dowling.JointCompression

noncomputable section
namespace Dowling
open scoped Classical
variable {G : Type*} [Group G] [Fintype G] {n : ℕ}

omit [Fintype G] in
theorem mem_zero_fiber (p : GainPartition G n) (j : Fin n) :
    j∈p.fiber none ↔ p.code j=none := by
  simp only [GainPartition.fiber,Finset.mem_filter,Finset.mem_univ,true_and,
    GainPartition.blockColor,Option.map_eq_none_iff]

omit [Fintype G] in
theorem jointCompression_zero_fiber_image (p : GainPartition G n) (i : Fin n) (hi : p.code i=none) :
    ((jointCompression p i hi).fiber none).image (jointPartition i).rootVertex=(p.fiber none).erase i := by
  ext j
  simp only [Finset.mem_image,Finset.mem_erase,mem_zero_fiber]
  constructor
  · rintro ⟨c,hc,rfl⟩
    exact ⟨joint_rootVertex_ne i c,(jointCompression_code_none_iff p i hi c).mp hc⟩
  · rintro ⟨hji,hj⟩
    obtain ⟨c,hc⟩ := joint_rootVertex_surjective (G := G) i j hji
    refine ⟨c,?_,hc⟩
    apply (jointCompression_code_none_iff p i hi c).mpr
    rwa [hc]

omit [Fintype G] in
theorem jointCompression_zero_card (p : GainPartition G n) (i : Fin n) (hi : p.code i=none) :
    ((jointCompression p i hi).fiber none).card+1=(p.fiber none).card := by
  have h := congrArg Finset.card (jointCompression_zero_fiber_image p i hi)
  rw [Finset.card_image_of_injective _ (jointPartition i).rootVertex_strictMono.injective] at h
  rw [h]
  exact Finset.card_erase_add_one ((mem_zero_fiber p i).mpr hi)

omit [Fintype G] in
theorem jointCompression_code_map (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (j : Fin (jointPartition (G := G) i).roots.card) :
    ((jointCompression p i hi).code j).map (fun v => ((jointPartition i).rootVertex v.1,v.2)) =
      p.code ((jointPartition i).rootVertex j) := by
  have h := congrArg (fun q : GainPartition G n => q.code ((jointPartition i).rootVertex j))
    (jointCompression_compose p i hi)
  change (jointPartition i).compositeCode (jointCompression p i hi) ((jointPartition i).rootVertex j)=_ at h
  rw [GainPartition.compositeCode_rootVertex] at h
  exact h

omit [Fintype G] in
theorem jointCompression_blockColor_map (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (j : Fin (jointPartition (G := G) i).roots.card) :
    ((jointCompression p i hi).blockColor j).map (jointPartition i).rootVertex =
      p.blockColor ((jointPartition i).rootVertex j) := by
  have h := congrArg (Option.map Prod.fst) (jointCompression_code_map p i hi j)
  simpa only [GainPartition.blockColor,Option.map_map,Function.comp_def] using h

omit [Fintype G] in
theorem jointCompression_balanced_fiber_image (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (s : Fin (jointPartition (G := G) i).roots.card) :
    ((jointCompression p i hi).fiber (some s)).image (jointPartition i).rootVertex =
      p.fiber (some ((jointPartition i).rootVertex s)) := by
  ext j
  simp only [Finset.mem_image,GainPartition.fiber,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨c,hc,rfl⟩
    rw [← jointCompression_blockColor_map p i hi c,hc]
    rfl
  · intro hj
    have hji : j≠i := by
      intro h
      subst j
      change (p.code i).map Prod.fst=some _ at hj
      rw [hi] at hj
      cases hj
    obtain ⟨c,hc⟩ := joint_rootVertex_surjective (G := G) i j hji
    refine ⟨c,?_,hc⟩
    apply Option.map_injective (jointPartition i).rootVertex_strictMono.injective
    rw [jointCompression_blockColor_map,hc]
    exact hj

omit [Fintype G] in
theorem jointCompression_balanced_card (p : GainPartition G n) (i : Fin n) (hi : p.code i=none)
    (s : Fin (jointPartition (G := G) i).roots.card) :
    ((jointCompression p i hi).fiber (some s)).card =
      (p.fiber (some ((jointPartition i).rootVertex s))).card := by
  have h := congrArg Finset.card (jointCompression_balanced_fiber_image p i hi s)
  rwa [Finset.card_image_of_injective _ (jointPartition i).rootVertex_strictMono.injective] at h

end Dowling
