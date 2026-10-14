import FourGeneratedSemigroups.StaircaseSliceCounts

noncomputable section
namespace FourGeneratedSemigroups
open PlaneStaircase
variable {S : NumericalSemigroup} (G : FourGenerated S)

lemma sum_corners_balance (n : ℕ) :
    Nat.card (Corners (planeSlice G 0)) +
      ∑ z ∈ Finset.range n, Nat.card (NewCorners (planeSlice G z) (planeSlice G (z+1))) =
    Nat.card (Corners (planeSlice G n)) +
      ∑ z ∈ Finset.range n, Nat.card (LostCorners (planeSlice G z) (planeSlice G (z+1))) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := corners_balance (planeSlice_finite G n) (planeSlice_finite G (n+1))
      (planeSlice_antitone G (Nat.le_succ n))
    simp only [Finset.sum_range_succ]
    omega

lemma corners_card_eq_base_add_new :
    Nat.card (staircaseCorners G) = Nat.card (Corners (planeSlice G 0)) +
      ∑ z ∈ Finset.range (criticalExponent G.generators G.positive 3),
        Nat.card (NewCorners (planeSlice G z) (planeSlice G (z+1))) := by
  have h := sum_corners_balance G (criticalExponent G.generators G.positive 3)
  rw [planeSlice_top_empty,corners_empty] at h
  have hz : Nat.card (∅ : Set Point)=0 := by simp
  rw [hz,zero_add,←corners_card_eq_slice_sum G] at h
  exact h.symm

/-- The actual minimal three-variable staircase generators are at most twice
its actual outer corners, plus one. No genericity or size bound is imposed. -/
theorem staircaseGeneratorNumber_le_twice_corners_add_one :
    staircaseGeneratorNumber G ≤ 2 * Nat.card (staircaseCorners G) + 1 := by
  have hg := Finset.sum_le_sum (s := Finset.range (criticalExponent G.generators G.positive 3))
    (fun z hz => generators_le_lost_add_new (planeSlice_finite G z)
      (planeSlice_finite G (z+1)) (planeSlice_lower G (z+1)))
  rw [Finset.sum_add_distrib] at hg
  have ht := corners_card_eq_slice_sum G
  have hbalance := corners_card_eq_base_add_new G
  have hmu := generatorNumber_eq_slice_sum G
  have hbase := boundary_card_eq (planeSlice_finite G 0) (planeSlice_lower G 0)
  omega

/-- The actual outer corners are controlled by all minimal generators and
by the generators using all three variables. The terminal empty slice gives
the sharp constant two. -/
theorem corners_add_two_le_staircaseGeneratorNumber_add_fullSupport :
    Nat.card (staircaseCorners G) + 2 ≤
      staircaseGeneratorNumber G + fullSupportGeneratorNumber G := by
  obtain ⟨m,hm⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt (criticalExponent_spec G.generators G.positive 3).1)
  change criticalExponent G.generators G.positive 3=m+1 at hm
  have hu := Finset.sum_le_sum (s := Finset.range m) (fun z hz =>
    new_le_generators_add_interior (planeSlice_finite G z) (planeSlice_lower G z)
      (planeSlice_lower G (z+1)) (planeSlice_antitone G (Nat.le_succ z)))
  rw [Finset.sum_add_distrib] at hu
  have hlast : planeSlice G (m+1)=∅ := by
    rw [←hm]
    exact planeSlice_top_empty G
  have hun : Nat.card (NewCorners (planeSlice G m) (planeSlice G (m+1)))=0 := by
    simp [hlast]
  have hgn : Nat.card (Generators (planeSlice G m) (planeSlice G (m+1)))=1 := by
    rw [hlast,generators_empty (planeSlice_zero_mem G (by omega))]
    simp
  have hbalance := corners_card_eq_base_add_new G
  have hmu := generatorNumber_eq_slice_sum G
  have hr := fullSupport_eq_slice_sum G
  have hbase := boundary_card_eq (planeSlice_finite G 0) (planeSlice_lower G 0)
  rw [hm,Finset.sum_range_succ,hun] at hbalance
  rw [hm,Finset.sum_range_succ,hgn] at hmu
  rw [hm,Finset.sum_range_succ] at hr
  omega

end FourGeneratedSemigroups
