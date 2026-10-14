import Fan.ComponentRepresentatives
import Fan.GraphicRanks
import ThagomizerTuran.IntervalTransport

namespace Fan

noncomputable instance (n : ℕ) : Fintype (Configuration n) := Fintype.ofFinite _
noncomputable instance (n : ℕ) : DecidableEq (Configuration n) := Classical.decEq _
noncomputable instance (n : ℕ) : LocallyFiniteOrder (Configuration n) := by
  classical
  exact Fintype.toLocallyFiniteOrder

def configurationRank {n : ℕ} (p : Configuration n) : ℕ := (p.val.1 ∪ p.val.2).card

theorem configuration_rank {n : ℕ} (p : Configuration n) :
    graphicRank ((configurationOrderIso n).symm p).val=configurationRank p := by
  change graphicRank (selectedGraph p.val).edgeSet=configurationRank p
  rw [graphicRank_readPair p.property.isGraphicFlat,p.property.readPair_selected]
  rfl

theorem configurationRank_strictMono (n : ℕ) : StrictMono (@configurationRank n) := by
  intro p q hpq
  rw [← configuration_rank p,← configuration_rank q]
  exact graphicRank_strictMono ((configurationOrderIso n).symm.strictMono hpq)

noncomputable def configurationBottom (n : ℕ) : Configuration n :=
  configurationOrderIso n (bottomFlat n)
noncomputable def configurationTop (n : ℕ) : Configuration n :=
  configurationOrderIso n (topFlat n)

theorem configurationBottom_rank (n : ℕ) : configurationRank (configurationBottom n)=0 := by
  rw [← configuration_rank]
  change graphicRank ((configurationOrderIso n).symm (configurationOrderIso n (bottomFlat n))).val=0
  rw [OrderIso.symm_apply_apply,graphicRank_bottom]

theorem configurationTop_rank (n : ℕ) : configurationRank (configurationTop n)=n := by
  rw [← configuration_rank]
  change graphicRank ((configurationOrderIso n).symm (configurationOrderIso n (topFlat n))).val=n
  rw [OrderIso.symm_apply_apply]
  exact graph_rank n

/-- Every subsequent finite configuration evaluation is transported from the
actual graph-flat inverse-Z invariant. -/
theorem inverseZ_configuration (n : ℕ) : inverseZ n =
    MatroidInverseZ.inverseZ configurationRank (configurationBottom n) (configurationTop n) := by
  classical
  have h := MatroidInverseZ.inverseZ_interval_transport (configurationOrderIso n).symm.toOrderEmbedding
    (fun _ _ y _ _ => ⟨configurationOrderIso n y,(configurationOrderIso n).symm_apply_apply y⟩)
    configurationRank (fun F : GraphicFlat n => graphicRank F.val)
    (fun a b => by
      change graphicRank ((configurationOrderIso n).symm b).val-
        graphicRank ((configurationOrderIso n).symm a).val = _
      rw [configuration_rank a,configuration_rank b])
    (configurationBottom n) (configurationTop n)
  change MatroidInverseZ.inverseZ (fun F : GraphicFlat n => graphicRank F.val)
    ((configurationOrderIso n).symm (configurationOrderIso n (bottomFlat n)))
    ((configurationOrderIso n).symm (configurationOrderIso n (topFlat n))) = _ at h
  rw [OrderIso.symm_apply_apply,OrderIso.symm_apply_apply] at h
  exact h

end Fan
