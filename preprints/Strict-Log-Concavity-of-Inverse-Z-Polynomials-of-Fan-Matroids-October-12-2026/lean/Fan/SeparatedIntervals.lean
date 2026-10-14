import Fan.SeparatedConfigurations
import Fan.ConfigurationBounds
import Fan.ProductInvariants

namespace Fan

noncomputable def joinedConfiguration {m n : ℕ} (p : Configuration m) (q : Configuration n)
    (hc : Compatible p.val q.val) : Configuration (m+n) :=
  ⟨joinPair p.val q.val,valid_joinPair p.property q.property hc⟩

noncomputable def separatedLowerEmbedding {m n : ℕ} (p : Configuration m) (q : Configuration n)
    (hc : Compatible p.val q.val) : (Set.Iic p × Set.Iic q) ↪o Configuration (m+n) :=
  OrderEmbedding.ofMapLEIff
    (fun x => joinedConfiguration x.1.val x.2.val
      (compatible_mono hc x.1.property x.2.property))
    (fun x y => by
      change joinPair x.1.val.val x.2.val.val ≤ joinPair y.1.val.val y.2.val.val ↔ _
      exact joinPair_le_iff _ _ _ _)

theorem split_bounds {m n : ℕ} (p : Configuration m) (q : Configuration n)
    (z : Configuration (m+n)) (hz : z.val ≤ joinPair p.val q.val) :
    leftPair z.val ≤ p.val ∧ rightPair z.val ≤ q.val := by
  rw [← joinPair_left_right z.val,joinPair_le_iff] at hz
  exact hz

theorem split_gap {m n : ℕ} (p : Configuration m) (q : Configuration n)
    (z : Configuration (m+n)) (hz : z.val ≤ joinPair p.val q.val) :
    ∀ j : Fin n, j.val=0 → j.natAdd m∉z.val.2 := by
  intro j hj hm
  have hb := split_bounds p q z hz
  have hjq := hb.2.2 ((mem_rightSet z.val.2 j).mpr hm)
  have := q.property.1 j hjq
  omega

theorem separatedLowerEmbedding_fills {m n : ℕ} (p : Configuration m) (q : Configuration n)
    (hc : Compatible p.val q.val) :
    ∀ a b z, separatedLowerEmbedding p q hc a ≤ z → z ≤ separatedLowerEmbedding p q hc b →
      ∃ x, separatedLowerEmbedding p q hc x=z := by
  intro _ b z _ hzb
  have hzb' : z.val ≤ joinPair b.1.val.val b.2.val.val := hzb
  have hz : z.val ≤ joinPair p.val q.val := hzb'.trans
    ((joinPair_le_iff _ _ _ _).mpr ⟨b.1.property,b.2.property⟩)
  have hb := split_bounds p q z hz
  let l : Configuration m := ⟨leftPair z.val,z.property.left_valid⟩
  let r : Configuration n := ⟨rightPair z.val,z.property.right_valid (split_gap p q z hz)⟩
  refine ⟨(⟨l,hb.1⟩,⟨r,hb.2⟩),?_⟩
  apply Subtype.ext
  exact joinPair_left_right z.val

theorem separatedLowerEmbedding_rank {m n : ℕ} (p : Configuration m) (q : Configuration n)
    (hc : Compatible p.val q.val) (x : Set.Iic p × Set.Iic q) :
    configurationRank (separatedLowerEmbedding p q hc x)=
      configurationRank x.1.val+configurationRank x.2.val :=
  joinPair_rank x.1.val x.2.val (compatible_mono hc x.1.property x.2.property)

theorem separatedLowerEmbedding_bot {m n : ℕ} (p : Configuration m) (q : Configuration n)
    (hc : Compatible p.val q.val) : separatedLowerEmbedding p q hc (⊥,⊥)=⊥ := by
  apply Subtype.ext
  change joinPair (⊥ : Configuration m).val (⊥ : Configuration n).val=(⊥ : Configuration (m+n)).val
  rw [configuration_bot_val,configuration_bot_val,configuration_bot_val]
  simp [joinPair,joinSets]

theorem lowerQ_join {m n : ℕ} (p : Configuration m) (q : Configuration n)
    (hc : Compatible p.val q.val) :
    lowerQ (joinedConfiguration p q hc)=lowerQ p*lowerQ q := by
  classical
  have h := MatroidInverseZ.inverseKL_interval_transport (separatedLowerEmbedding p q hc)
    (separatedLowerEmbedding_fills p q hc)
    (fun x : Set.Iic p × Set.Iic q => configurationRank x.1.val+configurationRank x.2.val)
    configurationRank
    (fun a b => by rw [separatedLowerEmbedding_rank,separatedLowerEmbedding_rank])
    (⊥,⊥) (⊤,⊤)
  rw [separatedLowerEmbedding_bot] at h
  change lowerQ (joinedConfiguration p q hc)=_ at h
  rw [h,MatroidInverseZ.inverseKL_product
    (fun x : Set.Iic p => configurationRank x.val)
    (fun x : Set.Iic q => configurationRank x.val)
    (fun _ _ hxy => (configurationRank_strictMono m).monotone hxy)
    (fun _ _ hxy => (configurationRank_strictMono n).monotone hxy)
    (⊥,⊥) (⊤,⊤) (by exact bot_le)]
  rw [lower_inverseKL,lower_inverseKL]
  rfl

end Fan
