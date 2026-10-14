import Fan.PendantIntervals

namespace Fan

noncomputable def pendantEmbedding {n : ℕ} (p : Configuration (n+1))
    (hp : Fin.last n∉p.val.1) : (Set.Iic p × Bool) ↪o Configuration (n+2) :=
  OrderEmbedding.ofMapLEIff (fun x => appendConfiguration x.1.val false x.2 (by
    cases h : x.2
    · exact allowed_false_false _
    · apply (allowed_false_true _).mpr
      intro hs
      exact hp (x.1.property.1 hs))) (fun x y => by
    change appendPair x.1.val.val false x.2 ≤ appendPair y.1.val.val false y.2 ↔ _
    rw [appendPair_le_iff]
    simp only [le_refl,true_and]
    rfl)

theorem pendantEmbedding_fills {n : ℕ} (p : Configuration (n+1))
    (hp : Fin.last n∉p.val.1) :
    ∀ a b z, pendantEmbedding p hp a ≤ z → z ≤ pendantEmbedding p hp b →
      ∃ x, pendantEmbedding p hp x=z := by
  intro _ b z _ hzb
  obtain ⟨⟨q,⟨⟨d,c⟩,ha⟩⟩,rfl⟩ := (extensionEquiv n).surjective z
  change appendPair q.val d c ≤ appendPair b.1.val.val false b.2 at hzb
  obtain ⟨hqb,hd,_⟩ := (appendPair_le_iff _ _ _ _ _ _).mp hzb
  have hd' : d=false := by
    cases d
    · rfl
    · exact False.elim ((by decide : ¬((true : Bool)≤false)) hd)
  subst d
  exact ⟨(⟨q,hqb.trans b.1.property⟩,c),rfl⟩

theorem pendantEmbedding_rank {n : ℕ} (p : Configuration (n+1))
    (hp : Fin.last n∉p.val.1) (x : Set.Iic p × Bool) :
    configurationRank (pendantEmbedding p hp x)=configurationRank x.1.val+bitRank x.2 := by
  change (appendSet x.1.val.val.1 false ∪ appendSet x.1.val.val.2 x.2).card=_
  rw [appendSet_union,appendSet_card]
  simp only [Bool.false_or,bitRank,configurationRank]

theorem pendantEmbedding_bot {n : ℕ} (p : Configuration (n+1))
    (hp : Fin.last n∉p.val.1) : pendantEmbedding p hp (⊥,false)=⊥ := by
  apply Subtype.ext
  change appendPair (⊥ : Configuration (n+1)).val false false=(⊥ : Configuration (n+2)).val
  rw [configuration_bot_val,configuration_bot_val]
  simp [appendPair,appendSet,joinSets,bitSet]

/-- A selected rim with no new spoke is an actual coloop in the restriction.
The product interval, including its rank addition, is constructed above. -/
theorem lowerQ_append_pendant {n : ℕ} (p : Configuration (n+1))
    (hp : Fin.last n∉p.val.1) :
    lowerQ (appendConfiguration p false true ((allowed_false_true p.val).mpr hp))=lowerQ p := by
  classical
  have h := MatroidInverseZ.inverseKL_interval_transport (pendantEmbedding p hp)
    (pendantEmbedding_fills p hp)
    (fun x : Set.Iic p × Bool => configurationRank x.1.val+bitRank x.2)
    configurationRank
    (fun a b => by rw [pendantEmbedding_rank,pendantEmbedding_rank])
    (⊥,false) (⊤,true)
  rw [pendantEmbedding_bot] at h
  change lowerQ (appendConfiguration p false true ((allowed_false_true p.val).mpr hp))=_ at h
  rw [h,MatroidInverseZ.inverseKL_product
    (fun x : Set.Iic p => configurationRank x.val) bitRank
    (fun _ _ hxy => (configurationRank_strictMono (n+1)).monotone hxy)
    bitRank_mono (⊥,false) (⊤,true) ⟨bot_le,Bool.false_le _⟩]
  rw [bit_inverseKL,mul_one,lower_inverseKL]
  rfl

end Fan
