import Fan.ConfigurationInvariant

namespace Fan

theorem configurationBottom_le {n : ℕ} (p : Configuration n) : configurationBottom n ≤ p := by
  apply (configurationOrderIso n).symm.le_iff_le.mp
  change (configurationOrderIso n).symm (configurationOrderIso n (bottomFlat n)) ≤ _
  rw [OrderIso.symm_apply_apply]
  exact Set.empty_subset _

theorem configuration_le_top {n : ℕ} (p : Configuration n) : p ≤ configurationTop n := by
  apply (configurationOrderIso n).symm.le_iff_le.mp
  change _ ≤ (configurationOrderIso n).symm (configurationOrderIso n (topFlat n))
  rw [OrderIso.symm_apply_apply]
  exact ((configurationOrderIso n).symm p).property.1

noncomputable instance (n : ℕ) : OrderBot (Configuration n) where
  bot := configurationBottom n
  bot_le := configurationBottom_le
noncomputable instance (n : ℕ) : OrderTop (Configuration n) where
  top := configurationTop n
  le_top := configuration_le_top

@[simp] theorem configuration_bot_val (n : ℕ) : (⊥ : Configuration n).val=(∅,∅) := by
  change readPair (∅ : Set (Sym2 (Vertex n)))=(∅,∅)
  classical
  simp [readPair]

@[simp] theorem configuration_bot_rank (n : ℕ) : configurationRank (⊥ : Configuration n)=0 :=
  configurationBottom_rank n
@[simp] theorem configuration_top_rank (n : ℕ) : configurationRank (⊤ : Configuration n)=n :=
  configurationTop_rank n

noncomputable def Q (n : ℕ) : Polynomial ℤ :=
  MatroidInverseZ.inverseKL configurationRank (⊥ : Configuration n) ⊤

noncomputable def lowerQ {n : ℕ} (p : Configuration n) : Polynomial ℤ :=
  MatroidInverseZ.inverseKL configurationRank (⊥ : Configuration n) p

noncomputable def lowerEmbedding {n : ℕ} (p : Configuration n) : Set.Iic p ↪o Configuration n where
  toFun := Subtype.val
  inj' := Subtype.val_injective
  map_rel_iff' := Iff.rfl

theorem lowerEmbedding_fills {n : ℕ} (p : Configuration n) :
    ∀ a b y, lowerEmbedding p a ≤ y → y ≤ lowerEmbedding p b →
      ∃ x, lowerEmbedding p x=y := by
  intro _ b y _ hy
  exact ⟨⟨y,hy.trans b.property⟩,rfl⟩

theorem lower_inverseKL {n : ℕ} (p : Configuration n) (a b : Set.Iic p) :
    MatroidInverseZ.inverseKL (fun x : Set.Iic p => configurationRank x.val) a b =
      MatroidInverseZ.inverseKL configurationRank a.val b.val := by
  classical
  symm
  exact MatroidInverseZ.inverseKL_interval_transport (lowerEmbedding p)
    (lowerEmbedding_fills p) _ _ (fun _ _ => rfl) a b

end Fan
