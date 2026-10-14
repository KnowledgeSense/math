import MainTheorems.DominationRoots.ExtensionPolynomial

namespace ResearchMain.DominationRoots

open Classical Polynomial ResearchMain.Domination

variable {V U : Type} [Fintype V] [Fintype U]

omit [Fintype V] [Fintype U] in
theorem dominates_iso_iff {G : SimpleGraph V} {H : SimpleGraph U} (e : G ≃g H) (S : Finset V) :
    Dominates G S ↔ Dominates H (S.map e.toEquiv.toEmbedding) := by
  constructor
  · intro hdom v
    obtain ⟨w, rfl⟩ := e.surjective v
    obtain ⟨u, hu, he | hadj⟩ := hdom w
    · exact ⟨e u, Finset.mem_map.mpr ⟨u, hu, rfl⟩, Or.inl (congrArg e he)⟩
    · exact ⟨e u, Finset.mem_map.mpr ⟨u, hu, rfl⟩, Or.inr (e.map_adj_iff.mpr hadj)⟩
  · intro hdom v
    obtain ⟨u, hu, he⟩ := hdom (e v)
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hu
    refine ⟨w, hw, ?_⟩
    rcases he with he | hadj
    · exact Or.inl (e.injective he)
    · exact Or.inr (e.map_adj_iff.mp hadj)

theorem dominationPolynomial_iso {G : SimpleGraph V} {H : SimpleGraph U} (e : G ≃g H) :
    dominationPolynomial G = dominationPolynomial H := by
  have hsum :
      (∑ S : Finset V, if Dominates G S then (X : ℤ[X]) ^ S.card else 0) =
      ∑ T : Finset U, if Dominates H T then (X : ℤ[X]) ^ T.card else 0 := by
    apply Fintype.sum_equiv e.toEquiv.finsetCongr
    intro S
    simp only [Equiv.finsetCongr_apply, Finset.card_map]
    rw [dominates_iso_iff e]
  simpa [dominationPolynomial, allDominatingSets, Finset.sum_filter] using hsum

def HasLeafPresentation (G : SimpleGraph V) : Prop :=
  ∃ (C I : Type) (_ : Fintype C) (_ : Fintype I) (W : C → Type)
    (hW : ∀ c, Fintype (W c)) (H : SimpleGraph C),
    (∀ c, @Fintype.card (W c) (hW c) = 1 ∨ @Fintype.card (W c) (hW c) = 2) ∧
      Nonempty (leafExtension H I W ≃g G)

theorem realRooted_domination_iff_leaf_presentation (G : SimpleGraph V) :
    RealRooted (dominationPolynomial G) ↔ HasLeafPresentation G := by
  constructor
  · intro hr
    have hG := realRooted_oneTwoLeafGraph hr
    refine ⟨CoreVertex G, ↥(isolatedVertices G), inferInstance, inferInstance,
      (fun v : CoreVertex G => ↥(attachedLeaves G v.val)),
      (fun _ => inferInstance), coreGraph G, ?_, ⟨supportGraphIso G⟩⟩
    intro v
    simpa only [Fintype.card_coe] using hG v
  · rintro ⟨C, I, hC, hI, W, hW, H, hs, ⟨e⟩⟩
    let _ : Fintype C := hC
    let _ : Fintype I := hI
    let _ : ∀ c, Fintype (W c) := hW
    rw [← dominationPolynomial_iso e]
    exact leafExtension_realRooted H hs

end ResearchMain.DominationRoots
