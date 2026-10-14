import Fan.ConfigurationBounds
import ThagomizerTuran.BooleanEvaluation

namespace Fan
open scoped Classical

noncomputable def spokelessEmbedding {n : ℕ} (p : Configuration n) :
    Finset {j : Fin n // j∈p.val.2} ↪o Configuration n :=
  OrderEmbedding.ofMapLEIff (fun T => ⟨(∅,T.map (Function.Embedding.subtype _)),by
    constructor
    · intro j hj
      exact p.property.1 j (Finset.property_of_mem_map_subtype T hj)
    · intro i j _
      simp only [Finset.notMem_empty,iff_self,implies_true,false_implies,and_self]⟩)
    (fun S T => by
      change ((∅ : Finset (Fin n))⊆∅ ∧ S.map (Function.Embedding.subtype _) ⊆
        T.map (Function.Embedding.subtype _)) ↔ S⊆T
      simp only [Finset.empty_subset,true_and,Finset.map_subset_map])

theorem spokelessEmbedding_fills {n : ℕ} (p : Configuration n) :
    ∀ a b y, spokelessEmbedding p a ≤ y → y ≤ spokelessEmbedding p b →
      ∃ x, spokelessEmbedding p x=y := by
  intro _ b y _ hy
  have hs : y.val.1=∅ := Finset.subset_empty.mp hy.1
  have hr : ∀ j∈y.val.2, j∈p.val.2 := fun _ hj =>
    Finset.property_of_mem_map_subtype b (hy.2 hj)
  refine ⟨y.val.2.subtype (·∈p.val.2),?_⟩
  apply Subtype.ext
  apply Prod.ext
  · exact hs.symm
  · exact Finset.subtype_map_of_mem hr

theorem spokelessEmbedding_rank {n : ℕ} (p : Configuration n)
    (T : Finset {j : Fin n // j∈p.val.2}) :
    configurationRank (spokelessEmbedding p T)=T.card := by
  change (∅ ∪ T.map (Function.Embedding.subtype _)).card=T.card
  rw [Finset.empty_union,Finset.card_map]

theorem spokelessEmbedding_bot {n : ℕ} (p : Configuration n) : spokelessEmbedding p ∅=⊥ := by
  apply Subtype.ext
  rw [configuration_bot_val]
  change (∅,Finset.map _ ∅)=(∅,∅)
  rw [Finset.map_empty]

theorem spokelessEmbedding_top {n : ℕ} (p : Configuration n) (hp : p.val.1=∅) :
    spokelessEmbedding p p.val.2.attach=p := by
  apply Subtype.ext
  apply Prod.ext
  · exact hp.symm
  · exact Finset.attach_map_val

theorem lowerQ_spokeless {n : ℕ} (p : Configuration n) (hp : p.val.1=∅) : lowerQ p=1 := by
  classical
  have h := MatroidInverseZ.inverseKL_interval_transport (spokelessEmbedding p)
    (spokelessEmbedding_fills p) Finset.card configurationRank
    (fun a b => by rw [spokelessEmbedding_rank,spokelessEmbedding_rank]) ∅ p.val.2.attach
  rw [spokelessEmbedding_bot,spokelessEmbedding_top p hp] at h
  change lowerQ p=_ at h
  rw [h,MatroidInverseZ.boolean_inverseKL _ _ (Finset.empty_subset _)]

theorem lower_mu_spokeless {n : ℕ} (p : Configuration n) (hp : p.val.1=∅) :
    IncidenceAlgebra.mu ℤ (⊥ : Configuration n) p=(-1 : ℤ)^p.val.2.card := by
  classical
  have h := MatroidInverseZ.mu_interval_transport (spokelessEmbedding p)
    (spokelessEmbedding_fills p) ∅ p.val.2.attach
  rw [spokelessEmbedding_bot,spokelessEmbedding_top p hp] at h
  rw [h,MatroidInverseZ.boolean_mu _ _ (Finset.empty_subset _)]
  simp only [Finset.card_empty,Nat.sub_zero,Finset.card_attach]

end Fan
