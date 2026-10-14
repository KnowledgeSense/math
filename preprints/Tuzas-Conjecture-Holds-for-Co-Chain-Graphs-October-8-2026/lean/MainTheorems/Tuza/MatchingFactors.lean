import MainTheorems.Tuza.ExtendedMatching
import MainTheorems.Tuza.FanTriangles

namespace ResearchMain.Tuza

structure MatchingFactors (Q F : Type*) where
  graph : F → SimpleGraph Q
  matching : ∀ i x y z, (graph i).Adj x y → (graph i).Adj x z → y = z
  separated : ∀ i j x y, (graph i).Adj x y → (graph j).Adj x y → i = j

variable {K : Type*} [AddCommGroup K]

def reflectionFactors (hd : Function.Injective (fun x : K => x + x)) :
    MatchingFactors K K where
  graph := reflectionGraph
  matching := fun _ _ _ _ => reflection_adj_unique
  separated := fun _ _ _ _ => reflection_factor_unique hd

def extendedFactors (hd : Function.Injective (fun x : K => x + x)) :
    MatchingFactors (Option K) K where
  graph := extendedReflectionGraph
  matching := fun _ _ _ _ => extended_adj_unique
  separated := fun _ _ _ _ => extended_factor_unique hd

namespace MatchingFactors

variable {C Q F : Type*} [DecidableEq C] [DecidableEq Q]

def TriangleIndex (M : MatchingFactors Q F) (f : C ↪ F) :=
  {p : C × Sym2 Q // p.2 ∈ (M.graph (f p.1)).edgeSet}

noncomputable def packingFamily (M : MatchingFactors Q F) (f : C ↪ F) :
    PackingFamily (fanGraph C Q) (M.TriangleIndex f) where
  triangle i := fanTriangle i.val.1 i.val.2
  clique i := fanTriangle_clique i.val.1
    ((M.graph (f i.val.1)).not_isDiag_of_mem_edgeSet i.property)
  disjoint i j hij := fanTriangle_disjoint M.graph f M.matching M.separated
    i.property j.property (fun h => hij (Subtype.ext h))

variable [Fintype C] [Fintype Q]

noncomputable instance (M : MatchingFactors Q F) (f : C ↪ F) :
    Fintype (M.TriangleIndex f) := by
  classical
  unfold TriangleIndex
  exact Fintype.ofFinite _

omit [DecidableEq C] [DecidableEq Q] in
theorem index_card (M : MatchingFactors Q F) (f : C ↪ F) (k : ℕ)
    (hk : ∀ i, Nat.card (M.graph (f i)).edgeSet = k) :
    Fintype.card (M.TriangleIndex f) = Fintype.card C * k := by
  classical
  let e : M.TriangleIndex f ≃ Σ c : C, (M.graph (f c)).edgeSet :=
    Equiv.subtypeProdEquivSigmaSubtype (fun c z => z ∈ (M.graph (f c)).edgeSet)
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp_rw [← Nat.card_eq_fintype_card, hk]
  simp

theorem packing_lower_bound (M : MatchingFactors Q F) (f : C ↪ F) (k : ℕ)
    (hk : ∀ i, Nat.card (M.graph (f i)).edgeSet = k) :
    Fintype.card C * k ≤ packingNumber (fanGraph C Q) := by
  rw [← M.index_card f k hk]
  exact (M.packingFamily f).number_bound

end MatchingFactors

end ResearchMain.Tuza
