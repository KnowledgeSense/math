import EdgeColoringMixing.SideTransport
import EdgeColoringMixing.ColorPairCounting
import EdgeColoringMixing.ObservedMarginal

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace EdgeColoringMixing.ObservedCounting
open Finset SimpleGraph RootedCounting TreeGeometry
attribute [local instance] Classical.propDecidable
universe u
variable {V : Type u} {G : SimpleGraph V}

/-- Inclusion of a genuine side edge into the original edge set. -/
def sideEdge (x y r : V) : (sideGraph (G := G) x y r).edgeSet → G.edgeSet :=
  (sideCopy x y r).toLineGraphEmbedding

theorem sideEdge_injective (x y r : V) : Function.Injective (sideEdge (G := G) x y r) :=
  (sideCopy x y r).toLineGraphEmbedding.injective

theorem sideEdge_mem_iff (x y r : V) (e : (sideGraph (G := G) x y r).edgeSet) (v : V) :
    v ∈ (sideEdge x y r e).1 ↔ ∃ w : side (G := G) x y r, w ∈ e.1 ∧ w.1 = v := by
  rcases e with ⟨e,he⟩
  induction e using Sym2.ind with
  | h a b =>
    change v ∈ s(a.1,b.1) ↔ ∃ w, w ∈ s(a,b) ∧ w.1 = v
    simp only [Sym2.mem_iff]
    constructor
    · rintro (h | h)
      · exact ⟨a, Or.inl rfl, h.symm⟩
      · exact ⟨b, Or.inr rfl, h.symm⟩
    · rintro ⟨w, (rfl | rfl), rfl⟩ <;> simp

theorem sideEdge_ne_observed (x y r : V) (hxy : G.Adj x y)
    (e : (sideGraph (G := G) x y r).edgeSet) : sideEdge x y r e ≠ ⟨s(x,y),hxy⟩ := by
  rcases e with ⟨e,he⟩
  induction e using Sym2.ind with
  | h a b =>
    intro h
    have hv := congrArg Subtype.val h
    exact (deleteEdges_adj.mp he).2 (by exact Set.mem_singleton_iff.mpr hv)

theorem sideEdge_adj_iff (x y r : V) (e f : (sideGraph (G := G) x y r).edgeSet) :
    G.lineGraph.Adj (sideEdge x y r e) (sideEdge x y r f) ↔
      (sideGraph (G := G) x y r).lineGraph.Adj e f :=
  (sideCopy x y r).toLineGraphEmbedding.map_rel_iff

theorem sides_edge_not_adj (hG : G.IsTree) {x y : V} (hxy : G.Adj x y)
    (e : (sideGraph (G := G) x y x).edgeSet)
    (f : (sideGraph (G := G) x y y).edgeSet) :
    ¬ G.lineGraph.Adj (sideEdge x y x e) (sideEdge x y y f) := by
  intro h
  obtain ⟨_,v,he,hf⟩ := lineGraph_adj_iff_exists.mp h
  obtain ⟨a,_,ha⟩ := (sideEdge_mem_iff x y x e v).mp he
  obtain ⟨b,_,hb⟩ := (sideEdge_mem_iff x y y f v).mp hf
  have hx : (cutGraph (G := G) x y).Reachable x a.1 :=
    (ConnectedComponent.exact a.2).symm
  have hy : (cutGraph (G := G) x y).Reachable b.1 y := ConnectedComponent.exact b.2
  exact cut_not_reachable hG hxy (hx.trans (hb.trans ha.symm ▸ hy))

/-- Every original edge is the observed edge or an edge of exactly one endpoint side. -/
theorem edge_observed_or_side (hG : G.IsTree) {x y : V} (hxy : G.Adj x y) (e : G.edgeSet) :
    e = ⟨s(x,y),hxy⟩ ∨
      (∃ a, sideEdge x y x a = e) ∨ (∃ b, sideEdge x y y b = e) := by
  rcases e with ⟨e,he⟩
  induction e using Sym2.ind with
  | h a b =>
    by_cases hab : s(a,b) = s(x,y)
    · exact Or.inl (Subtype.ext hab)
    · have hd : (cutGraph (G := G) x y).Adj a b :=
        deleteEdges_adj.mpr ⟨he, by simpa using hab⟩
      have build (r : V) (hr : (cutGraph (G := G) x y).Reachable r a) :
          ∃ f : (sideGraph (G := G) x y r).edgeSet,
            sideEdge x y r f = ⟨s(a,b),he⟩ := by
        let a' : side (G := G) x y r := ⟨a, ConnectedComponent.sound hr.symm⟩
        let b' : side (G := G) x y r := ⟨b, ConnectedComponent.sound (hr.trans hd.reachable).symm⟩
        exact ⟨⟨s(a',b'),hd⟩, rfl⟩
      rcases cut_reachable_or hG.connected x y a with h | h
      · exact Or.inr (Or.inl (build x h))
      · exact Or.inr (Or.inr (build y h))

theorem sides_edge_ne (hG : G.IsTree) {x y : V} (hxy : G.Adj x y)
    (e : (sideGraph (G := G) x y x).edgeSet)
    (f : (sideGraph (G := G) x y y).edgeSet) :
    sideEdge x y x e ≠ sideEdge x y y f := by
  intro h
  let a := e.1.out.1
  have ha : a.1 ∈ (sideEdge x y x e).1 :=
    (sideEdge_mem_iff x y x e a.1).mpr ⟨a, Sym2.out_fst_mem _, rfl⟩
  rw [h] at ha
  obtain ⟨b,_,hb⟩ := (sideEdge_mem_iff x y y f a.1).mp ha
  have hx : (cutGraph (G := G) x y).Reachable x a.1 :=
    (ConnectedComponent.exact a.2).symm
  have hy : (cutGraph (G := G) x y).Reachable b.1 y := ConnectedComponent.exact b.2
  exact cut_not_reachable hG hxy (hx.trans (hb ▸ hy))

/-- Canonical splitting into the observed edge and the two genuine side edge sets. -/
noncomputable def edgeSplit (hG : G.IsTree) {x y : V} (hxy : G.Adj x y) :
    Unit ⊕ ((sideGraph (G := G) x y x).edgeSet ⊕ (sideGraph (G := G) x y y).edgeSet) ≃
      G.edgeSet := by
  let f : Unit ⊕ ((sideGraph (G := G) x y x).edgeSet ⊕
      (sideGraph (G := G) x y y).edgeSet) → G.edgeSet :=
    Sum.elim (fun _ => ⟨s(x,y),hxy⟩) (Sum.elim (sideEdge x y x) (sideEdge x y y))
  apply Equiv.ofBijective f
  constructor
  · intro a b h
    rcases a with a | (a | a) <;> rcases b with b | (b | b)
    · congr
    · exact False.elim (sideEdge_ne_observed x y x hxy b h.symm)
    · exact False.elim (sideEdge_ne_observed x y y hxy b h.symm)
    · exact False.elim (sideEdge_ne_observed x y x hxy a h)
    · exact congrArg (Sum.inr ∘ Sum.inl) (sideEdge_injective x y x h)
    · exact False.elim (sides_edge_ne hG hxy a b h)
    · exact False.elim (sideEdge_ne_observed x y y hxy a h)
    · exact False.elim (sides_edge_ne hG hxy b a h.symm)
    · exact congrArg (Sum.inr ∘ Sum.inr) (sideEdge_injective x y y h)
  · intro e
    rcases edge_observed_or_side hG hxy e with h | ⟨a,h⟩ | ⟨b,h⟩
    · exact ⟨Sum.inl (),h.symm⟩
    · exact ⟨Sum.inr (Sum.inl a),h⟩
    · exact ⟨Sum.inr (Sum.inr b),h⟩

@[simp] theorem edgeSplit_observed (hG : G.IsTree) {x y : V} (hxy : G.Adj x y) :
    edgeSplit hG hxy (.inl ()) = ⟨s(x,y),hxy⟩ := rfl

@[simp] theorem edgeSplit_left (hG : G.IsTree) {x y : V} (hxy : G.Adj x y)
    (e : (sideGraph (G := G) x y x).edgeSet) :
    edgeSplit hG hxy (.inr (.inl e)) = sideEdge x y x e := rfl

@[simp] theorem edgeSplit_right (hG : G.IsTree) {x y : V} (hxy : G.Adj x y)
    (e : (sideGraph (G := G) x y y).edgeSet) :
    edgeSplit hG hxy (.inr (.inr e)) = sideEdge x y y e := rfl

theorem observed_side_adj_iff {x y r z : V} (hxy : G.Adj x y)
    (he : s(r,z) = s(x,y)) (hn : ¬ (cutGraph (G := G) x y).Reachable r z)
    (e : (sideGraph (G := G) x y r).edgeSet) :
    G.lineGraph.Adj ⟨s(x,y),hxy⟩ (sideEdge x y r e) ↔ sideRoot x y r ∈ e.1 := by
  rw [lineGraph_adj_iff_exists]
  constructor
  · rintro ⟨_,v,hv,hev⟩
    change v ∈ s(x,y) at hv
    rw [← he] at hv
    rcases Sym2.mem_iff.mp hv with h | h
    · subst v
      obtain ⟨w,hw,hwr⟩ := (sideEdge_mem_iff x y r e r).mp hev
      have hwroot : w = sideRoot x y r := Subtype.ext hwr
      exact hwroot ▸ hw
    · subst v
      obtain ⟨w,_,hwz⟩ := (sideEdge_mem_iff x y r e z).mp hev
      exact False.elim (hn (hwz ▸ (ConnectedComponent.exact w.2).symm))
  · intro h
    refine ⟨(sideEdge_ne_observed x y r hxy e).symm, r, ?_, ?_⟩
    · change r ∈ s(x,y)
      rw [← he]; simp
    · exact (sideEdge_mem_iff x y r e r).mpr ⟨sideRoot x y r,h,rfl⟩

def restrictSide {q : ℕ} {F : V → Finset (Fin q)} (x y r : V)
    (σ : Coloring G q F) : Coloring (sideGraph (G := G) x y r) q (fun v => F v.1) :=
  ⟨fun e => σ.1 (sideEdge x y r e),
    ⟨fun e f h => σ.2.1 _ _ ((sideEdge_adj_iff x y r e f).mpr h),
      fun e v hv => σ.2.2 _ v.1 ((sideEdge_mem_iff x y r e v.1).mpr ⟨v,hv,rfl⟩)⟩⟩

/-- Compatibility of a side coloring with the color placed on the observed edge. -/
def SideCompatible {q : ℕ} (F : V → Finset (Fin q)) (x y r : V) (c : Fin q)
    (σ : Coloring (sideGraph (G := G) x y r) q (fun v => F v.1)) : Prop :=
  c ∉ F r ∧ ∀ e, sideRoot x y r ∈ e.1 → σ.1 e ≠ c

theorem restrictSide_compatible {q : ℕ} {F : V → Finset (Fin q)}
    {x y r z : V} (hxy : G.Adj x y) (he : s(r,z) = s(x,y))
    (hn : ¬ (cutGraph (G := G) x y).Reachable r z) (σ : Coloring G q F) :
    SideCompatible F x y r (σ.1 ⟨s(x,y),hxy⟩) (restrictSide x y r σ) := by
  constructor
  · apply σ.2.2 _ r
    change r ∈ s(x,y)
    rw [← he]; simp
  · intro e he'
    exact σ.2.1 _ _ ((observed_side_adj_iff hxy he hn e).mpr he').symm

noncomputable def glueColor (hG : G.IsTree) {x y : V} (hxy : G.Adj x y)
    {q : ℕ} (c : Fin q)
    (a : (sideGraph (G := G) x y x).edgeSet → Fin q)
    (b : (sideGraph (G := G) x y y).edgeSet → Fin q) : G.edgeSet → Fin q :=
  fun e => Sum.elim (fun _ => c) (Sum.elim a b) ((edgeSplit hG hxy).symm e)

@[simp] theorem glueColor_observed (hG : G.IsTree) {x y : V} (hxy : G.Adj x y)
    {q : ℕ} (c : Fin q) (a b) : glueColor hG hxy c a b ⟨s(x,y),hxy⟩ = c := by
  change Sum.elim _ _ ((edgeSplit hG hxy).symm (edgeSplit hG hxy (.inl ()))) = c
  rw [Equiv.symm_apply_apply]; rfl

@[simp] theorem glueColor_left (hG : G.IsTree) {x y : V} (hxy : G.Adj x y)
    {q : ℕ} (c : Fin q) (a b) (e : (sideGraph (G := G) x y x).edgeSet) :
    glueColor hG hxy c a b (sideEdge x y x e) = a e := by
  change Sum.elim _ _ ((edgeSplit hG hxy).symm (edgeSplit hG hxy (.inr (.inl e)))) = a e
  rw [Equiv.symm_apply_apply]; rfl

@[simp] theorem glueColor_right (hG : G.IsTree) {x y : V} (hxy : G.Adj x y)
    {q : ℕ} (c : Fin q) (a b) (e : (sideGraph (G := G) x y y).edgeSet) :
    glueColor hG hxy c a b (sideEdge x y y e) = b e := by
  change Sum.elim _ _ ((edgeSplit hG hxy).symm (edgeSplit hG hxy (.inr (.inr e)))) = b e
  rw [Equiv.symm_apply_apply]; rfl

theorem glueColor_proper (hG : G.IsTree) {x y : V} (hxy : G.Adj x y)
    {q : ℕ} {F : V → Finset (Fin q)} (c : Fin q)
    (a : Coloring (sideGraph (G := G) x y x) q (fun v => F v.1))
    (b : Coloring (sideGraph (G := G) x y y) q (fun v => F v.1))
    (ha : SideCompatible F x y x c a) (hb : SideCompatible F x y y c b) :
    Proper G q (glueColor hG hxy c a.1 b.1) := by
  have hn := cut_not_reachable hG hxy
  have hn' : ¬ (cutGraph (G := G) x y).Reachable y x := fun h => hn h.symm
  intro e f hef
  rcases edge_observed_or_side hG hxy e with rfl | ⟨e,rfl⟩ | ⟨e,rfl⟩ <;>
    rcases edge_observed_or_side hG hxy f with rfl | ⟨f,rfl⟩ | ⟨f,rfl⟩
  · exact False.elim (G.lineGraph.irrefl hef)
  · simpa only [glueColor_observed, glueColor_left] using
      (ha.2 f ((observed_side_adj_iff hxy rfl hn f).mp hef)).symm
  · simpa only [glueColor_observed, glueColor_right] using
      (hb.2 f ((observed_side_adj_iff hxy (Sym2.eq_swap) hn' f).mp hef)).symm
  · simpa only [glueColor_observed, glueColor_left] using
      ha.2 e ((observed_side_adj_iff hxy rfl hn e).mp hef.symm)
  · simpa only [glueColor_left] using a.2.1 e f ((sideEdge_adj_iff x y x e f).mp hef)
  · exact False.elim (sides_edge_not_adj hG hxy e f hef)
  · simpa only [glueColor_observed, glueColor_right] using
      hb.2 e ((observed_side_adj_iff hxy (Sym2.eq_swap) hn' e).mp hef.symm)
  · exact False.elim (sides_edge_not_adj hG hxy f e hef.symm)
  · simpa only [glueColor_right] using b.2.1 e f ((sideEdge_adj_iff x y y e f).mp hef)

theorem glueColor_lists (hG : G.IsTree) {x y : V} (hxy : G.Adj x y)
    {q : ℕ} {F : V → Finset (Fin q)} (c : Fin q)
    (a : Coloring (sideGraph (G := G) x y x) q (fun v => F v.1))
    (b : Coloring (sideGraph (G := G) x y y) q (fun v => F v.1))
    (ha : SideCompatible F x y x c a) (hb : SideCompatible F x y y c b) :
    ∀ e v, v ∈ e.1 → glueColor hG hxy c a.1 b.1 e ∉ F v := by
  intro e v hv
  rcases edge_observed_or_side hG hxy e with rfl | ⟨e,rfl⟩ | ⟨e,rfl⟩
  · change v ∈ s(x,y) at hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · simpa only [glueColor_observed] using ha.1
    · simpa only [glueColor_observed] using hb.1
  · obtain ⟨w,hw,rfl⟩ := (sideEdge_mem_iff x y x e v).mp hv
    simpa only [glueColor_left] using a.2.2 e w hw
  · obtain ⟨w,hw,rfl⟩ := (sideEdge_mem_iff x y y e v).mp hv
    simpa only [glueColor_right] using b.2.2 e w hw

theorem side_coloring_nonempty {q : ℕ} {F : V → Finset (Fin q)}
    (hfull : Nonempty (Coloring G q F)) (x y r : V) :
    Nonempty (Coloring (sideGraph (G := G) x y r) q (fun v => F v.1)) := by
  obtain ⟨σ⟩ := hfull
  exact ⟨restrictSide x y r σ⟩

theorem sideCompatible_ratio [Fintype V] {q : ℕ} (F : V → Finset (Fin q))
    (x y r : V) (c : Fin q) :
    (Fintype.card {σ : Coloring (sideGraph (G := G) x y r) q (fun v => F v.1) //
      SideCompatible F x y r c σ} : ℝ) /
      Fintype.card (Coloring (sideGraph (G := G) x y r) q (fun v => F v.1)) =
    rootAvailability (G := sideGraph (G := G) x y r) (sideRoot x y r) q (fun v => F v.1) c := by
  classical
  have hnum := Fintype.card_congr ((Equiv.refl
    (Coloring (sideGraph (G := G) x y r) q (fun v => F v.1))).subtypeEquiv
    (p := SideCompatible F x y r c)
    (q := fun σ => c ∉ F r ∧ ∀ i : (sideGraph (G := G) x y r).neighborSet (sideRoot x y r),
      σ.1 (rootEdge (sideRoot x y r) i) ≠ c)
    (fun σ => by
      change (c ∉ F r ∧ _) ↔ (c ∉ F r ∧ _)
      rw [root_avoid_iff]; rfl))
  rw [hnum]
  unfold rootAvailability
  change _ = if c ∈ F r then 0 else _
  by_cases hc : c ∈ F r <;> simp [hc]

theorem sigma_subtype_pair_ext {I A B : Type*} {P : I → A → Prop} {Q : I → B → Prop}
    (z w : (i : I) × ({a : A // P i a} × {b : B // Q i b}))
    (hi : z.1 = w.1) (ha : z.2.1.1 = w.2.1.1) (hb : z.2.2.1 = w.2.2.1) : z = w := by
  rcases z with ⟨i, ⟨⟨a, hpa⟩, ⟨b, hqb⟩⟩⟩
  rcases w with ⟨j, ⟨⟨a', hpa'⟩, ⟨b', hqb'⟩⟩⟩
  dsimp only at hi ha hb
  subst j
  subst a'
  subst b'
  rfl

noncomputable def coloringEquivSides (hG : G.IsTree) {x y : V} (hxy : G.Adj x y)
    (q : ℕ) (F : V → Finset (Fin q)) : Coloring G q F ≃
    ((c : Fin q) ×
      ({a : Coloring (sideGraph (G := G) x y x) q (fun v => F v.1) // SideCompatible F x y x c a} ×
       {b : Coloring (sideGraph (G := G) x y y) q (fun v => F v.1) // SideCompatible F x y y c b})) := by
  have hn := cut_not_reachable hG hxy
  have hn' : ¬ (cutGraph (G := G) x y).Reachable y x := fun h => hn h.symm
  refine
    { toFun := fun σ => ⟨σ.1 ⟨s(x,y),hxy⟩,
        ⟨⟨restrictSide x y x σ, restrictSide_compatible hxy rfl hn σ⟩,
         ⟨restrictSide x y y σ, restrictSide_compatible hxy Sym2.eq_swap hn' σ⟩⟩⟩
      invFun := fun z => ⟨glueColor hG hxy z.1 z.2.1.1.1 z.2.2.1.1,
        glueColor_proper hG hxy z.1 z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2,
        glueColor_lists hG hxy z.1 z.2.1.1 z.2.2.1 z.2.1.2 z.2.2.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro σ
    apply Subtype.ext
    funext e
    rcases edge_observed_or_side hG hxy e with rfl | ⟨e,rfl⟩ | ⟨e,rfl⟩ <;>
      simp only [glueColor_observed, glueColor_left, glueColor_right, restrictSide]
  · rintro ⟨c,⟨a,b⟩⟩
    apply sigma_subtype_pair_ext
    · exact glueColor_observed hG hxy c a.1.1 b.1.1
    · apply Subtype.ext
      funext e
      exact glueColor_left hG hxy c a.1.1 b.1.1 e
    · apply Subtype.ext
      funext e
      exact glueColor_right hG hxy c a.1.1 b.1.1 e

/-- The observed-edge marginal is exactly the normalized product of its two actual side messages. -/
theorem coloring_marginal_eq_observedMarginal [Fintype V]
    (hG : G.IsTree) {x y : V} (hxy : G.Adj x y)
    (q : ℕ) (F : V → Finset (Fin q)) (hfull : Nonempty (Coloring G q F)) (c : Fin q) :
    (Fintype.card {σ : Coloring G q F // σ.1 ⟨s(x,y),hxy⟩ = c} : ℝ) /
      Fintype.card (Coloring G q F) =
    observedMarginal
      (rootAvailability (G := sideGraph (G := G) x y x) (sideRoot x y x) q (fun v => F v.1))
      (rootAvailability (G := sideGraph (G := G) x y y) (sideRoot x y y) q (fun v => F v.1)) c := by
  have h := normalized_color_pair_counts (SideCompatible F x y x) (SideCompatible F x y y)
    (fun σ : Coloring G q F => σ.1 ⟨s(x,y),hxy⟩)
    (coloringEquivSides hG hxy q F) (fun _ => rfl)
    (side_coloring_nonempty hfull x y x) (side_coloring_nonempty hfull x y y) c
  simp_rw [sideCompatible_ratio] at h
  exact h

end EdgeColoringMixing.ObservedCounting
