import MainTheorems.Tuza.CliquePacking
import MainTheorems.Tuza.FanCountConstruction

namespace ResearchMain.Tuza

variable {V K : Type*} [DecidableEq V] [DecidableEq K]

def EdgeRegionSupport (c : V → K) (R : Finset (Sym2 K)) (P : Finset (Finset V)) : Prop :=
  ∀ t ∈ P, ∀ e ∈ triangleEdges t, e.map c ∈ R

def colorPairs (A B : Finset K) : Finset (Sym2 K) := (A.product B).image (fun p => s(p.1, p.2))

omit [DecidableEq K] in
theorem CliqueSupport.region {I : Type*} {a : I → V} {P : Finset (Finset V)}
    (hP : CliqueSupport a P) (c : V → K) (A : Finset K) (ha : ∀ i, c (a i) ∈ A) :
    EdgeRegionSupport c A.sym2 P := by
  intro t ht e he
  obtain ⟨i, j, rfl⟩ := hP t ht e he
  apply Finset.mk_mem_sym2_iff.mpr
  exact ⟨ha i, ha j⟩

theorem FanSupport.region {C Q : Type*} [DecidableEq C] [DecidableEq Q]
    {a : C → V} {b : Q → V} {P : Finset (Finset V)} (hP : FanSupport a b P)
    (c : V → K) (A B : Finset K) (ha : ∀ i, c (a i) ∈ A) (hb : ∀ j, c (b j) ∈ B) :
    EdgeRegionSupport c (B.sym2 ∪ colorPairs A B) P := by
  intro t ht e he
  rcases hP t ht e he with ⟨i, j, rfl⟩ | ⟨i, j, rfl⟩
  · exact Finset.mem_union_left _ (Finset.mk_mem_sym2_iff.mpr ⟨hb i, hb j⟩)
  · apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨(c (a i), c (b j)), Finset.mem_product.mpr ⟨ha i, hb j⟩, rfl⟩

omit [DecidableEq K] in
theorem EdgeRegionSupport.disjoint {c : V → K} {R S : Finset (Sym2 K)}
    {P Q : Finset (Finset V)} (hP : EdgeRegionSupport c R P) (hQ : EdgeRegionSupport c S Q)
    (hrs : Disjoint R S) {t u : Finset V} (ht : t ∈ P) (hu : u ∈ Q) :
    Disjoint (triangleEdges t) (triangleEdges u) := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  exact Finset.disjoint_left.mp hrs (hP t ht e he) (hQ u hu e he')

theorem EdgeRegionSupport.union {c : V → K} {R S : Finset (Sym2 K)}
    {P Q : Finset (Finset V)} (hP : EdgeRegionSupport c R P) (hQ : EdgeRegionSupport c S Q) :
    EdgeRegionSupport c (R ∪ S) (P ∪ Q) := by
  intro t ht e he
  rcases Finset.mem_union.mp ht with ht | ht
  · exact Finset.mem_union_left _ (hP t ht e he)
  · exact Finset.mem_union_right _ (hQ t ht e he)

theorem combine_region_packings {G : SimpleGraph V} {c : V → K} {R S : Finset (Sym2 K)}
    {P Q : Finset (Finset V)} (hP : Packing G P) (hQ : Packing G Q)
    (hPs : EdgeRegionSupport c R P) (hQs : EdgeRegionSupport c S Q) (hrs : Disjoint R S) :
    ∃ T : Finset (Finset V), Packing G T ∧ T.card = P.card + Q.card ∧ EdgeRegionSupport c (R ∪ S) T := by
  have hcross : ∀ t ∈ P, ∀ u ∈ Q, Disjoint (triangleEdges t) (triangleEdges u) :=
    fun _ ht _ hu => hPs.disjoint hQs hrs ht hu
  exact ⟨P ∪ Q, hP.union hQ hcross, hP.card_union hcross, hPs.union hQs⟩

omit [DecidableEq K] in
theorem exists_region_clique_packing {G : SimpleGraph V} {n : ℕ} (a : Fin n ↪ V)
    (ha : ∀ i j, i ≠ j → G.Adj (a i) (a j)) (c : V → K) (A : Finset K)
    (hcolor : ∀ i, c (a i) ∈ A) :
    ∃ P : Finset (Finset V), Packing G P ∧ P.card = completeCount n ∧ EdgeRegionSupport c A.sym2 P := by
  obtain ⟨P, hP, hc, hs⟩ := exists_clique_packing a ha
  exact ⟨P, hP, hc, hs.region c A hcolor⟩

theorem exists_region_fan_packing {G : SimpleGraph V} {n q : ℕ}
    (a : Fin n ↪ V) (b : Fin q ↪ V) (hd : ∀ i j, a i ≠ b j)
    (ha : ∀ i j, G.Adj (a i) (b j)) (hb : ∀ i j, i ≠ j → G.Adj (b i) (b j))
    (c : V → K) (A B : Finset K) (hca : ∀ i, c (a i) ∈ A) (hcb : ∀ j, c (b j) ∈ B) :
    ∃ P : Finset (Finset V), Packing G P ∧ P.card = fanCount n q ∧
      EdgeRegionSupport c (B.sym2 ∪ colorPairs A B) P := by
  obtain ⟨P, hP, hc, hs⟩ := exists_fanCount_packing a b hd ha hb
  exact ⟨P, hP, hc, hs.region c A B hca hcb⟩

end ResearchMain.Tuza
