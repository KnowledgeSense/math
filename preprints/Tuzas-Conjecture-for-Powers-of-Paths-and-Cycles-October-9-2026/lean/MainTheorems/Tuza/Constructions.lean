import MainTheorems.Tuza.Basic

namespace ResearchMain.Tuza

variable {V I : Type*} [DecidableEq V]

structure PackingFamily (G : SimpleGraph V) (I : Type*) where
  triangle : I → Finset V
  clique : ∀ i, G.IsNClique 3 (triangle i)
  disjoint : ∀ i j, i ≠ j → Disjoint (triangleEdges (triangle i)) (triangleEdges (triangle j))

namespace PackingFamily

variable {G : SimpleGraph V}

theorem injective (P : PackingFamily G I) : Function.Injective P.triangle := by
  intro i j hij
  by_contra hne
  obtain ⟨e, he⟩ := triangleEdges_nonempty (P.clique i)
  have hd := Finset.disjoint_left.mp (P.disjoint i j hne)
  exact hd he (hij ▸ he)

def carrier [Fintype I] (P : PackingFamily G I) : Finset (Finset V) := Finset.univ.image P.triangle

theorem packing [Fintype I] (P : PackingFamily G I) : Packing G P.carrier := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    exact P.clique i
  · intro t ht u hu htu
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hu
    exact P.disjoint i j (fun ht => htu (congrArg P.triangle ht))

theorem card [Fintype I] (P : PackingFamily G I) : P.carrier.card = Fintype.card I := by
  rw [carrier, Finset.card_image_of_injective _ P.injective, Finset.card_univ]

theorem number_bound [Fintype V] [Fintype I] (P : PackingFamily G I) :
    Fintype.card I ≤ packingNumber G := by
  rw [← P.card]
  exact packing_le_number P.packing

def in_supergraph {H : SimpleGraph V} (P : PackingFamily G I) (h : G ≤ H) : PackingFamily H I where
  triangle := P.triangle
  clique := fun i => (P.clique i).mono h
  disjoint := P.disjoint

end PackingFamily

def monochromatic (c : V → Bool) : Sym2 V → Bool :=
  Sym2.lift ⟨fun x y => decide (c x = c y), by intro x y; simp [eq_comm]⟩

omit [DecidableEq V] in
@[simp]
theorem monochromatic_mk (c : V → Bool) (a b : V) :
    monochromatic c s(a, b) = true ↔ c a = c b := by
  simp [monochromatic, Sym2.lift_mk]

def coloredCover [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (c : V → Bool) :
    Finset (Sym2 V) := G.edgeFinset.filter (fun e => monochromatic c e = true)

omit [DecidableEq V] in
@[simp]
theorem mem_coloredCover [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) (a b : V) :
    s(a, b) ∈ coloredCover G c ↔ G.Adj a b ∧ c a = c b := by
  simp [coloredCover]

theorem coloredCover_covers [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V → Bool) : Cover G (coloredCover G c) := by
  refine ⟨fun _ he => G.mem_edgeFinset.mp (Finset.mem_filter.mp he).1, ?_⟩
  intro t ht
  obtain ⟨a, b, d, hab, had, hbd, rfl⟩ := G.is3Clique_iff.mp ht
  by_cases hc₁ : c a = c b
  · refine ⟨s(a, b), Finset.mem_inter.mpr ⟨?_, (mem_coloredCover G c a b).mpr ⟨hab, hc₁⟩⟩⟩
    exact mem_triangleEdges.mpr ⟨by simp, by simp, hab.ne⟩
  · by_cases hc₂ : c a = c d
    · refine ⟨s(a, d), Finset.mem_inter.mpr ⟨?_, (mem_coloredCover G c a d).mpr ⟨had, hc₂⟩⟩⟩
      exact mem_triangleEdges.mpr ⟨by simp, by simp, had.ne⟩
    · have hc₃ : c b = c d := by
        cases hca : c a <;> cases hcb : c b <;> cases hcd : c d <;> simp_all
      refine ⟨s(b, d), Finset.mem_inter.mpr ⟨?_, (mem_coloredCover G c b d).mpr ⟨hbd, hc₃⟩⟩⟩
      exact mem_triangleEdges.mpr ⟨by simp, by simp, hbd.ne⟩

end ResearchMain.Tuza
