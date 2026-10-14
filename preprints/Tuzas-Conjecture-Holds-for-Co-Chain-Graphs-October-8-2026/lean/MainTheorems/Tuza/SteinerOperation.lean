import MainTheorems.Tuza.PackingEdges

namespace ResearchMain.Tuza

structure SteinerOperation (V : Type*) where
  third : V → V → V
  comm : ∀ x y, third x y = third y x
  involutive : ∀ x y, third x (third x y) = y
  idempotent : ∀ x, third x x = x

namespace SteinerOperation

variable {V : Type*} [DecidableEq V] (S : SteinerOperation V)

def block (x y : V) : Finset V := {x, y, S.third x y}

omit [DecidableEq V] in
theorem third_ne_left {x y : V} (hxy : x ≠ y) : S.third x y ≠ x := by
  intro h
  have ht := S.involutive x y
  rw [h, S.idempotent] at ht
  exact hxy ht

omit [DecidableEq V] in
theorem third_ne_right {x y : V} (hxy : x ≠ y) : S.third x y ≠ y := by
  rw [S.comm]
  exact S.third_ne_left hxy.symm

theorem block_clique {x y : V} (hxy : x ≠ y) :
    (⊤ : SimpleGraph V).IsNClique 3 (S.block x y) := by
  apply SimpleGraph.is3Clique_iff.mpr
  refine ⟨x, y, S.third x y, hxy, (S.third_ne_left hxy).symm,
    (S.third_ne_right hxy).symm, rfl⟩

theorem block_eq_of_pair {x y a b : V} (ha : a ∈ S.block x y) (hb : b ∈ S.block x y)
    (hab : a ≠ b) : S.block a b = S.block x y := by
  have hxz := S.involutive x y
  have hyz : S.third y (S.third x y) = x := by
    rw [S.comm x y]
    exact S.involutive y x
  have hzx : S.third (S.third x y) x = y := (S.comm _ _).trans hxz
  have hzy : S.third (S.third x y) y = x := (S.comm _ _).trans hyz
  have hyx := S.comm y x
  simp only [block, Finset.mem_insert, Finset.mem_singleton] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  all_goals try exact False.elim (hab rfl)
  all_goals
    ext v
    simp only [block, hxz, hyz, hzx, hzy, hyx, Finset.mem_insert, Finset.mem_singleton] <;> tauto

def blocks [Fintype V] : Finset (Finset V) :=
  (Finset.univ.filter (fun p : V × V => p.1 ≠ p.2)).image (fun p => S.block p.1 p.2)

theorem mem_blocks [Fintype V] {t : Finset V} :
    t ∈ S.blocks ↔ ∃ x y, x ≠ y ∧ t = S.block x y := by
  constructor
  · intro ht
    obtain ⟨⟨x, y⟩, hp, he⟩ := Finset.mem_image.mp ht
    exact ⟨x, y, (Finset.mem_filter.mp hp).2, he.symm⟩
  · rintro ⟨x, y, hxy, rfl⟩
    exact Finset.mem_image.mpr ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxy⟩, rfl⟩

theorem blocks_packing [Fintype V] : Packing (⊤ : SimpleGraph V) S.blocks := by
  refine ⟨?_, ?_⟩
  · intro t ht
    obtain ⟨x, y, hxy, rfl⟩ := S.mem_blocks.mp ht
    exact S.block_clique hxy
  · intro t ht u hu htu
    obtain ⟨x, y, _, rfl⟩ := S.mem_blocks.mp ht
    obtain ⟨z, w, _, rfl⟩ := S.mem_blocks.mp hu
    apply Finset.disjoint_left.mpr
    intro e he₁ he₂
    induction e using Sym2.inductionOn with
    | hf a b =>
      obtain ⟨ha₁, hb₁, hab⟩ := mem_triangleEdges.mp he₁
      obtain ⟨ha₂, hb₂, _⟩ := mem_triangleEdges.mp he₂
      exact htu ((S.block_eq_of_pair ha₁ hb₁ hab).symm.trans (S.block_eq_of_pair ha₂ hb₂ hab))

noncomputable def decomposition [Fintype V] : TriangleDecomposition (⊤ : SimpleGraph V) where
  triangles := S.blocks
  packing := S.blocks_packing
  covers e := by
    induction e using Sym2.inductionOn with
    | hf x y =>
      intro hxy
      apply mem_packingEdges.mpr
      refine ⟨S.block x y, S.mem_blocks.mpr ⟨x, y, hxy, rfl⟩, ?_⟩
      exact mem_triangleEdges.mpr ⟨by simp [block], by simp [block], hxy⟩

theorem blocks_card [Fintype V] : 3 * S.blocks.card = (Fintype.card V).choose 2 := by
  have he := S.decomposition.card
  rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two] at he
  exact he

end SteinerOperation

end ResearchMain.Tuza
