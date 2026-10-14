import MainTheorems.Tuza.FiniteGadgets
import MainTheorems.Tuza.DecompositionAssembly

namespace ResearchMain.Tuza

def pairEmbedding {V : Type*} (x y : V) (hxy : x ≠ y) : Fin 2 ↪ V where
  toFun i := if i = 0 then x else y
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

@[simp]
theorem pairEmbedding_zero {V : Type*} (x y : V) (hxy : x ≠ y) :
    pairEmbedding x y hxy 0 = x := rfl

@[simp]
theorem pairEmbedding_one {V : Type*} (x y : V) (hxy : x ≠ y) :
    pairEmbedding x y hxy 1 = y := rfl

def productEmbedding {V W Q : Type*} (e : V ↪ W) : (V × Q) ↪ (W × Q) where
  toFun x := (e x.1, x.2)
  inj' := by
    intro x y h
    exact Prod.ext (e.injective (congrArg (fun z : W × Q => z.1) h))
      (congrArg (fun z : W × Q => z.2) h)

@[simp]
theorem productEmbedding_apply {V W Q : Type*} (e : V ↪ W) (x : V × Q) :
    productEmbedding e x = (e x.1, x.2) := rfl

theorem image_cycleGadget_iff {V : Type*} (x y : V) (hne : x ≠ y) (u v : V × ZMod 3) :
    (imageGraph cycleGadget (productEmbedding (pairEmbedding x y hne))).Adj u v ↔
      u.2 ≠ v.2 ∧ ((u.1 = x ∧ v.1 = x) ∨ (u.1 = x ∧ v.1 = y) ∨
        (u.1 = y ∧ v.1 = x)) := by
  constructor
  · rintro ⟨⟨i, a⟩, ⟨j, b⟩, rfl, rfl, h⟩
    fin_cases i <;> fin_cases j
    all_goals simp_all [cycleGadget]
  · rintro ⟨hlabel, h | h | h⟩
    · refine ⟨(0, u.2), (0, v.2), ?_, ?_, ?_⟩
      · exact Prod.ext h.1.symm rfl
      · exact Prod.ext h.2.symm rfl
      · simp [cycleGadget, hlabel]
    · refine ⟨(0, u.2), (1, v.2), ?_, ?_, ?_⟩
      · exact Prod.ext h.1.symm rfl
      · exact Prod.ext h.2.symm rfl
      · simp [cycleGadget, hlabel]
    · refine ⟨(1, u.2), (0, v.2), ?_, ?_, ?_⟩
      · exact Prod.ext h.1.symm rfl
      · exact Prod.ext h.2.symm rfl
      · simp [cycleGadget, hlabel]

def cycleInflationGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph (V × ZMod 3) where
  Adj x y := (x.1 = y.1 ∧ x.2 ≠ y.2) ∨ (G.Adj x.1 y.1 ∧ x.2 ≠ y.2)
  symm := ⟨by
    intro x y h
    rcases h with h | h
    · exact Or.inl ⟨h.1.symm, h.2.symm⟩
    · exact Or.inr ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h
    · exact h.2 rfl
    · exact h.2 rfl⟩

theorem exists_cycle_inflation_decomposition {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (S : CycleOrientation G) :
    Nonempty (TriangleDecomposition (cycleInflationGraph G)) := by
  classical
  let f (x : V) : (Fin 2 × ZMod 3) ↪ (V × ZMod 3) :=
    productEmbedding (pairEmbedding x (S.successor x) (S.adjacent x).ne)
  let H (x : V) := imageGraph cycleGadget (f x)
  have hd (x : V) : Nonempty (TriangleDecomposition (H x)) := cycleGadgetDecomposition.map (f x)
  let D (x : V) := Classical.choice (hd x)
  apply TriangleDecomposition.of_partition H D
  · intro x u v huv
    obtain ⟨hlabel, h | h | h⟩ := (image_cycleGadget_iff x (S.successor x) (S.adjacent x).ne u v).mp huv
    · exact Or.inl ⟨h.1.trans h.2.symm, hlabel⟩
    · exact Or.inr ⟨by rw [h.1, h.2]; exact S.adjacent x, hlabel⟩
    · exact Or.inr ⟨by rw [h.1, h.2]; exact (S.adjacent x).symm, hlabel⟩
  · intro x y hxy u v huv huv'
    obtain ⟨_, hx⟩ := (image_cycleGadget_iff x (S.successor x) (S.adjacent x).ne u v).mp huv
    obtain ⟨_, hy⟩ := (image_cycleGadget_iff y (S.successor y) (S.adjacent y).ne u v).mp huv'
    rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
    all_goals have hnx := (S.adjacent x).ne
    all_goals have hny := (S.adjacent y).ne
    all_goals have hrev := S.noReverse x
    all_goals try exact hxy (hx.1.symm.trans hy.1)
    all_goals try exact hxy (S.successor.injective (hx.1.symm.trans hy.1))
    all_goals
      have he : S.successor x = y := by grind
      have he' : S.successor y = x := by grind
      exact hrev (by rw [he, he'])
  · intro u v huv
    rcases huv with h | h
    · refine ⟨u.1, ?_⟩
      exact (image_cycleGadget_iff u.1 (S.successor u.1) (S.adjacent u.1).ne u v).mpr
        ⟨h.2, Or.inl ⟨rfl, h.1.symm⟩⟩
    · rcases S.exhaustive u.1 v.1 h.1 with hs | hs
      · exact ⟨u.1, (image_cycleGadget_iff u.1 (S.successor u.1) (S.adjacent u.1).ne u v).mpr
          ⟨h.2, Or.inr (Or.inl ⟨rfl, hs.symm⟩)⟩⟩
      · exact ⟨v.1, (image_cycleGadget_iff v.1 (S.successor v.1) (S.adjacent v.1).ne u v).mpr
          ⟨h.2, Or.inr (Or.inr ⟨hs.symm, rfl⟩)⟩⟩

end ResearchMain.Tuza
