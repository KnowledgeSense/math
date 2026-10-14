import MainTheorems.Tuza.ShiftedMatching
import MainTheorems.Tuza.CycleInflation
import MainTheorems.Tuza.BlowupDecomposition

namespace ResearchMain.Tuza
namespace PerfectFactors

variable {V : Type*}

def firstTwo (M : PerfectFactors V (Fin 3)) : PerfectFactors V (Fin 2) :=
  M.reindex ⟨Fin.castSucc, by intro i j h; exact Fin.ext (congrArg (fun z : Fin 3 => z.val) h)⟩

theorem three_union_iff (M : PerfectFactors V (Fin 3)) (x y : V) :
    M.unionGraph.Adj x y ↔ M.firstTwo.unionGraph.Adj x y ∨ (M.graph 2).Adj x y := by
  constructor
  · rintro ⟨i, hi⟩
    fin_cases i
    · exact Or.inl ⟨0, hi⟩
    · exact Or.inl ⟨1, hi⟩
    · exact Or.inr hi
  · rintro (⟨i, hi⟩ | hi)
    · exact ⟨i.castSucc, hi⟩
    · exact ⟨2, hi⟩

variable [LinearOrder V]

theorem diagonal_shifted_disjoint (M : PerfectFactors V (Fin 3))
    (i : Fin 2) (d : ZMod 3) (x y : V × ZMod 3)
    (hi : ((M.firstTwo.diagonal (ZMod 3)).graph i).Adj x y) :
    ¬(shiftedGraph (M.graph 2) d).Adj x y := by
  intro hd
  have he := M.separated i.castSucc 2 x.1 y.1 hi.1 hd.1
  have hv := congrArg Fin.val he
  change i.val = 2 at hv
  have hn := i.isLt
  omega

def inflateThree (M : PerfectFactors V (Fin 3)) :
    PerfectFactors (V × ZMod 3) (Fin 2 ⊕ ZMod 3) :=
  (M.firstTwo.diagonal (ZMod 3)).sum
    (shiftedFactors (M.graph 2) (M.matching 2) (M.perfect 2))
    M.diagonal_shifted_disjoint

theorem inflateThree_union_iff (M : PerfectFactors V (Fin 3)) (x y : V × ZMod 3) :
    M.inflateThree.unionGraph.Adj x y ↔
      (M.firstTwo.unionGraph.Adj x.1 y.1 ∧ x.2 = y.2) ∨ (M.graph 2).Adj x.1 y.1 := by
  have hs := sum_union_iff (M.firstTwo.diagonal (ZMod 3))
    (shiftedFactors (M.graph 2) (M.matching 2) (M.perfect 2))
    M.diagonal_shifted_disjoint x y
  apply hs.trans
  apply or_congr (M.firstTwo.diagonal_union_iff x y)
  rw [shifted_union_eq]
  rfl

end PerfectFactors

theorem inflate_three_factor_decomposition {V : Type*} [Fintype V] [LinearOrder V]
    (D : FactorDecomposition V (Fin 3)) :
    Nonempty (FactorDecomposition (V × ZMod 3) (Fin 2 ⊕ ZMod 3)) := by
  classical
  let M := D.factors
  obtain ⟨B⟩ := exists_blowup_decomposition (Q := ZMod 3) D.triangles
  obtain ⟨S⟩ := M.firstTwo.two_cycle_orientation
  obtain ⟨C⟩ := exists_cycle_inflation_decomposition S
  have hdis : ∀ x y, (crossGraph (⊤ \ M.unionGraph) (ZMod 3)).Adj x y →
      ¬(cycleInflationGraph M.firstTwo.unionGraph).Adj x y := by
    intro x y hxy hcy
    change x.1 ≠ y.1 ∧ ¬M.unionGraph.Adj x.1 y.1 at hxy
    rcases hcy with hcy | hcy
    · exact hxy.1 hcy.1
    · obtain ⟨i, hi⟩ := hcy.1
      exact hxy.2 ⟨i.castSucc, hi⟩
  obtain ⟨E⟩ := B.join C hdis
  have hgraph : crossGraph (⊤ \ M.unionGraph) (ZMod 3) ⊔ cycleInflationGraph M.firstTwo.unionGraph =
      ⊤ \ M.inflateThree.unionGraph := by
    ext x y
    change ((x.1 ≠ y.1 ∧ ¬M.unionGraph.Adj x.1 y.1) ∨
      ((x.1 = y.1 ∧ x.2 ≠ y.2) ∨ (M.firstTwo.unionGraph.Adj x.1 y.1 ∧ x.2 ≠ y.2))) ↔
      x ≠ y ∧ ¬M.inflateThree.unionGraph.Adj x y
    rw [M.three_union_iff, M.inflateThree_union_iff]
    have hsep : M.firstTwo.unionGraph.Adj x.1 y.1 → ¬(M.graph 2).Adj x.1 y.1 := by
      rintro ⟨i, hi⟩ ht
      have he := M.separated i.castSucc 2 x.1 y.1 hi ht
      have hv := congrArg Fin.val he
      change i.val = 2 at hv
      have hn := i.isLt
      omega
    by_cases hb : x.1 = y.1
    · have htwo : ¬M.firstTwo.unionGraph.Adj x.1 y.1 := by
        rw [hb]
        exact M.firstTwo.unionGraph.irrefl
      have hthird : ¬(M.graph 2).Adj x.1 y.1 := by rw [hb]; exact (M.graph 2).irrefl
      have hneq : x ≠ y ↔ x.2 ≠ y.2 :=
        ⟨fun h he => h (Prod.ext hb he), fun h he => h (congrArg Prod.snd he)⟩
      tauto
    · have hne : x ≠ y := fun he => hb (congrArg Prod.fst he)
      tauto
  rw [hgraph] at E
  exact ⟨⟨M.inflateThree, E⟩⟩

end ResearchMain.Tuza
