import MainTheorems.Tuza.FactorOperations
import MainTheorems.Tuza.LatinTriangles

namespace ResearchMain.Tuza

variable {V Q : Type*} [LinearOrder V] [AddCommGroup Q]

def shiftedGraph (G : SimpleGraph V) (d : Q) : SimpleGraph (V × Q) where
  Adj x y := G.Adj x.1 y.1 ∧
    ((x.1 < y.1 ∧ y.2 = x.2 + d) ∨ (y.1 < x.1 ∧ x.2 = y.2 + d))
  symm := ⟨by
    intro x y h
    refine ⟨h.1.symm, ?_⟩
    exact h.2.elim (fun h => Or.inr h) (fun h => Or.inl h)⟩
  loopless := ⟨by intro x h; exact G.irrefl h.1⟩

theorem shifted_adj_unique {G : SimpleGraph V}
    (hmatch : ∀ x y z, G.Adj x y → G.Adj x z → y = z) {d : Q} {x y z : V × Q}
    (hy : (shiftedGraph G d).Adj x y) (hz : (shiftedGraph G d).Adj x z) : y = z := by
  have he := hmatch x.1 y.1 z.1 hy.1 hz.1
  apply Prod.ext he
  rcases hy.2 with hy | hy <;> rcases hz.2 with hz | hz
  · exact hy.2.trans hz.2.symm
  · exact False.elim ((not_lt_of_ge (by rw [he]; exact le_of_lt hz.1)) hy.1)
  · exact False.elim ((not_lt_of_ge (by rw [← he]; exact le_of_lt hy.1)) hz.1)
  · exact add_right_cancel (hy.2.symm.trans hz.2)

theorem shifted_factor_unique {G : SimpleGraph V} {d e : Q} {x y : V × Q}
    (hd : (shiftedGraph G d).Adj x y) (he : (shiftedGraph G e).Adj x y) : d = e := by
  rcases hd.2 with hd | hd <;> rcases he.2 with he | he
  · exact add_left_cancel (hd.2.symm.trans he.2)
  · exact False.elim (lt_asymm hd.1 he.1)
  · exact False.elim (lt_asymm hd.1 he.1)
  · exact add_left_cancel (hd.2.symm.trans he.2)

def shiftedFactors (G : SimpleGraph V)
    (hmatch : ∀ x y z, G.Adj x y → G.Adj x z → y = z)
    (hperfect : ∀ x, ∃ y, G.Adj x y) : PerfectFactors (V × Q) Q where
  graph := shiftedGraph G
  matching := fun _ _ _ _ => shifted_adj_unique hmatch
  separated := fun _ _ _ _ => shifted_factor_unique
  perfect := by
    intro d x
    obtain ⟨y, hy⟩ := hperfect x.1
    rcases lt_or_gt_of_ne hy.ne with hlt | hgt
    · exact ⟨(y, x.2 + d), hy, Or.inl ⟨hlt, rfl⟩⟩
    · exact ⟨(y, x.2 - d), hy, Or.inr ⟨hgt, by simp⟩⟩

theorem shifted_union_eq (G : SimpleGraph V)
    (hmatch : ∀ x y z, G.Adj x y → G.Adj x z → y = z)
    (hperfect : ∀ x, ∃ y, G.Adj x y) :
    (shiftedFactors (Q := Q) G hmatch hperfect).unionGraph = crossGraph G Q := by
  ext x y
  constructor
  · rintro ⟨d, hd⟩
    exact hd.1
  · intro hxy
    have hbase : G.Adj x.1 y.1 := hxy
    rcases lt_or_gt_of_ne hbase.ne with hlt | hgt
    · exact ⟨y.2 - x.2, hxy, Or.inl ⟨hlt, by simp⟩⟩
    · exact ⟨x.2 - y.2, hxy, Or.inr ⟨hgt, by simp⟩⟩

end ResearchMain.Tuza
