import MainTheorems.Tuza.FanPacking
import MainTheorems.Tuza.PackingEdges
import Mathlib.Tactic.FinCases

namespace ResearchMain.Tuza

variable {Q : Type*} [AddCommGroup Q]

def latinLabel (u v : Q) (i : Fin 3) : Q := if i = 0 then u else if i = 1 then v else u + v

theorem latin_label_unique {i j : Fin 3} (hij : i ≠ j) {u v u' v' : Q}
    (hi : latinLabel u v i = latinLabel u' v' i)
    (hj : latinLabel u v j = latinLabel u' v' j) : u = u' ∧ v = v' := by
  fin_cases i <;> fin_cases j
  all_goals try exact False.elim (hij rfl)
  all_goals simp [latinLabel] at hi hj
  all_goals aesop

theorem exists_latin_labels {i j : Fin 3} (hij : i ≠ j) (a b : Q) :
    ∃ u v, latinLabel u v i = a ∧ latinLabel u v j = b := by
  fin_cases i <;> fin_cases j
  all_goals try exact False.elim (hij rfl)
  · exact ⟨a, b, by simp [latinLabel]⟩
  · exact ⟨a, b - a, by simp [latinLabel]⟩
  · exact ⟨b, a, by simp [latinLabel]⟩
  · exact ⟨b - a, a, by simp [latinLabel]⟩
  · exact ⟨b, a - b, by simp [latinLabel]⟩
  · exact ⟨a - b, b, by simp [latinLabel]⟩

variable [DecidableEq Q]

def latinTriangle (u v : Q) : Finset (Fin 3 × Q) :=
  Finset.univ.image (fun i => (i, latinLabel u v i))

@[simp]
theorem mem_latinTriangle {u v : Q} {x : Fin 3 × Q} :
    x ∈ latinTriangle u v ↔ x.2 = latinLabel u v x.1 := by
  constructor
  · intro hx
    obtain ⟨i, _, he⟩ := Finset.mem_image.mp hx
    rw [← he]
  · intro hx
    exact Finset.mem_image.mpr ⟨x.1, Finset.mem_univ _, Prod.ext rfl hx.symm⟩

def crossGraph {V : Type*} (G : SimpleGraph V) (Q : Type*) : SimpleGraph (V × Q) where
  Adj x y := G.Adj x.1 y.1
  symm := ⟨by intro x y h; exact h.symm⟩
  loopless := ⟨by intro x h; exact G.irrefl h⟩

theorem latinTriangle_clique (u v : Q) :
    (crossGraph (⊤ : SimpleGraph (Fin 3)) Q).IsNClique 3 (latinTriangle u v) := by
  refine ⟨?_, ?_⟩
  · intro x hx y hy hxy
    change x.1 ≠ y.1
    intro he
    apply hxy
    apply Prod.ext he
    rw [mem_latinTriangle.mp hx, mem_latinTriangle.mp hy, he]
  · rw [latinTriangle, Finset.card_image_of_injective]
    · simp
    · intro i j h
      exact congrArg Prod.fst h

theorem latinTriangle_disjoint {u v u' v' : Q} (h : (u, v) ≠ (u', v')) :
    Disjoint (triangleEdges (latinTriangle u v)) (triangleEdges (latinTriangle u' v')) := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  induction e using Sym2.inductionOn with
  | hf x y =>
    obtain ⟨hx, hy, hxy⟩ := mem_triangleEdges.mp he
    obtain ⟨hx', hy', _⟩ := mem_triangleEdges.mp he'
    have hij : x.1 ≠ y.1 := (latinTriangle_clique u v).1 hx hy hxy
    have hi := (mem_latinTriangle.mp hx).symm.trans (mem_latinTriangle.mp hx')
    have hj := (mem_latinTriangle.mp hy).symm.trans (mem_latinTriangle.mp hy')
    obtain ⟨hu, hv⟩ := latin_label_unique hij hi hj
    exact h (Prod.ext hu hv)

def latinEmbedding {V : Type*} (e : Fin 3 ↪ V) : (Fin 3 × Q) ↪ (V × Q) where
  toFun x := (e x.1, x.2)
  inj' := by
    intro x y h
    exact Prod.ext (e.injective (congrArg (fun z : V × Q => z.1) h))
      (congrArg (fun z : V × Q => z.2) h)

theorem mem_mapped_latinTriangle {V : Type*} [DecidableEq V] (e : Fin 3 ↪ V)
    (u v : Q) (x : V × Q) :
    x ∈ (latinTriangle u v).map (latinEmbedding e) ↔
      ∃ i, e i = x.1 ∧ x.2 = latinLabel u v i := by
  constructor
  · intro hx
    obtain ⟨z, hz, he⟩ := Finset.mem_map.mp hx
    refine ⟨z.1, congrArg Prod.fst he, ?_⟩
    have hlabel := mem_latinTriangle.mp hz
    exact (congrArg Prod.snd he).symm.trans hlabel
  · rintro ⟨i, hi, hx⟩
    refine Finset.mem_map.mpr ⟨(i, latinLabel u v i), mem_latinTriangle.mpr rfl, ?_⟩
    exact Prod.ext hi hx.symm

theorem mapped_latinTriangle_base_edge {V : Type*} [DecidableEq V] (e : Fin 3 ↪ V)
    {t : Finset V} (ht : ∀ i, e i ∈ t) {u v : Q} {x y : V × Q}
    (hxy : s(x, y) ∈ triangleEdges ((latinTriangle u v).map (latinEmbedding e))) :
    s(x.1, y.1) ∈ triangleEdges t := by
  obtain ⟨hx, hy, hne⟩ := mem_triangleEdges.mp hxy
  obtain ⟨i, hi, hxi⟩ := (mem_mapped_latinTriangle e u v x).mp hx
  obtain ⟨j, hj, hyj⟩ := (mem_mapped_latinTriangle e u v y).mp hy
  refine mem_triangleEdges.mpr ⟨hi ▸ ht i, hj ▸ ht j, ?_⟩
  intro he
  have hij : i = j := e.injective (hi.trans (he.trans hj.symm))
  exact hne (Prod.ext he (hxi.trans (by rw [hij, ← hyj])))

end ResearchMain.Tuza
