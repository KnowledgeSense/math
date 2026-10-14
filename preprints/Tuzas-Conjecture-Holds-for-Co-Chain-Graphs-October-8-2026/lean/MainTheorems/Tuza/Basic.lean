import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace ResearchMain.Tuza

variable {V : Type*} [DecidableEq V]

def triangleEdges (s : Finset V) : Finset (Sym2 V) := s.sym2.filter (fun e => ¬e.IsDiag)

@[simp]
theorem mem_triangleEdges {s : Finset V} {a b : V} :
    s(a, b) ∈ triangleEdges s ↔ a ∈ s ∧ b ∈ s ∧ a ≠ b := by
  simp only [triangleEdges, Finset.mem_filter, Finset.mk_mem_sym2_iff, Sym2.mk_isDiag_iff]
  tauto

def Packing (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  (∀ t ∈ P, G.IsNClique 3 t) ∧
    (P : Set (Finset V)).Pairwise (fun t u => Disjoint (triangleEdges t) (triangleEdges u))

def Cover (G : SimpleGraph V) (C : Finset (Sym2 V)) : Prop :=
  (∀ e ∈ C, e ∈ G.edgeSet) ∧ ∀ t, G.IsNClique 3 t → (triangleEdges t ∩ C).Nonempty

theorem triangleEdges_subset {G : SimpleGraph V} {t : Finset V} (ht : G.IsNClique 3 t) :
    ∀ e ∈ triangleEdges t, e ∈ G.edgeSet := by
  intro e
  induction e using Sym2.inductionOn with
  | hf a b =>
    intro he
    obtain ⟨ha, hb, hab⟩ := mem_triangleEdges.mp he
    exact ht.isClique ha hb hab

theorem triangleEdges_nonempty {G : SimpleGraph V} {t : Finset V} (ht : G.IsNClique 3 t) :
    (triangleEdges t).Nonempty := by
  obtain ⟨a, b, c, hab, _, _, rfl⟩ := G.is3Clique_iff.mp ht
  refine ⟨s(a, b), mem_triangleEdges.mpr ⟨?_, ?_, hab.ne⟩⟩ <;> simp

@[simp]
theorem packing_empty (G : SimpleGraph V) : Packing G ∅ := by
  simp [Packing]

theorem Packing.mono {G H : SimpleGraph V} {P : Finset (Finset V)}
    (hP : Packing G P) (h : G ≤ H) : Packing H P :=
  ⟨fun t ht => (hP.1 t ht).mono h, hP.2⟩

theorem Packing.subset {G : SimpleGraph V} {P Q : Finset (Finset V)}
    (hP : Packing G P) (h : Q ⊆ P) : Packing G Q :=
  ⟨fun t ht => hP.1 t (h ht), hP.2.mono (by exact_mod_cast h)⟩

theorem Packing.union {G : SimpleGraph V} {P Q : Finset (Finset V)}
    (hP : Packing G P) (hQ : Packing G Q)
    (hcross : ∀ t ∈ P, ∀ u ∈ Q, Disjoint (triangleEdges t) (triangleEdges u)) : Packing G (P ∪ Q) := by
  refine ⟨?_, ?_⟩
  · intro t ht
    exact (Finset.mem_union.mp ht).elim (hP.1 t) (hQ.1 t)
  · intro t ht u hu htu
    rcases Finset.mem_union.mp ht with ht | ht <;> rcases Finset.mem_union.mp hu with hu | hu
    · exact hP.2 ht hu htu
    · exact hcross t ht u hu
    · exact (hcross u hu t ht).symm
    · exact hQ.2 ht hu htu

theorem Cover.of_subset {G : SimpleGraph V} {C D : Finset (Sym2 V)}
    (hC : Cover G C) (h : C ⊆ D) (hD : ∀ e ∈ D, e ∈ G.edgeSet) : Cover G D := by
  refine ⟨hD, ?_⟩
  intro t ht
  obtain ⟨e, he⟩ := hC.2 t ht
  obtain ⟨het, heC⟩ := Finset.mem_inter.mp he
  exact ⟨e, Finset.mem_inter.mpr ⟨het, h heC⟩⟩

theorem Cover.restrict {G H : SimpleGraph V} {C : Finset (Sym2 V)}
    (hC : Cover H C) (h : G ≤ H) [Fintype V] [DecidableRel G.Adj] :
    Cover G (C ∩ G.edgeFinset) := by
  refine ⟨fun _ he => G.mem_edgeFinset.mp (Finset.mem_inter.mp he).2, ?_⟩
  intro t ht
  obtain ⟨e, he⟩ := hC.2 t (ht.mono h)
  obtain ⟨het, heC⟩ := Finset.mem_inter.mp he
  exact ⟨e, Finset.mem_inter.mpr ⟨het, Finset.mem_inter.mpr
    ⟨heC, G.mem_edgeFinset.mpr (triangleEdges_subset ht e het)⟩⟩⟩

variable [Fintype V]

theorem exists_cover (G : SimpleGraph V) : ∃ C : Finset (Sym2 V), Cover G C := by
  classical
  refine ⟨G.edgeFinset, ⟨fun _ he => G.mem_edgeFinset.mp he, ?_⟩⟩
  intro t ht
  obtain ⟨e, he⟩ := triangleEdges_nonempty ht
  exact ⟨e, Finset.mem_inter.mpr ⟨he, G.mem_edgeFinset.mpr (triangleEdges_subset ht e he)⟩⟩

noncomputable def packingNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ.filter (Packing G)).sup Finset.card

noncomputable def coverNumber (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.find (by obtain ⟨C, hC⟩ := exists_cover G; exact ⟨C.card, C, hC, rfl⟩ :
    ∃ n, ∃ C : Finset (Sym2 V), Cover G C ∧ C.card = n)

def Inequality (G : SimpleGraph V) : Prop := coverNumber G ≤ 2 * packingNumber G

theorem packing_le_number {G : SimpleGraph V} {P : Finset (Finset V)} (hP : Packing G P) :
    P.card ≤ packingNumber G := by
  classical
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP⟩)

theorem exists_maximum_packing (G : SimpleGraph V) :
    ∃ P : Finset (Finset V), Packing G P ∧ P.card = packingNumber G := by
  classical
  have hn : (Finset.univ.filter (Packing G)).Nonempty :=
    ⟨∅, Finset.mem_filter.mpr ⟨Finset.mem_univ _, packing_empty G⟩⟩
  obtain ⟨P, hP, heq⟩ := Finset.exists_mem_eq_sup (Finset.univ.filter (Packing G)) hn Finset.card
  exact ⟨P, (Finset.mem_filter.mp hP).2, heq.symm⟩

theorem exists_minimum_cover (G : SimpleGraph V) :
    ∃ C : Finset (Sym2 V), Cover G C ∧ C.card = coverNumber G := by
  classical
  unfold coverNumber
  exact Nat.find_spec (p := fun n => ∃ C : Finset (Sym2 V), Cover G C ∧ C.card = n) _

theorem number_le_cover {G : SimpleGraph V} {C : Finset (Sym2 V)} (hC : Cover G C) :
    coverNumber G ≤ C.card := by
  classical
  exact Nat.find_min' _ ⟨C, hC, rfl⟩

theorem inequality_of_certificates {G : SimpleGraph V} {C : Finset (Sym2 V)} {P : Finset (Finset V)}
    (hC : Cover G C) (hP : Packing G P) (hsize : C.card ≤ 2 * P.card) : Inequality G :=
  (number_le_cover hC).trans (hsize.trans (Nat.mul_le_mul_left 2 (packing_le_number hP)))

theorem packingNumber_mono {G H : SimpleGraph V} (h : G ≤ H) : packingNumber G ≤ packingNumber H := by
  obtain ⟨P, hP, heq⟩ := exists_maximum_packing G
  rw [← heq]
  exact packing_le_number (hP.mono h)

end ResearchMain.Tuza
