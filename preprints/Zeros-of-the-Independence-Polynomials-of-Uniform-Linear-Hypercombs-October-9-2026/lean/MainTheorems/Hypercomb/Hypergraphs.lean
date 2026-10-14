import Mathlib.Data.Finset.Sum
import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace ResearchMain.Hypercomb

open Classical

def StrongIndependent {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (S : Finset V) : Prop :=
  ∀ E ∈ H, (S ∩ E).card ≤ 1

theorem strongIndependent_insert {V : Type*} [DecidableEq V] (H : Finset (Finset V)) (E S : Finset V) :
    StrongIndependent (insert E H) S ↔ (S ∩ E).card ≤ 1 ∧ StrongIndependent H S := by
  constructor
  · intro h
    exact ⟨h E (Finset.mem_insert_self _ _), fun F hF => h F (Finset.mem_insert_of_mem hF)⟩
  · rintro ⟨hE, h⟩ F hF
    rcases Finset.mem_insert.mp hF with rfl | hF
    · exact hE
    · exact h F hF

theorem disjSum_inter {V W : Type*} [DecidableEq V] [DecidableEq W] (S E : Finset V) (T F : Finset W) :
    (S.disjSum T) ∩ (E.disjSum F) = (S ∩ E).disjSum (T ∩ F) := by
  ext (v | w) <;> simp

theorem strongIndependent_old {V W : Type*} [DecidableEq V] [DecidableEq W]
    (H : Finset (Finset V)) (S : Finset V) (T : Finset W) :
    StrongIndependent (H.image fun E => E.map (Function.Embedding.inl : V ↪ V ⊕ W)) (S.disjSum T) ↔
      StrongIndependent H S := by
  constructor
  · intro h E hE
    have h' := h (E.map Function.Embedding.inl) (Finset.mem_image.mpr ⟨E, hE, rfl⟩)
    rw [← Finset.disjSum_empty, disjSum_inter] at h'
    simpa using h'
  · intro h E hE
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
    rw [← Finset.disjSum_empty, disjSum_inter]
    simpa using h F hF

noncomputable def extensionEdges {V P T : Type*} [Fintype P] [Fintype T]
    [DecidableEq V] [DecidableEq P] [DecidableEq T]
    (H : Finset (Finset V)) (r : V) : Finset (Finset (V ⊕ (Option P ⊕ T))) :=
  insert ((∅ : Finset V).disjSum (({none} : Finset (Option P)).disjSum (Finset.univ : Finset T)))
    (insert (({r} : Finset V).disjSum ((Finset.univ : Finset (Option P)).disjSum (∅ : Finset T)))
      (H.image fun E => E.map Function.Embedding.inl))

theorem extension_strongIndependent {V P T : Type*} [Fintype P] [Fintype T]
    [DecidableEq V] [DecidableEq P] [DecidableEq T]
    (H : Finset (Finset V)) (r : V) (S : Finset V) (L : Finset (Option P)) (U : Finset T) :
    StrongIndependent (extensionEdges (P := P) (T := T) H r) (S.disjSum (L.disjSum U)) ↔
      StrongIndependent H S ∧ (S ∩ {r}).card + L.card ≤ 1 ∧ (L ∩ {none}).card + U.card ≤ 1 := by
  rw [extensionEdges, strongIndependent_insert, strongIndependent_insert, strongIndependent_old,
    disjSum_inter, disjSum_inter, disjSum_inter, disjSum_inter]
  simp only [Finset.inter_empty, Finset.inter_univ, Finset.card_disjSum, Finset.card_empty,
    zero_add, add_zero]
  tauto

def combVertices (a : ℕ) : ℕ → Type
  | 0 => Option (Fin a)
  | n + 1 => combVertices a n ⊕ (Option (Fin (a - 1)) ⊕ Fin a)

@[instance_reducible]
def combVerticesFintype (a : ℕ) : ∀ n, Fintype (combVertices a n)
  | 0 => inferInstanceAs (Fintype (Option (Fin a)))
  | n + 1 =>
      letI := combVerticesFintype a n
      inferInstanceAs (Fintype (combVertices a n ⊕ (Option (Fin (a - 1)) ⊕ Fin a)))

instance (a n : ℕ) : Fintype (combVertices a n) := combVerticesFintype a n

@[instance_reducible]
def combVerticesDecidableEq (a : ℕ) : ∀ n, DecidableEq (combVertices a n)
  | 0 => inferInstanceAs (DecidableEq (Option (Fin a)))
  | n + 1 =>
      letI := combVerticesDecidableEq a n
      inferInstanceAs (DecidableEq (combVertices a n ⊕ (Option (Fin (a - 1)) ⊕ Fin a)))

instance (a n : ℕ) : DecidableEq (combVertices a n) := combVerticesDecidableEq a n

def combRoot (a : ℕ) : ∀ n, combVertices a n
  | 0 => none
  | _ + 1 => Sum.inr (Sum.inl none)

noncomputable def combEdges (a : ℕ) : ∀ n, Finset (Finset (combVertices a n))
  | 0 => {Finset.univ}
  | n + 1 => extensionEdges (P := Fin (a - 1)) (T := Fin a) (combEdges a n) (combRoot a n)

theorem combEdges_uniform (a : ℕ) (ha : 1 ≤ a) (n : ℕ) :
    ∀ E ∈ combEdges a n, E.card = a + 1 := by
  induction n with
  | zero =>
    change ∀ E : Finset (Option (Fin a)), E ∈ ({Finset.univ} : Finset (Finset (Option (Fin a)))) → E.card = a + 1
    intro E hE
    have he : E = Finset.univ := Finset.mem_singleton.mp hE
    rw [he]
    simp only [Finset.card_univ, Fintype.card_option, Fintype.card_fin]
  | succ n ih =>
    change ∀ E : Finset (combVertices a n ⊕ (Option (Fin (a - 1)) ⊕ Fin a)),
      E ∈ extensionEdges (P := Fin (a - 1)) (T := Fin a) (combEdges a n) (combRoot a n) → E.card = a + 1
    intro E hE
    change E ∈ extensionEdges (P := Fin (a - 1)) (T := Fin a) (combEdges a n) (combRoot a n) at hE
    rw [extensionEdges] at hE
    rcases Finset.mem_insert.mp hE with rfl | hE
    · simp only [Finset.card_disjSum, Finset.card_empty, Finset.card_singleton,
        Finset.card_univ, Fintype.card_fin]
      omega
    · rcases Finset.mem_insert.mp hE with rfl | hE
      · simp only [Finset.card_disjSum, Finset.card_empty, Finset.card_singleton,
          Finset.card_univ, Fintype.card_option, Fintype.card_fin]
        omega
      · obtain ⟨F, hF, rfl⟩ := Finset.mem_image.mp hE
        rw [Finset.card_map]
        exact ih F hF

noncomputable def strongIndependentSets (a n : ℕ) : Finset (Finset (combVertices a n)) :=
  Finset.univ.filter (StrongIndependent (combEdges a n))

noncomputable def strongIndependencePolynomial (a n : ℕ) : Polynomial ℝ :=
  ∑ S ∈ strongIndependentSets a n, Polynomial.X ^ S.card

end ResearchMain.Hypercomb
