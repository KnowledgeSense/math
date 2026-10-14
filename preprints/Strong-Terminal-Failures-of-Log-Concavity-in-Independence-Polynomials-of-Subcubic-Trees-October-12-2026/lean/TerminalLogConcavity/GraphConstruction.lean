import TerminalLogConcavity.GraphTransport
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Fintype.Sum

namespace TerminalLogConcavity
open Finset

/-- Vertices of the actual finite graph represented by a forest expression. -/
@[reducible] def ForestExpr.Vertex : ForestExpr → Type
  | .empty => PEmpty
  | .union A B => A.Vertex ⊕ B.Vertex
  | .root A => Option A.Vertex

noncomputable instance ForestExpr.decidableEqVertex (A : ForestExpr) : DecidableEq A.Vertex := by
  induction A with
  | empty => exact inferInstanceAs (DecidableEq PEmpty)
  | union A B ha hb =>
    letI := ha
    letI := hb
    exact inferInstanceAs (DecidableEq (A.Vertex ⊕ B.Vertex))
  | root A ha =>
    letI := ha
    exact inferInstanceAs (DecidableEq (Option A.Vertex))

noncomputable instance ForestExpr.fintypeVertex (A : ForestExpr) : Fintype A.Vertex := by
  induction A with
  | empty => exact inferInstanceAs (Fintype PEmpty)
  | union A B ha hb =>
    letI := ha
    letI := hb
    exact inferInstanceAs (Fintype (A.Vertex ⊕ B.Vertex))
  | root A ha =>
    letI := ha
    exact inferInstanceAs (Fintype (Option A.Vertex))

/-- Distinguished roots of the components. -/
def ForestExpr.IsRoot : (A : ForestExpr) → A.Vertex → Prop
  | .empty, v => v.elim
  | .union A _, .inl v => A.IsRoot v
  | .union _ B, .inr v => B.IsRoot v
  | .root _, none => True
  | .root _, some _ => False

def ForestExpr.Adj : (A : ForestExpr) → A.Vertex → A.Vertex → Prop
  | .empty, v, _ => v.elim
  | .union A _, .inl u, .inl v => A.Adj u v
  | .union _ B, .inr u, .inr v => B.Adj u v
  | .union _ _, .inl _, .inr _ => False
  | .union _ _, .inr _, .inl _ => False
  | .root _, none, none => False
  | .root A, none, some v => A.IsRoot v
  | .root A, some v, none => A.IsRoot v
  | .root A, some u, some v => A.Adj u v

theorem ForestExpr.adj_symm (A : ForestExpr) {u v : A.Vertex} : A.Adj u v → A.Adj v u := by
  induction A with
  | empty => exact u.elim
  | union A B ha hb => cases u <;> cases v <;> simp only [Adj] <;> first | exact ha | exact hb | tauto
  | root A ha => cases u <;> cases v <;> simp only [Adj] <;> first | exact ha | tauto

theorem ForestExpr.adj_irrefl (A : ForestExpr) (u : A.Vertex) : ¬ A.Adj u u := by
  induction A with
  | empty => exact u.elim
  | union A B ha hb => cases u <;> simp only [Adj] <;> first | apply ha | apply hb
  | root A ha => cases u <;> simp only [Adj] <;> first | apply ha | tauto

/-- The finite simple graph with exactly the edges prescribed by the expression. -/
def ForestExpr.graph (A : ForestExpr) : SimpleGraph A.Vertex where
  Adj := A.Adj
  symm := ⟨fun _ _ => A.adj_symm⟩
  loopless := ⟨A.adj_irrefl⟩

/-- Distance below the root of a component. -/
def ForestExpr.depth : (A : ForestExpr) → A.Vertex → ℕ
  | .empty, v => v.elim
  | .union A _, .inl v => A.depth v
  | .union _ B, .inr v => B.depth v
  | .root _, none => 0
  | .root A, some v => A.depth v + 1

theorem ForestExpr.isRoot_iff_depth_zero (A : ForestExpr) (v : A.Vertex) :
    A.IsRoot v ↔ A.depth v = 0 := by
  induction A with
  | empty => exact v.elim
  | union A B ha hb => cases v <;> simp only [IsRoot, depth] <;> first | apply ha | apply hb
  | root A ha => cases v <;> simp [IsRoot, depth]

theorem ForestExpr.adj_depth (A : ForestExpr) {u v : A.Vertex} (h : A.Adj u v) :
    A.depth u + 1 = A.depth v ∨ A.depth v + 1 = A.depth u := by
  induction A with
  | empty => exact u.elim
  | union A B ha hb =>
    cases u <;> cases v <;> simp only [Adj, depth] at *
    · exact ha h
    · exact hb h
  | root A ha =>
    cases u with
    | none =>
      cases v with
      | none => contradiction
      | some v =>
        have hz := (A.isRoot_iff_depth_zero v).mp h
        simp [depth, hz]
    | some u =>
      cases v with
      | none =>
        have hz := (A.isRoot_iff_depth_zero u).mp h
        simp [depth, hz]
      | some v =>
        have hi := ha h
        simp only [depth]
        omega

theorem ForestExpr.lower_neighbor_unique (A : ForestExpr) (v u w : A.Vertex)
    (hu : A.Adj v u) (hdu : A.depth u ≤ A.depth v)
    (hw : A.Adj v w) (hdw : A.depth w ≤ A.depth v) : u = w := by
  induction A with
  | empty => exact v.elim
  | union A B ha hb =>
    cases v <;> cases u <;> cases w <;> simp only [Adj, depth] at *
    · exact congrArg Sum.inl (ha _ _ _ hu hdu hw hdw)
    · exact congrArg Sum.inr (hb _ _ _ hu hdu hw hdw)
  | root A ha =>
    cases v with
    | none => cases u <;> simp [Adj, depth] at hu hdu
    | some v =>
      cases u with
      | none =>
        cases w with
        | none => rfl
        | some w =>
          have hz := (A.isRoot_iff_depth_zero v).mp hu
          have hd := A.adj_depth hw
          simp only [depth] at hdw
          omega
      | some u =>
        cases w with
        | none =>
          have hz := (A.isRoot_iff_depth_zero v).mp hw
          have hd := A.adj_depth hu
          simp only [depth] at hdu
          omega
        | some w =>
          simp only [depth] at hdu hdw
          exact congrArg some (ha _ _ _ hu (by omega) hw (by omega))

/-- A graph with at most one non-increasing neighbor at each vertex is acyclic. -/
theorem isAcyclic_of_rank {V : Type*} (G : SimpleGraph V) (d : V → ℕ)
    (hu : ∀ v u w, G.Adj v u → d u ≤ d v → G.Adj v w → d w ≤ d v → u = w) :
    G.IsAcyclic := by
  classical
  intro v p hp
  have hn : p.support.toFinset.Nonempty := ⟨v, List.mem_toFinset.mpr p.start_mem_support⟩
  obtain ⟨m, hm, he⟩ := Finset.exists_mem_eq_sup p.support.toFinset hn d
  have hm' : m ∈ p.support := List.mem_toFinset.mp hm
  have hmax : ∀ w ∈ p.support, d w ≤ d m := by
    intro w hw
    rw [← he]
    exact Finset.le_sup (List.mem_toFinset.mpr hw)
  let q := p.rotate m hm'
  have hq : q.IsCycle := (SimpleGraph.Walk.isCycle_rotate hm').mpr hp
  have hs : q.snd ∈ p.support := (p.mem_support_rotate_iff m hm').mp (q.getVert_mem_support 1)
  have ht : q.penultimate ∈ p.support :=
    (p.mem_support_rotate_iff m hm').mp (q.getVert_mem_support (q.length - 1))
  exact hq.snd_ne_penultimate (hu m q.snd q.penultimate (q.adj_snd hq.not_nil)
    (hmax _ hs) (q.adj_penultimate hq.not_nil).symm (hmax _ ht))

theorem ForestExpr.graph_acyclic (A : ForestExpr) : A.graph.IsAcyclic :=
  isAcyclic_of_rank A.graph A.depth A.lower_neighbor_unique

def ForestExpr.leftHom (A B : ForestExpr) : A.graph →g (ForestExpr.union A B).graph where
  toFun := Sum.inl
  map_rel' := fun h => h

def ForestExpr.rightHom (A B : ForestExpr) : B.graph →g (ForestExpr.union A B).graph where
  toFun := Sum.inr
  map_rel' := fun h => h

def ForestExpr.someHom (A : ForestExpr) : A.graph →g (ForestExpr.root A).graph where
  toFun := some
  map_rel' := fun h => h

theorem ForestExpr.reachable_root (A : ForestExpr) (v : A.Vertex) :
    ∃ r, A.IsRoot r ∧ A.graph.Reachable v r := by
  induction A with
  | empty => exact v.elim
  | union A B ha hb =>
    cases v with
    | inl v =>
      obtain ⟨r, hr, hp⟩ := ha v
      exact ⟨.inl r, hr, hp.map (A.leftHom B)⟩
    | inr v =>
      obtain ⟨r, hr, hp⟩ := hb v
      exact ⟨.inr r, hr, hp.map (A.rightHom B)⟩
  | root A ha =>
    cases v with
    | none => exact ⟨none, trivial, SimpleGraph.Reachable.refl _⟩
    | some v =>
      obtain ⟨r, hr, hp⟩ := ha v
      have hadj : (ForestExpr.root A).graph.Adj (some r) none := hr
      exact ⟨none, trivial, (hp.map A.someHom).trans hadj.reachable⟩

theorem ForestExpr.root_graph_isTree (A : ForestExpr) : (ForestExpr.root A).graph.IsTree where
  isAcyclic := (ForestExpr.root A).graph_acyclic
  connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
    refine ⟨none, fun v => ?_⟩
    obtain ⟨r, hr, hp⟩ := (ForestExpr.root A).reachable_root v
    cases r with
    | none => exact hp.symm
    | some r => exact False.elim hr

/-- Every expression is realized by its actual graph, with precisely the designated roots. -/
theorem ForestExpr.realization (A : ForestExpr) :
    ∃ rs, ForestRealization A.graph univ rs A ∧ ∀ v, v ∈ rs ↔ A.IsRoot v := by
  induction A with
  | empty =>
    refine ⟨∅, ?_, fun v => v.elim⟩
    have he : (univ : Finset (ForestExpr.empty.Vertex)) = ∅ := by ext v; exact v.elim
    rw [he]
    exact .empty
  | union A B ha hb =>
    obtain ⟨ra, hA, hra⟩ := ha
    obtain ⟨rb, hB, hrb⟩ := hb
    let fa : A.Vertex ↪ (ForestExpr.union A B).Vertex := ⟨Sum.inl, Sum.inl_injective⟩
    let fb : B.Vertex ↪ (ForestExpr.union A B).Vertex := ⟨Sum.inr, Sum.inr_injective⟩
    have hA' := hA.map (H := (ForestExpr.union A B).graph) fa (fun _ _ => Iff.rfl)
    have hB' := hB.map (H := (ForestExpr.union A B).graph) fb (fun _ _ => Iff.rfl)
    have hd : Disjoint (univ.map fa) (univ.map fb) := by
      apply disjoint_left.mpr
      intro v hv hw
      obtain ⟨u, _, hu⟩ := mem_map.mp hv
      obtain ⟨w, _, hw⟩ := mem_map.mp hw
      have hh : Sum.inl u = Sum.inr w := hu.trans hw.symm
      cases hh
    have hs : Separated (ForestExpr.union A B).graph (univ.map fa) (univ.map fb) := by
      intro v hv w hw
      obtain ⟨v, _, rfl⟩ := mem_map.mp hv
      obtain ⟨w, _, rfl⟩ := mem_map.mp hw
      exact id
    have hu : univ.map fa ∪ univ.map fb = univ := by
      ext v
      cases v <;> simp [fa, fb, Finset.mem_map]
    refine ⟨ra.map fa ∪ rb.map fb, ?_, ?_⟩
    · rw [← hu]
      exact .union hd hs hA' hB'
    · intro v
      cases v <;> simp [fa, fb, Finset.mem_map, IsRoot, hra, hrb]
  | root A ha =>
    obtain ⟨rs, hA, hrs⟩ := ha
    let f : A.Vertex ↪ (ForestExpr.root A).Vertex := ⟨some, Option.some_injective _⟩
    have hA' := hA.map (H := (ForestExpr.root A).graph) f (fun _ _ => Iff.rfl)
    have hn : none ∉ univ.map f := by simp [f, Finset.mem_map]
    have he : ∀ w ∈ univ.map f, (ForestExpr.root A).graph.Adj none w ↔ w ∈ rs.map f := by
      intro w hw
      obtain ⟨v, _, rfl⟩ := mem_map.mp hw
      simpa [f, graph, Adj, Function.Embedding.coeFn_mk] using (hrs v).symm
    have hu : insert none (univ.map f) = univ := by
      ext v
      cases v <;> simp [f, Finset.mem_map]
    refine ⟨{none}, ?_, ?_⟩
    · rw [← hu]
      exact .root none hn he hA'
    · intro v
      cases v <;> simp [IsRoot]

end TerminalLogConcavity
