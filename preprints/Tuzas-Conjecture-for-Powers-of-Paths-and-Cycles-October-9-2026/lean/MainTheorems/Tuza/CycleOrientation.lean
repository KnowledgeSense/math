import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic

namespace ResearchMain.Tuza

variable {V : Type*} {G : SimpleGraph V}

theorem rotate_twice_ne {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    finRotate n (finRotate n i) ≠ i := by
  let _ : NeZero n := ⟨by omega⟩
  simp only [finRotate_apply]
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_add] at hv
  have h1 : (1 : Fin n).val = 1 := by
    change 1 % n = 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [h1] at hv
  have hi := i.isLt
  have hmod := Nat.mod_lt (i.val + 1) (by omega : 0 < n)
  by_cases hlast : i.val + 1 = n
  · rw [hlast, Nat.mod_self, zero_add, Nat.mod_eq_of_lt (by omega : 1 < n)] at hv
    omega
  · rw [Nat.mod_eq_of_lt (by omega : i.val + 1 < n)] at hv
    by_cases hsecond : i.val + 2 = n
    · have he : i.val + 1 + 1 = n := by omega
      rw [he, Nat.mod_self] at hv
      omega
    · rw [Nat.mod_eq_of_lt (by omega : i.val + 1 + 1 < n)] at hv
      omega

theorem cycle_coordinates {v : V} (p : G.Walk v v) (hp : p.IsCycle)
    {c : G.ConnectedComponent} (hc : p.toSubgraph.verts = c.supp) :
    ∃ e : Fin p.length ≃ c.supp,
      ∀ i, G.Adj (e i).val (e (finRotate p.length i)).val := by
  classical
  let f : Fin p.length → c.supp := fun i => ⟨p.getVert i.val, by
    rw [← hc, SimpleGraph.Walk.mem_verts_toSubgraph]
    exact p.getVert_mem_support i.val⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Fin.ext
      exact hp.getVert_injOn' (by simp; omega) (by simp; omega) (congrArg Subtype.val hij)
    · intro x
      have hx : x.val ∈ p.support := by
        rw [← SimpleGraph.Walk.mem_verts_toSubgraph, hc]
        exact x.property
      obtain ⟨k, hk, hkl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hx
      by_cases hlt : k < p.length
      · exact ⟨⟨k, hlt⟩, Subtype.ext hk⟩
      · have he : k = p.length := by omega
        refine ⟨⟨0, by have := hp.three_le_length; omega⟩, Subtype.ext ?_⟩
        simpa [f, he] using hk
  refine ⟨Equiv.ofBijective f hf, ?_⟩
  intro i
  change G.Adj (p.getVert i.val) (p.getVert (finRotate p.length i).val)
  have hn := hp.three_le_length
  let _ : NeZero p.length := ⟨by omega⟩
  have h1 : (1 : Fin p.length).val = 1 := by
    change 1 % p.length = 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [finRotate_apply, Fin.val_add, h1]
  by_cases hlast : i.val + 1 = p.length
  · rw [hlast, Nat.mod_self]
    simpa [hlast] using p.adj_getVert_succ i.isLt
  · rw [Nat.mod_eq_of_lt (by omega : i.val + 1 < p.length)]
    exact p.adj_getVert_succ i.isLt

structure CycleOrientation (G : SimpleGraph V) where
  successor : V ≃ V
  adjacent : ∀ x, G.Adj x (successor x)
  noReverse : ∀ x, successor (successor x) ≠ x
  exhaustive : ∀ x y, G.Adj x y → successor x = y ∨ successor y = x

theorem exists_cycle_orientation [Finite V] (hG : G.IsCycles)
    (hn : ∀ x, (G.neighborSet x).Nonempty) : Nonempty (CycleOrientation G) := by
  classical
  have hcycle (c : G.ConnectedComponent) :
      ∃ n : ℕ, 3 ≤ n ∧ ∃ e : Fin n ≃ c.supp,
        ∀ i, G.Adj (e i).val (e (finRotate n i)).val := by
    obtain ⟨v, hv⟩ := c.nonempty_supp
    obtain ⟨p, hp, hc⟩ := hG.exists_cycle_toSubgraph_verts_eq_connectedComponentSupp hv (hn v)
    obtain ⟨e, he⟩ := cycle_coordinates p hp hc
    exact ⟨p.length, hp.three_le_length, e, he⟩
  choose n hsize e hadj using hcycle
  let E : (Σ c : G.ConnectedComponent, Fin (n c)) ≃ V :=
    (Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv G.connectedComponentMk)
  let R : (Σ c : G.ConnectedComponent, Fin (n c)) ≃
      (Σ c : G.ConnectedComponent, Fin (n c)) := Equiv.sigmaCongrRight (fun c => finRotate (n c))
  let S : V ≃ V := E.symm.trans (R.trans E)
  have hS (z : Σ c : G.ConnectedComponent, Fin (n c)) : S (E z) = E (R z) := by
    simp [S]
  have hAdj (x : V) : G.Adj x (S x) := by
    obtain ⟨z, rfl⟩ := E.surjective x
    rw [hS]
    exact hadj z.1 z.2
  have hNo (x : V) : S (S x) ≠ x := by
    obtain ⟨z, rfl⟩ := E.surjective x
    rw [hS, hS]
    intro h
    have hz := E.injective h
    have hi : finRotate (n z.1) (finRotate (n z.1) z.2) = z.2 := by
      change Sigma.mk z.1 (finRotate (n z.1) (finRotate (n z.1) z.2)) = z at hz
      exact eq_of_heq (Sigma.mk.inj_iff.mp hz).2
    exact rotate_twice_ne (hsize z.1) z.2 hi
  refine ⟨⟨S, hAdj, hNo, ?_⟩⟩
  intro x y hxy
  by_cases h : S x = y
  · exact Or.inl h
  · right
    obtain ⟨w, hw, huniq⟩ := hG.existsUnique_ne_adj (hAdj x)
    have hp : S x ≠ S.symm x := by
      intro he
      exact hNo x (by rw [he, S.apply_symm_apply])
    have hy := huniq y ⟨h, hxy⟩
    have hpred := huniq (S.symm x) ⟨hp, by simpa using (hAdj (S.symm x)).symm⟩
    rw [← hpred] at hy
    rw [hy, S.apply_symm_apply]

end ResearchMain.Tuza
