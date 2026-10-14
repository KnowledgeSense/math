import MainTheorems.Corona.Basic
import Mathlib.Data.Finset.Sum

namespace ResearchMain.Corona

open Classical

variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

def corona (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V ⊕ (V × W)) where
  Adj x y := match x, y with
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inl u, Sum.inr (v, _) => u = v
    | Sum.inr (u, _), Sum.inl v => u = v
    | Sum.inr (u, w), Sum.inr (v, z) => u = v ∧ H.Adj w z
  symm := by
    constructor
    intro x y h
    rcases x with u | ⟨u, w⟩ <;> rcases y with v | ⟨v, z⟩
    · exact G.adj_symm h
    · exact h.symm
    · exact h.symm
    · exact ⟨h.1.symm, H.adj_symm h.2⟩
  loopless := by
    constructor
    intro x h
    rcases x with u | ⟨u, w⟩
    · exact G.irrefl h
    · exact H.irrefl h.2

noncomputable def attachmentFiber (R : Finset (V ⊕ (V × W))) (v : V) : Finset W :=
  Finset.univ.filter (fun w => (v, w) ∈ R.toRight)

omit [Fintype V] in
theorem mem_attachmentFiber (R : Finset (V ⊕ (V × W))) (v : V) (w : W) :
    w ∈ attachmentFiber R v ↔ Sum.inr (v, w) ∈ R := by
  simp only [attachmentFiber, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_toRight]

omit [Fintype V] in
theorem corona_independent (G : SimpleGraph V) (H : SimpleGraph W) (R : Finset (V ⊕ (V × W))) :
    (corona G H).IsIndepSet (R : Set (V ⊕ (V × W))) ↔
      G.IsIndepSet (R.toLeft : Set V) ∧
      (∀ v, H.IsIndepSet (attachmentFiber R v : Set W)) ∧
      ∀ v ∈ R.toLeft, attachmentFiber R v = ∅ := by
  simp only [independent_iff]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro u hu v hv
      exact h (Sum.inl u) (Finset.mem_toLeft.mp hu) (Sum.inl v) (Finset.mem_toLeft.mp hv)
    · intro v w hw z hz hadj
      exact h (Sum.inr (v, w)) ((mem_attachmentFiber R v w).mp hw)
        (Sum.inr (v, z)) ((mem_attachmentFiber R v z).mp hz) ⟨rfl, hadj⟩
    · intro v hv
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact h (Sum.inl v) (Finset.mem_toLeft.mp hv) (Sum.inr (v, w))
        ((mem_attachmentFiber R v w).mp hw) rfl
  · rintro ⟨hG, hH, hdisj⟩ x hx y hy hadj
    rcases x with u | ⟨u, w⟩ <;> rcases y with v | ⟨v, z⟩
    · exact hG u (Finset.mem_toLeft.mpr hx) v (Finset.mem_toLeft.mpr hy) hadj
    · change u = v at hadj
      subst v
      have hz := (mem_attachmentFiber R u z).mpr hy
      rw [hdisj u (Finset.mem_toLeft.mpr hx)] at hz
      exact Finset.notMem_empty z hz
    · change u = v at hadj
      subst v
      have hw := (mem_attachmentFiber R u w).mpr hx
      rw [hdisj u (Finset.mem_toLeft.mpr hy)] at hw
      exact Finset.notMem_empty w hw
    · change u = v ∧ H.Adj w z at hadj
      obtain ⟨rfl, hwz⟩ := hadj
      exact hH u w ((mem_attachmentFiber R u w).mpr hx) z ((mem_attachmentFiber R u z).mpr hy) hwz

end ResearchMain.Corona
