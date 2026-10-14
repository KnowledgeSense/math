import MainTheorems.Tuza.CompletePacking
import MainTheorems.Tuza.FanSupport
import MainTheorems.Tuza.CoChain

namespace ResearchMain.Tuza

def CliqueSupport {I V : Type*} [DecidableEq V] (a : I → V) (P : Finset (Finset V)) : Prop :=
  ∀ t ∈ P, ∀ e ∈ triangleEdges t, ∃ i j, e = s(a i, a j)

theorem exists_clique_packing {V : Type*} [DecidableEq V] {G : SimpleGraph V} {n : ℕ}
    (a : Fin n ↪ V) (ha : ∀ i j, i ≠ j → G.Adj (a i) (a j)) :
    ∃ P : Finset (Finset V), Packing G P ∧ P.card = completeCount n ∧ CliqueSupport a P := by
  classical
  obtain ⟨Q, hQ, hc⟩ := complete_packing n
  let F : PackingFamily (⊤ : SimpleGraph (Fin n)) Q := {
    triangle := Subtype.val
    clique := fun t => hQ.1 t.val t.property
    disjoint := fun t u htu => hQ.2 t.property u.property (fun h => htu (Subtype.ext h)) }
  let M : PackingFamily G Q := F.map a ha
  refine ⟨M.carrier, M.packing, M.card.trans ((Fintype.card_coe Q).trans hc), ?_⟩
  intro t ht e he
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ht
  change e ∈ triangleEdges (q.val.map a) at he
  rw [triangleEdges_map] at he
  obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp he
  induction z using Sym2.inductionOn with
  | hf i j => exact ⟨i, j, rfl⟩

theorem clique_support_disjoint {V : Type*} [DecidableEq V] {p q : ℕ}
    {a : Fin p ↪ V} {b : Fin q ↪ V} (hd : ∀ i j, a i ≠ b j)
    {P Q : Finset (Finset V)} (hP : CliqueSupport a P) (hQ : CliqueSupport b Q)
    {t u : Finset V} (ht : t ∈ P) (hu : u ∈ Q) :
    Disjoint (triangleEdges t) (triangleEdges u) := by
  apply Finset.disjoint_left.mpr
  intro e he he'
  obtain ⟨i, j, hij⟩ := hP t ht e he
  obtain ⟨k, l, hkl⟩ := hQ u hu e he'
  rcases Sym2.eq_iff.mp (hij.symm.trans hkl) with h | h
  · exact hd i k h.1
  · exact hd i l h.1

theorem exists_two_clique_packings {V : Type*} [DecidableEq V] {G : SimpleGraph V} {p q : ℕ}
    (a : Fin p ↪ V) (b : Fin q ↪ V) (hd : ∀ i j, a i ≠ b j)
    (ha : ∀ i j, i ≠ j → G.Adj (a i) (a j))
    (hb : ∀ i j, i ≠ j → G.Adj (b i) (b j)) :
    ∃ P : Finset (Finset V), Packing G P ∧ P.card = completeCount p + completeCount q := by
  obtain ⟨P, hP, hPc, hPs⟩ := exists_clique_packing a ha
  obtain ⟨Q, hQ, hQc, hQs⟩ := exists_clique_packing b hb
  have hcross : ∀ t ∈ P, ∀ u ∈ Q, Disjoint (triangleEdges t) (triangleEdges u) :=
    fun _ ht _ hu => clique_support_disjoint hd hPs hQs ht hu
  refine ⟨P ∪ Q, hP.union hQ hcross, ?_⟩
  rw [hP.card_union hcross, hPc, hQc]

theorem FerrersProfile.complete_bound {a b : ℕ} (d : FerrersProfile a b) :
    completeCount a + completeCount b ≤ packingNumber d.graph := by
  obtain ⟨P, hP, hc⟩ := exists_two_clique_packings (G := d.graph)
    Function.Embedding.inl Function.Embedding.inr
    (fun _ _ => Sum.inl_ne_inr) (fun _ _ h => h) (fun _ _ h => h)
  rw [← hc]
  exact packing_le_number (G := d.graph) hP

end ResearchMain.Tuza
