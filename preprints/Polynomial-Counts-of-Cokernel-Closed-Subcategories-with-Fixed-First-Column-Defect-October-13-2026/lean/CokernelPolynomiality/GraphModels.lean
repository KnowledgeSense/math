import CokernelPolynomiality.Cutoffs
import CokernelPolynomiality.Factorization

namespace CokernelPolynomiality
noncomputable section

 def rootNeighbors {n : ℕ} (G : SimpleGraph (Fin (n+1))) : Finset (Fin (n+1)) := by
  classical
  exact Finset.univ.filter (G.Adj 0)

 def rootExceptions {n : ℕ} (G : SimpleGraph (Fin (n+1))) : Finset (Fin (n+1)) := by
  classical
  exact Finset.univ.filter (fun v => v ≠ 0 ∧ ¬G.Adj 0 v)

 theorem mem_rootNeighbors {n : ℕ} (G : SimpleGraph (Fin (n+1))) (v : Fin (n+1)) :
    v ∈ rootNeighbors G ↔ G.Adj 0 v := by
  classical
  simp [rootNeighbors]

 theorem mem_rootExceptions {n : ℕ} (G : SimpleGraph (Fin (n+1))) (v : Fin (n+1)) :
    v ∈ rootExceptions G ↔ v ≠ 0 ∧ ¬G.Adj 0 v := by
  classical
  simp [rootExceptions]

 theorem root_partition {n : ℕ} (G : SimpleGraph (Fin (n+1))) :
    rootExceptions G ∪ rootNeighbors G = Finset.univ.erase 0 := by
  classical
  ext v
  by_cases hv : v = 0 <;> by_cases hg : G.Adj 0 v <;>
    simp_all [mem_rootExceptions,mem_rootNeighbors]

 theorem root_partition_disjoint {n : ℕ} (G : SimpleGraph (Fin (n+1))) :
    Disjoint (rootExceptions G) (rootNeighbors G) := by
  classical
  apply Finset.disjoint_left.mpr
  intro v hv hn
  exact ((mem_rootExceptions G v).mp hv).2 ((mem_rootNeighbors G v).mp hn)

 structure GraphModel (i m : ℕ) where
  graph : SimpleGraph (Fin (i+m+1))
  admissible : Admissible graph
  neighbors_card : (rootNeighbors graph).card = m

 variable {i m : ℕ}

 theorem GraphModel.exceptions_card (G : GraphModel i m) :
    (rootExceptions G.graph).card = i := by
  have hh := congrArg Finset.card (root_partition G.graph)
  rw [Finset.card_union_of_disjoint (root_partition_disjoint _),G.neighbors_card] at hh
  simp at hh
  omega

 def GraphModel.alpha (G : GraphModel i m) : Fin i ↪o Fin (i+m+1) :=
  (rootExceptions G.graph).orderEmbOfFin G.exceptions_card

 def GraphModel.beta (G : GraphModel i m) : Fin m ↪o Fin (i+m+1) :=
  (rootNeighbors G.graph).orderEmbOfFin G.neighbors_card

 theorem GraphModel.alpha_properties (G : GraphModel i m) (j : Fin i) :
    G.alpha j ≠ 0 ∧ ¬G.graph.Adj 0 (G.alpha j) :=
  (mem_rootExceptions _ _).mp (Finset.orderEmbOfFin_mem _ _ j)

 theorem GraphModel.beta_adj (G : GraphModel i m) (t : Fin m) :
    G.graph.Adj 0 (G.beta t) :=
  (mem_rootNeighbors _ _).mp (Finset.orderEmbOfFin_mem _ _ t)

 theorem GraphModel.alpha_beta_ne (G : GraphModel i m) (j : Fin i) (t : Fin m) :
    G.alpha j ≠ G.beta t := by
  intro h
  exact (G.alpha_properties j).2 (h ▸ G.beta_adj t)

 theorem GraphModel.alpha_pos (G : GraphModel i m) (j : Fin i) : 0 < G.alpha j :=
  Fin.pos_iff_ne_zero.mpr (G.alpha_properties j).1

 theorem GraphModel.beta_pos (G : GraphModel i m) (t : Fin m) : 0 < G.beta t :=
  Fin.pos_iff_ne_zero.mpr (G.beta_adj t).ne.symm

 def GraphModel.decode (G : GraphModel i m) : Vertex i m → Fin (i+m+1)
  | .root => 0
  | .exceptional j => G.alpha j
  | .regular t => G.beta t

 theorem GraphModel.decode_injective (G : GraphModel i m) : Function.Injective G.decode := by
  intro u v huv
  cases u with
  | root =>
    cases v with
    | root => rfl
    | exceptional j => exact False.elim ((G.alpha_properties j).1 huv.symm)
    | regular t => exact False.elim ((G.beta_adj t).ne huv)
  | exceptional j =>
    cases v with
    | root => exact False.elim ((G.alpha_properties j).1 huv)
    | exceptional k => exact congrArg Vertex.exceptional (G.alpha.injective huv)
    | regular t => exact False.elim (G.alpha_beta_ne j t huv)
  | regular t =>
    cases v with
    | root => exact False.elim ((G.beta_adj t).ne huv.symm)
    | exceptional j => exact False.elim (G.alpha_beta_ne j t huv.symm)
    | regular s => exact congrArg Vertex.regular (G.beta.injective huv)

 theorem GraphModel.decode_surjective (G : GraphModel i m) : Function.Surjective G.decode := by
  intro v
  by_cases hv : v = 0
  · exact ⟨.root,hv.symm⟩
  · by_cases hg : G.graph.Adj 0 v
    · have hm := (mem_rootNeighbors G.graph v).mpr hg
      let t := ((rootNeighbors G.graph).orderIsoOfFin G.neighbors_card).symm ⟨v,hm⟩
      refine ⟨.regular t,?_⟩
      change (((rootNeighbors G.graph).orderIsoOfFin G.neighbors_card) t).val = v
      simp [t]
    · have hm := (mem_rootExceptions G.graph v).mpr ⟨hv,hg⟩
      let j := ((rootExceptions G.graph).orderIsoOfFin G.exceptions_card).symm ⟨v,hm⟩
      refine ⟨.exceptional j,?_⟩
      change (((rootExceptions G.graph).orderIsoOfFin G.exceptions_card) j).val = v
      simp [j]

 def GraphModel.toCode (G : GraphModel i m) : Code i m where
  d j := firstHit (fun t => G.alpha j < G.beta t)
  y j := firstHit (fun t => G.graph.Adj (G.alpha j) (G.beta t))
  epsilon := G.graph.comap G.alpha
  monotone_d := by
    intro j k hjk
    exact firstHit_antitone _ _ (fun t ht => lt_of_le_of_lt (G.alpha.monotone hjk) ht)

 theorem GraphModel.d_cutoff (G : GraphModel i m) (j : Fin i) (t : Fin m) :
    (G.toCode.d j).val ≤ t.val ↔ G.alpha j < G.beta t :=
  firstHit_le_iff _ (fun _ _ hst h => lt_of_lt_of_le h (G.beta.monotone hst)) t

 theorem GraphModel.y_cutoff (G : GraphModel i m) (j : Fin i) (t : Fin m) :
    (G.toCode.y j).val ≤ t.val ↔ G.graph.Adj (G.alpha j) (G.beta t) := by
  apply firstHit_le_iff
  intro s t hst hs
  rcases lt_or_eq_of_le hst with hst | rfl
  · exact regular_neighbors_final _ G.admissible 0 (G.alpha j) (G.beta s) (G.beta t)
      (G.alpha_pos j) (G.beta_pos s) (G.beta.strictMono hst)
      (G.beta_adj s) (G.beta_adj t) hs (G.alpha_beta_ne j t)
  · exact hs

end
end CokernelPolynomiality
