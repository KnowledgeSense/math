import CokernelPolynomiality.GraphModels

namespace CokernelPolynomiality
noncomputable section

variable {i m : ℕ}

 theorem GraphModel.decode_strictMono (G : GraphModel i m) :
    let _ := codeOrder G.toCode.d
    StrictMono G.decode := by
  let _ := codeOrder G.toCode.d
  change ∀ ⦃u v : Vertex i m⦄, u < v → G.decode u < G.decode v
  intro u v huv
  cases u with
  | root =>
    cases v with
    | root => exact False.elim ((lt_irrefl _) huv)
    | exceptional j => exact G.alpha_pos j
    | regular t => exact G.beta_pos t
  | exceptional j =>
    cases v with
    | root => exact False.elim (not_lt_of_gt (root_lt_exceptional _ j) huv)
    | exceptional k =>
      exact G.alpha.strictMono ((exceptional_lt_exceptional _ G.toCode.monotone_d j k).mp huv)
    | regular t => exact (G.d_cutoff j t).mp ((exceptional_lt_regular _ j t).mp huv)
  | regular t =>
    cases v with
    | root => exact False.elim (not_lt_of_gt (root_lt_regular _ t) huv)
    | exceptional j =>
      have htj := (regular_lt_exceptional _ t j).mp huv
      have hnot : ¬G.alpha j < G.beta t := fun h => (Nat.not_le_of_gt htj) ((G.d_cutoff j t).mpr h)
      exact lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm (G.alpha_beta_ne j t))
    | regular s => exact G.beta.strictMono ((regular_lt_regular _ t s).mp huv)

 theorem GraphModel.decode_comap (G : GraphModel i m) :
    G.graph.comap G.decode = codeGraph G.toCode.y G.toCode.epsilon := by
  ext u v
  cases u with
  | root =>
    cases v with
    | root => simp [GraphModel.decode,codeGraph,SimpleGraph.comap]
    | exceptional j =>
      change G.graph.Adj 0 (G.alpha j) ↔ False
      exact iff_false_intro (G.alpha_properties j).2
    | regular t =>
      change G.graph.Adj 0 (G.beta t) ↔ True
      exact iff_true_intro (G.beta_adj t)
  | exceptional j =>
    cases v with
    | root =>
      change G.graph.Adj (G.alpha j) 0 ↔ False
      exact iff_false_intro (fun h => (G.alpha_properties j).2 h.symm)
    | exceptional k => rfl
    | regular t =>
      change G.graph.Adj (G.alpha j) (G.beta t) ↔ (G.toCode.y j).val < t.val+1
      simpa only [Nat.lt_add_one_iff] using (G.y_cutoff j t).symm
  | regular t =>
    cases v with
    | root =>
      change G.graph.Adj (G.beta t) 0 ↔ True
      exact iff_true_intro (G.beta_adj t).symm
    | exceptional j =>
      change G.graph.Adj (G.beta t) (G.alpha j) ↔ (G.toCode.y j).val < t.val+1
      rw [SimpleGraph.adj_comm]
      simpa only [Nat.lt_add_one_iff] using (G.y_cutoff j t).symm
    | regular s =>
      change G.graph.Adj (G.beta t) (G.beta s) ↔ t ≠ s
      constructor
      · intro h hts
        exact h.ne (congrArg G.beta hts)
      · intro hts
        rcases lt_or_gt_of_ne hts with hts | hst
        · exact root_neighbors_adj _ G.admissible 0 (G.beta t) (G.beta s)
            (G.beta_pos t) (G.beta.strictMono hts) (G.beta_adj t) (G.beta_adj s)
        · exact (root_neighbors_adj _ G.admissible 0 (G.beta s) (G.beta t)
            (G.beta_pos s) (G.beta.strictMono hst) (G.beta_adj s) (G.beta_adj t)).symm

 theorem GraphModel.toCode_admissible (G : GraphModel i m) : G.toCode.IsAdmissible := by
  let _ := codeOrder G.toCode.d
  have hh := admissible_comap _ G.admissible _ G.decode_strictMono
  rw [G.decode_comap] at hh
  exact hh

 def GraphModel.decodeOrderIso (G : GraphModel i m) :
    let _ := codeOrder G.toCode.d
    Vertex i m ≃o Fin (i+m+1) := by
  let _ := codeOrder G.toCode.d
  exact {
    toEquiv := Equiv.ofBijective G.decode ⟨G.decode_injective,G.decode_surjective⟩
    map_rel_iff' := G.decode_strictMono.le_iff_le }

end
end CokernelPolynomiality
