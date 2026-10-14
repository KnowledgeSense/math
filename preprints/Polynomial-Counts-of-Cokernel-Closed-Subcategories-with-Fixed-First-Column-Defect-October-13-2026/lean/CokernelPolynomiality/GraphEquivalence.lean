import CokernelPolynomiality.GraphConstruction
import CokernelPolynomiality.EmbeddingCount

namespace CokernelPolynomiality
noncomputable section
variable {i m : ℕ}

 theorem Code.toGraphModel_toCode (c : Code i m) (hc : c.IsAdmissible) :
    (c.toGraphModel hc).toCode = c := by
  let _ := codeOrder c.d
  apply Code.data_injective
  apply Prod.ext
  · funext j
    apply cutoff_unique
    intro t
    rw [(c.toGraphModel hc).d_cutoff, c.toGraphModel_alpha hc, c.toGraphModel_beta hc]
    change c.indexIso.symm (.exceptional j) < c.indexIso.symm (.regular t) ↔ _
    rw [c.indexIso.symm.lt_iff_lt]
    exact exceptional_lt_regular c.d j t
  · apply Prod.ext
    · funext j
      apply cutoff_unique
      intro t
      rw [(c.toGraphModel hc).y_cutoff, c.toGraphModel_alpha hc, c.toGraphModel_beta hc]
      change (codeGraph c.y c.epsilon).Adj (c.indexIso (c.vertexIndex (.exceptional j)))
        (c.indexIso (c.vertexIndex (.regular t))) ↔ _
      rw [c.indexIso_vertexIndex,c.indexIso_vertexIndex]
      exact Nat.lt_add_one_iff
    · ext j k
      change (c.toGraphModel hc).graph.Adj ((c.toGraphModel hc).alpha j)
        ((c.toGraphModel hc).alpha k) ↔ c.epsilon.Adj j k
      rw [c.toGraphModel_alpha hc,c.toGraphModel_alpha hc]
      change (codeGraph c.y c.epsilon).Adj (c.indexIso (c.vertexIndex (.exceptional j)))
        (c.indexIso (c.vertexIndex (.exceptional k))) ↔ _
      rw [c.indexIso_vertexIndex,c.indexIso_vertexIndex]
      rfl

 theorem GraphModel.graph_injective : Function.Injective (@GraphModel.graph i m) := by
  intro G H h
  cases G
  cases H
  cases h
  rfl

 instance : Finite (GraphModel i m) := Finite.of_injective _ GraphModel.graph_injective
 noncomputable instance : Fintype (GraphModel i m) := Fintype.ofFinite _

 theorem GraphModel.toCode_injective : Function.Injective (@GraphModel.toCode i m) := by
  intro G H h
  let _ := codeOrder G.toCode.d
  have hmono : StrictMono H.decode := by
    have hh := H.decode_strictMono
    rw [← h] at hh
    exact hh
  have hd : G.decode = H.decode :=
    (G.decode_strictMono.range_inj_of_wellFoundedLT hmono).mp (by
      rw [Set.range_eq_univ.mpr G.decode_surjective,Set.range_eq_univ.mpr H.decode_surjective])
  apply GraphModel.graph_injective
  ext u v
  obtain ⟨a,rfl⟩ := G.decode_surjective u
  obtain ⟨b,rfl⟩ := G.decode_surjective v
  have hg := congrArg (fun J : SimpleGraph (Vertex i m) => J.Adj a b) G.decode_comap
  have hh := congrArg (fun J : SimpleGraph (Vertex i m) => J.Adj a b) H.decode_comap
  change G.graph.Adj (G.decode a) (G.decode b) = _ at hg
  change H.graph.Adj (H.decode a) (H.decode b) = _ at hh
  rw [hg,hd,hh,h]

 def graphCodeEquiv (i m : ℕ) : GraphModel i m ≃ AdmissibleCode i m where
  toFun G := ⟨G.toCode,G.toCode_admissible⟩
  invFun c := c.val.toGraphModel c.property
  left_inv G := GraphModel.toCode_injective (G.toCode.toGraphModel_toCode G.toCode_admissible)
  right_inv c := Subtype.ext (c.val.toGraphModel_toCode c.property)

 theorem graphModel_card_formula (i m : ℕ) :
    Fintype.card (GraphModel i m) =
      ∑ q : Fin (2*i+1), templateCount i q * m.choose q := by
  classical
  rw [Fintype.card_congr (graphCodeEquiv i m)]
  exact codeCount_binomial_formula i m

end
end CokernelPolynomiality
