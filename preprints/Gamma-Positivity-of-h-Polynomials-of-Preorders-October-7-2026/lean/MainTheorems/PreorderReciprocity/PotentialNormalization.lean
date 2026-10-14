import MainTheorems.PreorderReciprocity.BasisExtension

namespace ResearchMain.PreorderReciprocity

open PreorderGamma

variable {L R : Type*} [Fintype L] [Fintype R]
variable {r : L → R → Prop} {d : L → ℕ} {s : R → ℕ}

theorem transportWalkCost_of_tight (p : NaturalTransport r d s)
    (rowPotential : L → ℤ) (columnPotential : R → ℤ)
    (htight : ∀ a b, 0 < p.flow a b →
      (transportEdgeWeight s a b : ℤ) + rowPotential a = columnPotential b)
    {u v : L ⊕ R} (w : (transportSupportGraph p).Walk u v) :
    transportWalkCost p w =
      Sum.elim rowPotential columnPotential v - Sum.elim rowPotential columnPotential u := by
  induction w with
  | nil => simp
  | @cons u v w h q ih =>
    rw [transportWalkCost_cons]
    cases u with
    | inl a =>
      cases v with
      | inl a' => exact False.elim h
      | inr b =>
        have heq := htight a b h
        simp only [transportArcCost, Sum.elim_inl, Sum.elim_inr] at ih ⊢
        linarith
    | inr b =>
      cases v with
      | inl a =>
        have heq := htight a b h
        simp only [transportArcCost, Sum.elim_inl, Sum.elim_inr] at ih ⊢
        linarith
      | inr b' => exact False.elim h

theorem transportTreeVertexPotential_of_tight (p : NaturalTransport r d s)
    (htree : (transportSupportGraph p).IsTree)
    (rowPotential : L → ℤ) (columnPotential : R → ℤ)
    (htight : ∀ a b, 0 < p.flow a b →
      (transportEdgeWeight s a b : ℤ) + rowPotential a = columnPotential b)
    (root v : L ⊕ R) :
    transportTreeVertexPotential p htree root v =
      Sum.elim rowPotential columnPotential v - Sum.elim rowPotential columnPotential root :=
  transportWalkCost_of_tight p rowPotential columnPotential htight (supportTreePath p htree root v)

end ResearchMain.PreorderReciprocity
