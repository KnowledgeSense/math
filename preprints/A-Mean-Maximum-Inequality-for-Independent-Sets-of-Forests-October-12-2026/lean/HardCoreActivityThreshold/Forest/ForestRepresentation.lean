import HardCoreActivityThreshold.Forest.LeafInsertion
import HardCoreActivityThreshold.ForestLeaves
import Mathlib.Logic.Equiv.Option

namespace HardCoreActivityThreshold.Forest

 def ForestExpr.addIsolated (A : ForestExpr) : ForestExpr := .union A (.root .empty)

 def ForestExpr.isolatedEquiv (A : ForestExpr) : A.addIsolated.Vertex ≃ Option A.Vertex where
  toFun := fun x => match x with
    | .inl a => some a
    | .inr none => none
    | .inr (some a) => a.elim
  invFun := fun x => match x with
    | none => .inr none
    | some a => .inl a
  left_inv := by intro x; rcases x with a|(_|a); rfl; rfl; exact a.elim
  right_inv := by intro x; cases x <;> rfl

 theorem ForestExpr.isolated_adj (A : ForestExpr) (x y : Option A.Vertex) :
    A.addIsolated.Adj (A.isolatedEquiv.symm x) (A.isolatedEquiv.symm y) ↔
      (match x,y with | some u,some v => A.Adj u v | _,_ => False) := by
  cases x <;> cases y <;> rfl

variable {V : Type*} [DecidableEq V]

noncomputable def leafExtensionEquiv (A : ForestExpr) (G : SimpleGraph V) (v b : V)
    (hb : b≠v) (e : A.graph ≃g G.induce {w : V | w≠v}) :
    (A.insertLeaf (e.symm ⟨b,hb⟩)).Vertex ≃ V :=
  (A.leafEquiv (e.symm ⟨b,hb⟩)).trans
    ((Equiv.optionCongr e.toEquiv).trans (Equiv.optionSubtypeNe v))

noncomputable def leafExtensionIso (A : ForestExpr) (G : SimpleGraph V) (v b : V)
    (hb : b≠v) (hv : ∀w,G.Adj v w ↔ w=b)
    (e : A.graph ≃g G.induce {w : V | w≠v}) :
    (A.insertLeaf (e.symm ⟨b,hb⟩)).graph ≃g G where
  toEquiv := leafExtensionEquiv A G v b hb e
  map_rel_iff' := by
    intro x y
    obtain ⟨x,rfl⟩ := (A.leafEquiv (e.symm ⟨b,hb⟩)).symm.surjective x
    obtain ⟨y,rfl⟩ := (A.leafEquiv (e.symm ⟨b,hb⟩)).symm.surjective y
    simp only [leafExtensionEquiv,Equiv.trans_apply,Equiv.apply_symm_apply]
    change G.Adj _ _ ↔ (A.insertLeaf _).Adj (A.leafEncode _ x) (A.leafEncode _ y)
    rw [A.leafEncode_adj]
    cases x with
    | none =>
      cases y with
      | none => simp [ForestExpr.leafAdj]
      | some y =>
        change G.Adj v (e y).val ↔ e.symm ⟨b,hb⟩=y
        rw [hv]
        calc
          (e y).val=b ↔ e y=⟨b,hb⟩ := ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩
          _ ↔ y=e.symm ⟨b,hb⟩ := e.toEquiv.eq_symm_apply.symm
          _ ↔ e.symm ⟨b,hb⟩=y := eq_comm
    | some x =>
      cases y with
      | none =>
        change G.Adj (e x).val v ↔ x=e.symm ⟨b,hb⟩
        rw [G.adj_comm,hv]
        exact (show (e x).val=b ↔ e x=⟨b,hb⟩ from ⟨fun h => Subtype.ext h,fun h => congrArg Subtype.val h⟩).trans e.toEquiv.eq_symm_apply.symm
      | some y =>
        exact e.map_rel_iff

noncomputable def isolatedExtensionIso (A : ForestExpr) (G : SimpleGraph V) (v : V)
    (hv : ∀w,¬G.Adj v w) (e : A.graph ≃g G.induce {w : V | w≠v}) :
    A.addIsolated.graph ≃g G where
  toEquiv := A.isolatedEquiv.trans ((Equiv.optionCongr e.toEquiv).trans (Equiv.optionSubtypeNe v))
  map_rel_iff' := by
    intro x y
    obtain ⟨x,rfl⟩ := A.isolatedEquiv.symm.surjective x
    obtain ⟨y,rfl⟩ := A.isolatedEquiv.symm.surjective y
    simp only [Equiv.trans_apply,Equiv.apply_symm_apply]
    change G.Adj _ _ ↔ A.addIsolated.Adj (A.isolatedEquiv.symm x) (A.isolatedEquiv.symm y)
    rw [A.isolated_adj]
    cases x with
    | none =>
      cases y with
      | none => simp
      | some y => exact iff_false_intro (hv (e y).val)
    | some x =>
      cases y with
      | none => exact iff_false_intro (fun h => hv (e x).val h.symm)
      | some y => exact e.map_rel_iff

 theorem finite_forest_representation [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    ∃A : ForestExpr,Nonempty (A.graph ≃g G) := by
  classical
  generalize hn : Fintype.card V=n
  induction n using Nat.strong_induction_on generalizing V with
  | h n ih =>
    by_cases he : IsEmpty V
    · let _ := he
      refine ⟨.empty,⟨{ toEquiv := Equiv.equivOfIsEmpty _ _ , map_rel_iff' := ?_ }⟩⟩
      intro x _
      exact x.elim
    · have : Nonempty V := not_isEmpty_iff.mp he
      obtain ⟨v,hv⟩ := forest_exists_leaf G hG
      let W := {w : V // w≠v}
      have hlt : Fintype.card W<n := by rw [←hn]; exact card_delete_vertex_lt v
      obtain ⟨A,⟨e⟩⟩ := ih (Fintype.card W) hlt (G.induce {w : V | w≠v})
        (forest_delete_vertex_acyclic G hG v) rfl
      by_cases hb : ∃b,G.Adj v b
      · obtain ⟨b,hb⟩ := hb
        have hbne : b≠v := by intro heq; subst b; exact G.loopless.irrefl v hb
        have hiff : ∀w,G.Adj v w ↔ w=b := by
          intro w
          exact ⟨fun h => hv w b h hb,fun h => h.symm ▸ hb⟩
        exact ⟨A.insertLeaf (e.symm ⟨b,hbne⟩),⟨leafExtensionIso A G v b hbne hiff e⟩⟩
      · exact ⟨A.addIsolated,⟨isolatedExtensionIso A G v (by simpa using hb) e⟩⟩

end HardCoreActivityThreshold.Forest
