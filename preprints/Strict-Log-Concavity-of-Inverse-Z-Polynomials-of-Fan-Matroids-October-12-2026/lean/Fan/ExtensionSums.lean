import Fan.AppendConfigurations
import Fan.ConfigurationBounds

namespace Fan
open Finset
open scoped Classical


theorem sum_allowed {R : Type*} [AddCommMonoid R] {n : ℕ} (p : Pair (n+1))
    (f : {bc : Bool × Bool // Allowed p bc.1 bc.2} → R) :
    (∑ x, f x)=f ⟨(false,false),allowed_false_false p⟩ +
      if h : Fin.last n∈p.1 then f ⟨(true,true),(allowed_true_true p).mpr h⟩
      else f ⟨(true,false),(allowed_true_false p).mpr h⟩+
        f ⟨(false,true),(allowed_false_true p).mpr h⟩ := by
  classical
  by_cases h : Fin.last n∈p.1
  · rw [dite_eq_left h]
    have hu : (univ : Finset {bc : Bool × Bool // Allowed p bc.1 bc.2}) =
        {⟨(false,false),allowed_false_false p⟩,⟨(true,true),(allowed_true_true p).mpr h⟩} := by
      ext x
      rcases x with ⟨⟨b,c⟩,hx⟩
      simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,Subtype.mk.injEq,Prod.mk.injEq]
      cases b <;> cases c <;> simp_all [Allowed]
    rw [hu]
    simp
  · rw [dite_eq_right h]
    have hu : (univ : Finset {bc : Bool × Bool // Allowed p bc.1 bc.2}) =
        {⟨(false,false),allowed_false_false p⟩,⟨(true,false),(allowed_true_false p).mpr h⟩,
          ⟨(false,true),(allowed_false_true p).mpr h⟩} := by
      ext x
      rcases x with ⟨⟨b,c⟩,hx⟩
      simp only [Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,Subtype.mk.injEq,Prod.mk.injEq]
      cases b <;> cases c <;> simp_all [Allowed]
    rw [hu]
    simp

theorem sum_extensions {R : Type*} [AddCommMonoid R] (n : ℕ)
    (f : Configuration (n+2) → R) :
    (∑ z, f z)=∑ p : Configuration (n+1), (
      f (appendConfiguration p false false (allowed_false_false p.val)) +
      if h : Fin.last n∈p.val.1 then
        f (appendConfiguration p true true ((allowed_true_true p.val).mpr h))
      else f (appendConfiguration p true false ((allowed_true_false p.val).mpr h))+
        f (appendConfiguration p false true ((allowed_false_true p.val).mpr h))) := by
  classical
  rw [← (extensionEquiv n).sum_comp f,Fintype.sum_sigma]
  apply sum_congr rfl
  intro p _
  exact sum_allowed p.val (fun bc => f (appendConfiguration p bc.val.1 bc.val.2 bc.property))

theorem top_spoke {n : ℕ} (i : Fin n) : i∈(⊤ : Configuration n).val.1 := by
  change i∈(readPair (graph n).edgeSet).1
  rw [mem_read_spokes]
  trivial

theorem append_top (n : ℕ) :
    appendConfiguration (⊤ : Configuration (n+1)) true true
      ((allowed_true_true _).mpr (top_spoke (Fin.last n)))=⊤ := by
  apply top_unique
  obtain ⟨x,hx⟩ := (extensionEquiv n).surjective (⊤ : Configuration (n+2))
  rw [← hx]
  change appendPair x.1.val x.2.val.1 x.2.val.2 ≤ appendPair _ true true
  rw [appendPair_le_iff]
  exact ⟨(show x.1 ≤ (⊤ : Configuration (n+1)) from le_top),Bool.le_true _,Bool.le_true _⟩

theorem appendConfiguration_eq_top_iff {n : ℕ} (p : Configuration (n+1)) (b c : Bool)
    (ha : Allowed p.val b c) :
    appendConfiguration p b c ha=⊤ ↔ p=⊤ ∧ b=true ∧ c=true := by
  rw [← append_top n]
  constructor
  · intro he
    have hle : appendPair (⊤ : Configuration (n+1)).val true true ≤ appendPair p.val b c :=
      (le_of_eq (congrArg Subtype.val he.symm))
    obtain ⟨hp,hb,hc⟩ := (appendPair_le_iff _ _ _ _ _ _).mp hle
    refine ⟨top_unique hp,?_,?_⟩
    · cases b
      · exact False.elim ((by decide : ¬((true : Bool)≤false)) hb)
      · rfl
    · cases c
      · exact False.elim ((by decide : ¬((true : Bool)≤false)) hc)
      · rfl
  · rintro ⟨rfl,rfl,rfl⟩
    rfl

end Fan
