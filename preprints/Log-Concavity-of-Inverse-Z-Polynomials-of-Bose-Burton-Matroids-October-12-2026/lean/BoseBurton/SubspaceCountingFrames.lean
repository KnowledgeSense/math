import BoseBurton.RankedSpaces
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

noncomputable section
namespace BoseBurton
open Submodule Module
variable (K V : Type*) [Field K] [AddCommGroup V] [Module K V]

abbrev IndependentFrame (k : ℕ) := {f : Fin k→V // LinearIndependent K f}
abbrev SubspacesOfDimension (k : ℕ) := {U : Submodule K V // finrank K U=k}

variable {K V}

def independentFrameSpan {k : ℕ} (f : IndependentFrame K V k) : SubspacesOfDimension K V k :=
  ⟨span K (Set.range f.val),by simpa using finrank_span_eq_card f.property⟩

def independentFrameInSpan {k : ℕ} (f : IndependentFrame K V k) :
    IndependentFrame K (independentFrameSpan f).val k :=
  ⟨fun i=>⟨f.val i,subset_span ⟨i,rfl⟩⟩,
    LinearIndependent.of_comp (independentFrameSpan f).val.subtype f.property⟩

def frameFromSubspace {k : ℕ} (x : Σ U : SubspacesOfDimension K V k,IndependentFrame K U.val k) :
    IndependentFrame K V k :=
  ⟨fun i=>(x.2.val i).val,x.2.property.map' x.1.val.subtype x.1.val.ker_subtype⟩

variable [Module.Finite K V]

theorem frameFromSubspace_span {k : ℕ}
    (x : Σ U : SubspacesOfDimension K V k,IndependentFrame K U.val k) :
    (independentFrameSpan (frameFromSubspace x)).val=x.1.val := by
  apply Submodule.eq_of_le_of_finrank_eq
  · apply span_le.mpr
    rintro v ⟨i,rfl⟩
    exact (x.2.val i).property
  · exact (independentFrameSpan (frameFromSubspace x)).property.trans x.1.property.symm

theorem frameFromSubspace_bijective (k : ℕ) :
    Function.Bijective (frameFromSubspace (K:=K) (V:=V) (k:=k)) := by
  constructor
  · rintro ⟨⟨U,hU⟩,f⟩ ⟨⟨W,hW⟩,g⟩ he
    have hspan := congrArg (fun f : IndependentFrame K V k=>(independentFrameSpan f).val) he
    rw [frameFromSubspace_span,frameFromSubspace_span] at hspan
    change U=W at hspan
    subst W
    congr 1
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun (congrArg Subtype.val he) i
  · intro f
    refine ⟨⟨independentFrameSpan f,independentFrameInSpan f⟩,?_⟩
    apply Subtype.ext
    rfl

def independentFrameSpanEquiv (k : ℕ) :
    (Σ U : SubspacesOfDimension K V k,IndependentFrame K U.val k) ≃ IndependentFrame K V k :=
  Equiv.ofBijective frameFromSubspace (frameFromSubspace_bijective k)

end BoseBurton
