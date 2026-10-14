import CokernelPolynomiality.ChainRepresentations
import Mathlib.LinearAlgebra.Dual.Lemmas

noncomputable section
open CategoryTheory
namespace CokernelPolynomiality

def chainMap {n : ℕ} (V : ChainRep n) (i j : (Fin (n+1))ᵒᵈ) (hij : i.ofDual.val ≤ j.ofDual.val) :
    V.obj j →ₗ[ℂ] V.obj i := (V.map (homOfLE (X:=(Fin (n+1))ᵒᵈ) (x:=j) (y:=i) hij)).hom.hom

@[simp] theorem chainMap_self {n : ℕ} (V : ChainRep n) (i : (Fin (n+1))ᵒᵈ) :
    chainMap V i i (le_refl i.ofDual.val)=LinearMap.id := by
  exact congrArg (fun f => f.hom.hom) (V.map_id i)

theorem chainMap_comp {n : ℕ} (V : ChainRep n) (i j k : (Fin (n+1))ᵒᵈ)
    (hij : i.ofDual.val ≤ j.ofDual.val) (hjk : j.ofDual.val ≤ k.ofDual.val) :
    (chainMap V i j hij).comp (chainMap V j k hjk)=chainMap V i k (hij.trans hjk) := by
  have hh := V.map_comp (homOfLE (X:=(Fin (n+1))ᵒᵈ) (x:=k) (y:=j) hjk)
    (homOfLE (X:=(Fin (n+1))ᵒᵈ) (x:=j) (y:=i) hij)
  exact (congrArg (fun f => f.hom.hom) hh).symm

def totalDimension {n : ℕ} (V : ChainRep n) : ℕ :=
  ∑ i : (Fin (n+1))ᵒᵈ, Module.finrank ℂ (V.obj i)

/-- Data for a genuine split interval subrepresentation of a finite chain. -/
structure SplitInterval {n : ℕ} (V : ChainRep n) where
  a : ℕ
  b : ℕ
  hab : a ≤ b
  hbn : b ≤ n
  inclusion : intervalRep n a b ⟶ V
  retraction : V ⟶ intervalRep n a b
  splitting : inclusion ≫ retraction=𝟙 (intervalRep n a b)

end CokernelPolynomiality
