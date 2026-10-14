import Mathlib.Algebra.Category.FGModuleCat.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic

noncomputable section
open CategoryTheory
namespace CokernelPolynomiality

/-- Finite-dimensional complex representations of the uniformly oriented
chain, with the contravariant convention of the source. -/
abbrev ChainRep (n : ℕ) := (Fin (n+1))ᵒᵈ ⥤ FGModuleCat ℂ

def intervalActive (a b i : ℕ) : Prop := a ≤ i ∧ i ≤ b

instance (a b i : ℕ) : Decidable (intervalActive a b i) := inferInstanceAs (Decidable (_ ∧ _))

def intervalSpace (a b i : ℕ) : Submodule ℂ ℂ :=
  if intervalActive a b i then ⊤ else ⊥

@[simp] theorem intervalSpace_of_active {a b i : ℕ} (h : intervalActive a b i) :
    intervalSpace a b i=⊤ := ite_eq_left h

@[simp] theorem intervalSpace_of_inactive {a b i : ℕ} (h : ¬intervalActive a b i) :
    intervalSpace a b i=⊥ := ite_eq_right h

def intervalMap (a b i j : ℕ) : intervalSpace a b j →ₗ[ℂ] intervalSpace a b i :=
  if hi : intervalActive a b i then
    { toFun := fun x => ⟨x.val,by simp [intervalSpace,hi]⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  else 0

@[simp] theorem intervalMap_val (a b i j : ℕ) (x : intervalSpace a b j) :
    (intervalMap a b i j x).val=if intervalActive a b i then x.val else 0 := by
  unfold intervalMap
  split <;> rfl

theorem intervalSpace_val_zero {a b i : ℕ} (hi : ¬intervalActive a b i)
    (x : intervalSpace a b i) : x.val=0 := by
  have hx := x.property
  simpa [intervalSpace,hi] using hx

theorem intervalMap_id (a b i : ℕ) : intervalMap a b i i=LinearMap.id := by
  ext x
  rw [intervalMap_val]
  by_cases hi : intervalActive a b i
  · simp [hi]
  · simp [hi,intervalSpace_val_zero hi x]

theorem intervalMap_comp (a b i j k : ℕ) (hij : i ≤ j) (hjk : j ≤ k) :
    (intervalMap a b i j).comp (intervalMap a b j k)=intervalMap a b i k := by
  ext x
  simp only [LinearMap.comp_apply,intervalMap_val]
  by_cases hi : intervalActive a b i
  · by_cases hj : intervalActive a b j
    · simp [hi,hj]
    · have hk : ¬intervalActive a b k := by
        unfold intervalActive at *
        omega
      simp [hi,hj,intervalSpace_val_zero hk x]
  · simp [hi]

def intervalRep (n a b : ℕ) : ChainRep n where
  obj i := FGModuleCat.of ℂ (intervalSpace a b i.ofDual.val)
  map {i j} f := FGModuleCat.ofHom (intervalMap a b j.ofDual.val i.ofDual.val)
  map_id i := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun f : intervalSpace a b i.ofDual.val →ₗ[ℂ] intervalSpace a b i.ofDual.val => f x) (intervalMap_id a b i.ofDual.val)
  map_comp {i j k} f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun f : intervalSpace a b i.ofDual.val →ₗ[ℂ] intervalSpace a b k.ofDual.val => f x)
      (intervalMap_comp a b k.ofDual.val j.ofDual.val i.ofDual.val (leOfHom g) (leOfHom f)).symm

end CokernelPolynomiality
