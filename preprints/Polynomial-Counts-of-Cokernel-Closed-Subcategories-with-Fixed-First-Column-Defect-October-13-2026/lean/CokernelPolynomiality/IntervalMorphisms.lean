import CokernelPolynomiality.ChainRepresentations

noncomputable section
open CategoryTheory
namespace CokernelPolynomiality

def intervalComponent (a b c d i : ℕ) : intervalSpace a b i →ₗ[ℂ] intervalSpace c d i :=
  if hi : intervalActive c d i then
    { toFun := fun x => ⟨x.val,by simp [intervalSpace,hi]⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  else 0

@[simp] theorem intervalComponent_val (a b c d i : ℕ) (x : intervalSpace a b i) :
    (intervalComponent a b c d i x).val=if intervalActive c d i then x.val else 0 := by
  unfold intervalComponent
  split <;> rfl

theorem intervalComponent_naturality (a b c d i j : ℕ) (hac : a ≤ c) (hbd : b ≤ d)
    (hij : i ≤ j) :
    (intervalComponent a b c d i).comp (intervalMap a b i j)=
      (intervalMap c d i j).comp (intervalComponent a b c d j) := by
  ext x
  simp only [LinearMap.comp_apply,intervalComponent_val,intervalMap_val]
  by_cases hi : intervalActive c d i
  · by_cases hj : intervalActive a b j
    · have ha : intervalActive a b i := by unfold intervalActive at *; omega
      have hd : intervalActive c d j := by unfold intervalActive at *; omega
      simp [hi,ha,hd]
    · simp [hi,intervalSpace_val_zero hj x]
  · simp [hi]

/-- The canonical nonzero interval morphism whenever the two intervals overlap
in the source's Hom order. The same construction is zero if they do not overlap. -/
def intervalHom (n a b c d : ℕ) (hac : a ≤ c) (hbd : b ≤ d) :
    intervalRep n a b ⟶ intervalRep n c d where
  app i := FGModuleCat.ofHom (intervalComponent a b c d i.ofDual.val)
  naturality {i j} f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun g : intervalSpace a b i.ofDual.val →ₗ[ℂ] intervalSpace c d j.ofDual.val => g x)
      (intervalComponent_naturality a b c d j.ofDual.val i.ofDual.val hac hbd (leOfHom f))

theorem intervalHom_nonzero (n a b c d : ℕ) (hac : a ≤ c) (hcb : c ≤ b)
    (hbd : b ≤ d) (hbn : b ≤ n) : intervalHom n a b c d hac hbd ≠ 0 := by
  intro he
  let i : (Fin (n+1))ᵒᵈ := ⟨b,by omega⟩
  have hab : intervalActive a b b := ⟨by omega,le_refl b⟩
  have hcd : intervalActive c d b := ⟨hcb,hbd⟩
  let x : intervalSpace a b b := ⟨1,by simp [intervalSpace,hab]⟩
  have h := congrArg (fun f : intervalRep n a b ⟶ intervalRep n c d =>
    ((f.app i).hom.hom x).val) he
  change (intervalComponent a b c d b x).val=0 at h
  rw [intervalComponent_val,ite_eq_left hcd] at h
  exact one_ne_zero h

end CokernelPolynomiality
