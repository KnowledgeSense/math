import CokernelPolynomiality.SplitKernel
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.Dimension.Constructions

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace CokernelPolynomiality

theorem totalDimension_iso {n : ℕ} {V W : ChainRep n} (e : V ≅ W) :
    totalDimension V=totalDimension W := by
  apply Finset.sum_congr rfl
  intro i _
  exact (FGModuleCat.isoToLinearEquiv (e.app i)).finrank_eq

theorem finrank_fg_biprod (X Y : FGModuleCat.{u} ℂ) :
    Module.finrank ℂ (biprod X Y : FGModuleCat ℂ)=Module.finrank ℂ X+Module.finrank ℂ Y := by
  let F := forget₂ (FGModuleCat.{u} ℂ) (ModuleCat.{u} ℂ)
  let : F.Additive := ⟨by intros; rfl⟩
  let := preservesBinaryBiproducts_of_preservesBiproducts F
  let e := F.mapBiprod X Y ≪≫ ModuleCat.biprodIsoProd (F.obj X) (F.obj Y)
  have h := e.toLinearEquiv.finrank_eq
  change Module.finrank ℂ (biprod X Y : FGModuleCat.{u} ℂ)=Module.finrank ℂ (X × Y) at h
  rw [Module.finrank_prod] at h
  exact h

theorem totalDimension_biprod {n : ℕ} (V W : ChainRep n) :
    totalDimension (biprod V W)=totalDimension V+totalDimension W := by
  unfold totalDimension
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  let E := (evaluation ((Fin (n+1))ᵒᵈ) (FGModuleCat ℂ)).obj i
  let := preservesBinaryBiproducts_of_preservesBiproducts E
  have h := (FGModuleCat.isoToLinearEquiv (E.mapBiprod V W)).finrank_eq
  exact h.trans (finrank_fg_biprod (V.obj i) (W.obj i))

theorem totalDimension_interval_pos (n a b : ℕ) (hab : a ≤ b) (hbn : b ≤ n) :
    0 < totalDimension (intervalRep n a b) := by
  let i : (Fin (n+1))ᵒᵈ := OrderDual.toDual ⟨b,by omega⟩
  have hd : Module.finrank ℂ ((intervalRep n a b).obj i)=1 := by
    change Module.finrank ℂ (intervalSpace a b b)=1
    rw [intervalSpace_of_active ⟨hab,le_refl b⟩]
    simp
  have h := Finset.single_le_sum (f:=fun j : (Fin (n+1))ᵒᵈ =>
    Module.finrank ℂ ((intervalRep n a b).obj j)) (s:=Finset.univ)
    (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  rw [hd] at h
  exact lt_of_lt_of_le (by decide) h

theorem SplitInterval.kernel_dimension_lt {n : ℕ} {V : ChainRep n} (s : SplitInterval V) :
    totalDimension (kernel s.retraction)<totalDimension V := by
  have he := totalDimension_iso (splitKernelIso s.inclusion s.retraction s.splitting)
  rw [totalDimension_biprod] at he
  have hp := totalDimension_interval_pos n s.a s.b s.hab s.hbn
  omega

end CokernelPolynomiality
