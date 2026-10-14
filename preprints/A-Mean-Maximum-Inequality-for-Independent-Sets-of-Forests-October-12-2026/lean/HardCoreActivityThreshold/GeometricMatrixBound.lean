import HardCoreActivityThreshold.TriangularBounds
import Mathlib.Algebra.Ring.GeomSum

namespace HardCoreActivityThreshold
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def geometricLayerWeight (C γ : ℝ) (h : ℕ) : ℝ :=
  if h=0 then 1 else Real.sqrt C*(Real.sqrt γ)^(h-1)

theorem geometricLayerWeight_nonneg (C γ : ℝ) (h : ℕ) : 0≤geometricLayerWeight C γ h := by
  unfold geometricLayerWeight
  split_ifs <;> positivity

theorem geometricLayerWeight_square (C γ : ℝ) (hC : 0≤C) (hγ : 0≤γ)
    (h : ℕ) (hh : h≠0) : (geometricLayerWeight C γ h)^2=C*γ^(h-1) := by
  simp only [geometricLayerWeight,hh,↓reduceIte,mul_pow]
  rw [Real.sq_sqrt hC,←pow_mul, Nat.mul_comm (h-1) 2,pow_mul,Real.sq_sqrt hγ]

theorem geometricLayerWeight_sum (C γ : ℝ) (hγ : 0≤γ) (hγ1 : γ<1) (N : ℕ) :
    (∑h : Fin (N+1),geometricLayerWeight C γ h.val)≤1+Real.sqrt C/(1-Real.sqrt γ) := by
  have hs : Real.sqrt γ<1 := (Real.sqrt_lt hγ (by norm_num)).mpr (by simpa using hγ1)
  have hp : 0<1-Real.sqrt γ := by linarith
  have he := geom_sum_mul_neg (Real.sqrt γ) N
  have hn : 0≤(Real.sqrt γ)^N := pow_nonneg (Real.sqrt_nonneg _) _
  have hg : (∑i∈range N,(Real.sqrt γ)^i)≤1/(1-Real.sqrt γ) := by
    rw [le_div_iff₀ hp]
    linarith
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,Fin.val_succ,geometricLayerWeight,↓reduceIte,Nat.add_eq_zero_iff,
    Nat.one_ne_zero,and_false, Nat.add_sub_cancel]
  rw [←mul_sum,Fin.sum_univ_eq_sum_range]
  have hm := mul_le_mul_of_nonneg_left hg (Real.sqrt_nonneg C)
  simpa only [mul_one_div,add_comm] using add_le_add_left hm 1

 theorem geometric_power_square_bound (B : Matrix V V ℝ) (C γ : ℝ)
    (hC : 0≤C) (hγ : 0≤γ)
    (hrow : ∀h : ℕ,0<h → ∀u v w,v≠w → (B^h) u v*(B^h) u w=0)
    (hcol : ∀h : ℕ,0<h → ∀v,(∑u,((B^h) u v)^2)≤C*γ^(h-1))
    (h : ℕ) (x : V → ℝ) :
    (∑u,((B^h)*ᵥx) u^2)≤(geometricLayerWeight C γ h)^2*(∑v,(x v)^2) := by
  by_cases hz : h=0
  · subst h
    simp [geometricLayerWeight]
  · rw [geometricLayerWeight_square C γ hC hγ h hz]
    exact sparse_matrix_square_bound (B^h) _ (hrow h (Nat.pos_of_ne_zero hz))
      (hcol h (Nat.pos_of_ne_zero hz)) x

theorem geometric_sum_square_bound (B : Matrix V V ℝ) (C γ : ℝ)
    (hC : 0≤C) (hγ : 0≤γ) (hγ1 : γ<1)
    (hrow : ∀h : ℕ,0<h → ∀u v w,v≠w → (B^h) u v*(B^h) u w=0)
    (hcol : ∀h : ℕ,0<h → ∀v,(∑u,((B^h) u v)^2)≤C*γ^(h-1))
    (N : ℕ) (x : V → ℝ) :
    (∑u,((∑h : Fin (N+1),B^h.val)*ᵥx) u^2)≤
      (1+Real.sqrt C/(1-Real.sqrt γ))^2*(∑v,(x v)^2) := by
  have h := matrix_sum_square_bound (fun h : Fin (N+1) => B^h.val)
    (fun h => geometricLayerWeight C γ h.val)
    (fun h => geometricLayerWeight_nonneg C γ h.val)
    (fun h => geometric_power_square_bound B C γ hC hγ hrow hcol h.val) x
  have hs := geometricLayerWeight_sum C γ hγ hγ1 N
  have hnon : 0≤∑h : Fin (N+1),geometricLayerWeight C γ h.val :=
    sum_nonneg (fun h _ => geometricLayerWeight_nonneg C γ h.val)
  have hsq : (∑h : Fin (N+1),geometricLayerWeight C γ h.val)^2≤
      (1+Real.sqrt C/(1-Real.sqrt γ))^2 := by nlinarith
  exact h.trans (mul_le_mul_of_nonneg_right hsq (sum_nonneg (fun _ _ => sq_nonneg _)))

 theorem triangular_correlation_quadratic_bound (R B : Matrix V V ℝ) (d : V → ℝ)
    (C γ : ℝ) (hC : 0≤C) (hγ : 0≤γ) (hγ1 : γ<1)
    (hrow : ∀h : ℕ,0<h → ∀u v w,v≠w → (B^h) u v*(B^h) u w=0)
    (hcol : ∀h : ℕ,0<h → ∀v,(∑u,((B^h) u v)^2)≤C*γ^(h-1))
    (N : ℕ) (hd : ∀i,d i≤1)
    (hR : R=(∑h : Fin (N+1),B^h.val)*diagonal d*(∑h : Fin (N+1),B^h.val).transpose)
    (x : V → ℝ) :
    x ⬝ᵥ (R*ᵥx)≤(1+Real.sqrt C/(1-Real.sqrt γ))^2*(∑v,(x v)^2) := by
  rw [hR]
  exact diagonal_factor_quadratic_bound _ d _ hd
    (geometric_sum_square_bound B C γ hC hγ hγ1 hrow hcol N) x

theorem bounded_triangular_correlation_quadratic_bound (R B : Matrix V V ℝ) (d : V → ℝ)
    (D C γ : ℝ) (hD : 0≤D) (hC : 0≤C) (hγ : 0≤γ) (hγ1 : γ<1)
    (hrow : ∀h : ℕ,0<h → ∀u v w,v≠w → (B^h) u v*(B^h) u w=0)
    (hcol : ∀h : ℕ,0<h → ∀v,(∑u,((B^h) u v)^2)≤C*γ^(h-1))
    (N : ℕ) (hd : ∀i,d i≤D)
    (hR : R=(∑h : Fin (N+1),B^h.val)*diagonal d*(∑h : Fin (N+1),B^h.val).transpose)
    (x : V → ℝ) :
    x ⬝ᵥ (R*ᵥx)≤D*(1+Real.sqrt C/(1-Real.sqrt γ))^2*(∑v,(x v)^2) := by
  rw [hR]
  exact bounded_diagonal_factor_quadratic_bound _ d D _ hD hd
    (geometric_sum_square_bound B C γ hC hγ hγ1 hrow hcol N) x

end HardCoreActivityThreshold
