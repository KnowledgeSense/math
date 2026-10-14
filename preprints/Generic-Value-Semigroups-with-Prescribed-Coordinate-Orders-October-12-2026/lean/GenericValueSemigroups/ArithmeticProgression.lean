import GenericValueSemigroups.WeightAsymptotic
import Mathlib.Analysis.Asymptotics.Defs

namespace GenericValueSemigroups
open scoped BigOperators Classical

/-- Positive integer coordinate orders in arithmetic progression. -/
def arithmeticOrders (m ℓ : ℕ) : Fin 3 → ℕ := ![m*ℓ,m*ℓ+m,m*ℓ+2*m]

theorem arithmeticOrders_pos {m ℓ : ℕ} (hm : 0<m) (hℓ : 0<ℓ) :
    ∀ i, 0<arithmeticOrders m ℓ i := by
  intro i
  fin_cases i <;> simp [arithmeticOrders, hm, hℓ]

theorem arithmeticOrders_sum (m ℓ : ℕ) :
    (∑ i, (arithmeticOrders m ℓ i : ℝ)) = 3*(m : ℝ)*((ℓ : ℝ)+1) := by
  simp [arithmeticOrders, Fin.sum_univ_succ]
  ring

theorem arithmeticOrders_prod (m ℓ : ℕ) :
    (∏ i, (arithmeticOrders m ℓ i : ℝ)) = (m : ℝ)^3*(ℓ : ℝ)*((ℓ : ℝ)+1)*((ℓ : ℝ)+2) := by
  simp [arithmeticOrders, Fin.prod_univ_succ]
  ring

theorem rpow_three_halves {x : ℝ} (hx : 0<x) :
    x^((3 : ℝ)/2)=x*x^((1 : ℝ)/2) := by
  rw [show (3 : ℝ)/2=1+1/2 by norm_num,Real.rpow_add hx,Real.rpow_one]

theorem rpow_half_sq {x : ℝ} (hx : 0≤x) : (x^((1 : ℝ)/2))^2=x := by
  simpa using Real.rpow_inv_natCast_pow hx (by decide : (2 : ℕ)≠0)

/-- The critical scale of the arithmetic progression lies between the stated half-power terms. -/
theorem arithmetic_scale_bounds {m ℓ : ℕ} (hm : 0<m) (hℓ : 0<ℓ) :
    (2*(m : ℝ))^((3 : ℝ)/2)/3*(ℓ : ℝ)^((3 : ℝ)/2) ≤
      (2/3 : ℝ)*genusScale (arithmeticOrders m ℓ) ∧
    (2/3 : ℝ)*genusScale (arithmeticOrders m ℓ) ≤
      (2*(m : ℝ))^((3 : ℝ)/2)/3*(ℓ : ℝ)^((3 : ℝ)/2) +
      2*(2*(m : ℝ))^((3 : ℝ)/2)/3*(ℓ : ℝ)^((1 : ℝ)/2) := by
  have hmR : (0 : ℝ)<m := by exact_mod_cast hm
  have hℓR : (0 : ℝ)<ℓ := by exact_mod_cast hℓ
  let t := genusScale (arithmeticOrders m ℓ)
  let u : ℝ := (2*(m : ℝ))^((3 : ℝ)/2)
  let v : ℝ := (ℓ : ℝ)^((1 : ℝ)/2)
  let z : ℝ := u*v
  have ht : 0<t := genusScale_pos _ (arithmeticOrders_pos hm hℓ)
  have hu : 0<u := Real.rpow_pos_of_pos (by positivity) _
  have hv : 0<v := Real.rpow_pos_of_pos hℓR _
  have hz : 0<z := mul_pos hu hv
  have hu2 : u^2=8*(m : ℝ)^3 := by
    dsimp [u]
    rw [rpow_three_halves (by positivity),mul_pow,rpow_half_sq (by positivity)]
    ring
  have hv2 : v^2=(ℓ : ℝ) := rpow_half_sq hℓR.le
  have hz2 : z^2=8*(m : ℝ)^3*(ℓ : ℝ) := by
    dsimp [z]
    rw [mul_pow,hu2,hv2]
  have ht2 : t^2=2*(m : ℝ)^3*(ℓ : ℝ)*((ℓ : ℝ)+1)*((ℓ : ℝ)+2) := by
    have hh := genusScale_pow (by decide : 2≤3) (arithmeticOrders m ℓ)
      (arithmeticOrders_pos hm hℓ)
    norm_num only [Nat.reduceSub,Nat.factorial_succ,Nat.factorial_zero,Nat.cast_ofNat] at hh
    rw [arithmeticOrders_prod] at hh
    dsimp [t]
    nlinarith [hh]
  have hlo : z*(ℓ : ℝ)≤2*t := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow,ht2]
    have hn : 0≤8*(m : ℝ)^3*(ℓ : ℝ)*(3*(ℓ : ℝ)+2) := by positivity
    nlinarith [hn]
  have hhi : 2*t≤z*((ℓ : ℝ)+2) := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow,ht2]
    have hn : 0≤8*(m : ℝ)^3*(ℓ : ℝ)*((ℓ : ℝ)+2) := by positivity
    nlinarith [hn]
  rw [rpow_three_halves hℓR]
  change u/3*((ℓ : ℝ)*v)≤(2/3 : ℝ)*t ∧
    (2/3 : ℝ)*t≤u/3*((ℓ : ℝ)*v)+2*u/3*v
  dsimp [z] at hlo hhi
  constructor <;> nlinarith

/-- The full arithmetic-progression genus corollary for the actual greedy gapset. -/
theorem arithmetic_progression_genus_bounds {m ℓ : ℕ} (hm : 0<m) (hℓ : 0<ℓ)
    (gaps : Finset ℕ)
    (hgaps : ∀ n, n ∈ gaps ↔ n ∉ Set.range
      (greedy (weightAt (arithmeticOrders m ℓ) (arithmeticOrders_pos hm hℓ) (by decide)))) :
    -3*(m : ℝ)*((ℓ : ℝ)+1)-1 ≤
      (gaps.card : ℝ)-(2*(m : ℝ))^((3 : ℝ)/2)/3*(ℓ : ℝ)^((3 : ℝ)/2) ∧
    (gaps.card : ℝ)-(2*(m : ℝ))^((3 : ℝ)/2)/3*(ℓ : ℝ)^((3 : ℝ)/2) ≤
      2*(2*(m : ℝ))^((3 : ℝ)/2)/3*(ℓ : ℝ)^((1 : ℝ)/2) := by
  have hg := greedy_genus_asymptotic (by decide : 2≤3) (arithmeticOrders m ℓ)
    (arithmeticOrders_pos hm hℓ) gaps hgaps
  norm_num only [Nat.reduceSub,Nat.cast_ofNat] at hg
  rw [arithmeticOrders_sum] at hg
  have hs := arithmetic_scale_bounds hm hℓ
  constructor <;> linarith [hg.1,hg.2,hs.1,hs.2]

/-- The half-integral power constant for the doubled arithmetic progression. -/
theorem four_rpow_three_halves : (4 : ℝ)^((3 : ℝ)/2)=8 := by
  have h := rpow_half_sq (x := 4) (by norm_num)
  have hp := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ)<4) ((1 : ℝ)/2)
  have he : (4 : ℝ)^((1 : ℝ)/2)=2 := by nlinarith
  rw [rpow_three_halves (by norm_num),he]
  norm_num

/-- A uniform linear error bound, making the stated `O(ℓ)` remainder explicit. -/
theorem even_arithmetic_progression_genus_error {ℓ : ℕ} (hℓ : 0<ℓ)
    (gaps : Finset ℕ)
    (hgaps : ∀ n, n ∈ gaps ↔ n ∉ Set.range
      (greedy (weightAt (arithmeticOrders 2 ℓ) (arithmeticOrders_pos (by decide) hℓ) (by decide)))) :
    |(gaps.card : ℝ)-(8/3 : ℝ)*(ℓ : ℝ)^((3 : ℝ)/2)| ≤ 13*(ℓ : ℝ) := by
  have hg := arithmetic_progression_genus_bounds (by decide : 0<2) hℓ gaps hgaps
  norm_num only [Nat.cast_ofNat,show (2 : ℝ)*2=4 by norm_num,four_rpow_three_halves] at hg
  have hℓR : (1 : ℝ)≤ℓ := by exact_mod_cast hℓ
  have hh := rpow_half_sq (x := (ℓ : ℝ)) (by positivity)
  have hhalf : (ℓ : ℝ)^((1 : ℝ)/2)≤(ℓ : ℝ) := by
    have hp : (0 : ℝ)≤(ℓ : ℝ)*((ℓ : ℝ)-1) := by positivity
    nlinarith [hp]
  rw [abs_le]
  constructor <;> linarith [hg.1,hg.2]

/-- For `(2ℓ,2ℓ+2,2ℓ+4)`, the genus is `(8/3)ℓ^(3/2)+O(ℓ)`. -/
theorem even_arithmetic_progression_genus_bigO (gaps : ℕ → Finset ℕ)
    (hgaps : ∀ ℓ (hℓ : 0<ℓ) n, n ∈ gaps ℓ ↔ n ∉ Set.range
      (greedy (weightAt (arithmeticOrders 2 ℓ) (arithmeticOrders_pos (by decide) hℓ) (by decide)))) :
    (fun ℓ : ℕ => ((gaps ℓ).card : ℝ)-(8/3 : ℝ)*(ℓ : ℝ)^((3 : ℝ)/2))
      =O[Filter.atTop] (fun ℓ : ℕ => (ℓ : ℝ)) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨13,Filter.eventually_atTop.mpr ⟨1,?_⟩⟩
  intro ℓ hℓ
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg ℓ : (0 : ℝ)≤ℓ)] using
    even_arithmetic_progression_genus_error (by omega : 0<ℓ) (gaps ℓ) (hgaps ℓ (by omega))

end GenericValueSemigroups
