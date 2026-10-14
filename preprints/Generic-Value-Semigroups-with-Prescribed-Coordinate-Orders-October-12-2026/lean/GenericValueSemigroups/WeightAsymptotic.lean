import GenericValueSemigroups.WeightVolume
import GenericValueSemigroups.GenusConductor
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.FieldSimp

namespace GenericValueSemigroups
open scoped BigOperators Classical

/-- The volume bounds, proved by exact finite residue-box counting. -/
theorem weightCount_volume_bounds {d : ℕ} (hd : 0<d) (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) (n : ℕ) :
    (n : ℝ)^d / ((d.factorial : ℝ) * ∏ i, (r i : ℝ)) ≤ (weightCount r n : ℝ) ∧
      (weightCount r n : ℝ) ≤
        ((n : ℝ)+∑ i, (r i : ℝ))^d / ((d.factorial : ℝ) * ∏ i, (r i : ℝ)) := by
  have hp : 0 < (d.factorial : ℝ) * ∏ i, (r i : ℝ) := by
    apply mul_pos
    · exact_mod_cast Nat.factorial_pos d
    · exact Finset.prod_pos (fun i _ => by exact_mod_cast hr i)
  constructor
  · rw [div_le_iff₀ hp]
    have hh := weightCount_lower_factorial hd r hr n
    have hh' : (n : ℝ)^d ≤ (d.factorial : ℝ) * (∏ i, (r i : ℝ)) * (weightCount r n : ℝ) := by
      exact_mod_cast hh
    nlinarith [hh']
  · rw [le_div_iff₀ hp]
    have hh := weightCount_upper_factorial r hr n
    have hh' : (d.factorial : ℝ) * (∏ i, (r i : ℝ)) * (weightCount r n : ℝ) ≤
        ((n : ℝ)+∑ i, (r i : ℝ))^d := by exact_mod_cast hh
    nlinarith [hh']

/-- The positive critical scale appearing in the genus asymptotic theorem. -/
noncomputable def genusScale {d : ℕ} (r : Fin d → ℕ) : ℝ :=
  (((d-1).factorial : ℝ) * ∏ i, (r i : ℝ)) ^ ((d-1 : ℕ) : ℝ)⁻¹

theorem genusScale_pos {d : ℕ} (r : Fin d → ℕ) (hr : ∀ i, 0<r i) :
    0<genusScale r := by
  apply Real.rpow_pos_of_pos
  exact mul_pos (by exact_mod_cast Nat.factorial_pos (d-1))
    (Finset.prod_pos (fun i _ => by exact_mod_cast hr i))

theorem genusScale_pow {d : ℕ} (hd : 2≤d) (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) :
    genusScale r ^ (d-1) = ((d-1).factorial : ℝ) * ∏ i, (r i : ℝ) := by
  apply Real.rpow_inv_natCast_pow
  · exact le_of_lt (mul_pos (by exact_mod_cast Nat.factorial_pos (d-1))
      (Finset.prod_pos (fun i _ => by exact_mod_cast hr i)))
  · omega

/-- The tangent inequality for an integral power, proved by Bernoulli's inequality. -/
theorem power_tangent_le {d : ℕ} (hd : 0<d) {t x : ℝ} (ht : 0<t) (hx : 0≤x) :
    t^d+(d : ℝ)*t^(d-1)*(x-t) ≤ x^d := by
  have hb := one_add_mul_sub_le_pow (a := x/t) (by have h : 0≤x/t := div_nonneg hx ht.le; linarith : -1≤x/t) d
  have hm := mul_le_mul_of_nonneg_right hb (pow_nonneg ht.le d)
  rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ ht.ne')] at hm
  have hp : t^d = t^(d-1)*t := by
    rw [← pow_succ, Nat.sub_add_cancel hd]
  have he : (1+(d : ℝ)*(x/t-1))*t^d = t^d+(d : ℝ)*t^(d-1)*(x-t) := by
    rw [hp]
    field_simp
  rwa [he] at hm

/-- The continuous deficit is bounded above by its value at the critical scale. -/
theorem continuous_deficit_le {d : ℕ} (hd : 2≤d) (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) {x : ℝ} (hx : 0≤x) :
    x-x^d/((d.factorial : ℝ)*∏ i, (r i : ℝ)) ≤
      ((d-1 : ℕ) : ℝ)/(d : ℝ)*genusScale r := by
  let t := genusScale r
  let A : ℝ := (d.factorial : ℝ)*∏ i, (r i : ℝ)
  have hd0 : 0<d := by omega
  have hdr : (0 : ℝ)<d := by exact_mod_cast hd0
  have ht : 0<t := genusScale_pos r hr
  have hA : 0<A := mul_pos (by exact_mod_cast Nat.factorial_pos d)
    (Finset.prod_pos (fun i _ => by exact_mod_cast hr i))
  have hfact : d.factorial=d*(d-1).factorial := by
    simpa [Nat.sub_add_cancel hd0] using Nat.factorial_succ (d-1)
  have hscale : (d : ℝ)*t^(d-1)=A := by
    dsimp [t,A]
    rw [genusScale_pow hd r hr, hfact, Nat.cast_mul]
    ring
  have hp : t^d=t^(d-1)*t := by rw [← pow_succ,Nat.sub_add_cancel hd0]
  have hdp : ((d-1 : ℕ) : ℝ)=(d : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤d), Nat.cast_one]
  have hb := power_tangent_le hd0 ht hx
  rw [hscale] at hb
  have hAt : A*t=(d : ℝ)*t^d := by rw [hp,← hscale]; ring
  have hxdiv : x^d/A*A=x^d := div_mul_cancel₀ _ hA.ne'
  have hcoeff : (((d-1 : ℕ) : ℝ)/(d : ℝ)*t)*A = A*t-t^d := by
    rw [hdp]
    field_simp
    nlinarith [hAt]
  change x-x^d/A ≤ ((d-1 : ℕ) : ℝ)/(d : ℝ)*t
  apply (mul_le_mul_iff_left₀ hA).mp
  nlinarith [hb,hxdiv,hcoeff]

/-- The value of the continuous deficit at its positive critical scale. -/
theorem genusScale_critical_value {d : ℕ} (hd : 2≤d) (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) :
    genusScale r - genusScale r^d/((d.factorial : ℝ)*∏ i, (r i : ℝ)) =
      ((d-1 : ℕ) : ℝ)/(d : ℝ)*genusScale r := by
  have hd0 : 0<d := by omega
  have hdne : (d : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hd0
  have hfne : ((d-1).factorial : ℝ)≠0 := by exact_mod_cast Nat.factorial_ne_zero (d-1)
  have hpne : (∏ i, (r i : ℝ))≠0 :=
    ne_of_gt (Finset.prod_pos (fun i _ => by exact_mod_cast hr i))
  have hfact : d.factorial=d*(d-1).factorial := by
    simpa [Nat.sub_add_cancel hd0] using Nat.factorial_succ (d-1)
  have hp : genusScale r^d=genusScale r^(d-1)*genusScale r := by
    rw [← pow_succ,Nat.sub_add_cancel hd0]
  rw [hp,genusScale_pow hd r hr,hfact,Nat.cast_mul,
    Nat.cast_sub (by omega : 1≤d),Nat.cast_one]
  field_simp

/-- The sharp genus estimate for any attained maximum of the actual counting deficits. -/
theorem genus_asymptotic_of_count_deficit {d : ℕ} (hd : 2≤d) (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) (D C : ℕ)
    (hbound : ∀ n, n ≤ weightCount r n+D) (hC : C=weightCount r C+D) :
    ((d-1 : ℕ) : ℝ)/(d : ℝ)*genusScale r-(∑ i, (r i : ℝ))-1 ≤ (D : ℝ) ∧
      (D : ℝ) ≤ ((d-1 : ℕ) : ℝ)/(d : ℝ)*genusScale r := by
  have hd0 : 0<d := by omega
  let t := genusScale r
  let R : ℝ := ∑ i, (r i : ℝ)
  let A : ℝ := (d.factorial : ℝ)*∏ i, (r i : ℝ)
  let q : ℝ := ((d-1 : ℕ) : ℝ)/(d : ℝ)
  have ht : 0<t := genusScale_pos r hr
  have hR : 0≤R := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  have hA : 0<A := mul_pos (by exact_mod_cast Nat.factorial_pos d)
    (Finset.prod_pos (fun i _ => by exact_mod_cast hr i))
  have hcritical : t-t^d/A=q*t := genusScale_critical_value hd r hr
  have hq : q≤1 := by
    dsimp [q]
    apply (div_le_one (by exact_mod_cast hd0 : (0 : ℝ)<d)).mpr
    exact_mod_cast Nat.sub_le d 1
  constructor
  · change q*t-R-1 ≤ (D : ℝ)
    by_cases htR : t<R
    · have hqt : q*t≤t := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) ht.le]
      have hD : (0 : ℝ)≤D := Nat.cast_nonneg D
      linarith
    · have hnonneg : 0≤t-R := by linarith
      let n : ℕ := ⌊t-R⌋₊
      have hn_le : (n : ℝ)≤t-R := Nat.floor_le hnonneg
      have hn_lt : t-R<(n : ℝ)+1 := Nat.lt_floor_add_one (t-R)
      have hnR : (n : ℝ)+R≤t := by linarith
      have hpow : ((n : ℝ)+R)^d≤t^d :=
        pow_le_pow_left₀ (by positivity) hnR d
      have hv := (weightCount_volume_bounds hd0 r hr n).2
      change (weightCount r n : ℝ) ≤ ((n : ℝ)+R)^d/A at hv
      have hdiv := div_le_div_of_nonneg_right hpow hA.le
      have hcnt : (n : ℝ)≤(weightCount r n : ℝ)+(D : ℝ) := by
        exact_mod_cast hbound n
      linarith
  · have hv := (weightCount_volume_bounds hd0 r hr C).1
    have hm := continuous_deficit_le hd r hr (x := (C : ℝ)) (Nat.cast_nonneg C)
    have hc : (C : ℝ)=(weightCount r C : ℝ)+(D : ℝ) := by exact_mod_cast hC
    linarith

/-- The full genus asymptotic theorem for the actual greedy monomial value set. -/
theorem greedy_genus_asymptotic {d : ℕ} (hd : 2≤d) (r : Fin d → ℕ)
    (hr : ∀ i, 0<r i) (gaps : Finset ℕ)
    (hgaps : ∀ n, n ∈ gaps ↔ n ∉ Set.range (greedy (weightAt r hr (by omega)))) :
    ((d-1 : ℕ) : ℝ)/(d : ℝ)*genusScale r-(∑ i, (r i : ℝ))-1 ≤ (gaps.card : ℝ) ∧
      (gaps.card : ℝ) ≤ ((d-1 : ℕ) : ℝ)/(d : ℝ)*genusScale r := by
  let i : Fin d := ⟨0,by omega⟩
  let j : Fin d := ⟨1,by omega⟩
  have hij : i≠j := by intro he; have := congrArg Fin.val he; simp [i,j] at this
  obtain ⟨D,J,h,hJ⟩ := exists_weight_deficit_maximum r hr (by omega) i j hij
  obtain ⟨gaps',hg',hcard⟩ := greedy_gaps_finite_card (weightAt r hr (by omega)) D J h hJ
  have he : gaps=gaps' := Finset.ext (fun n => (hgaps n).trans (hg' n).symm)
  rw [he,hcard]
  apply genus_asymptotic_of_count_deficit hd r hr D (J+D)
  · exact count_deficit_bound r hr (by omega) D h
  · have hc := count_deficit_attained r hr (by omega) D J h hJ
    rw [hJ] at hc
    omega

end GenericValueSemigroups
