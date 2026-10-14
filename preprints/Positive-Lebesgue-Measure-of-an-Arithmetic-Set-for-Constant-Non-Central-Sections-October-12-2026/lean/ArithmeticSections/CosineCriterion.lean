import ArithmeticSections.ConditionContinuity
import Mathlib.Analysis.Real.Pi.Bounds

namespace ArithmeticSections

theorem sine_quotient_half_angles_general {s t : ℝ} (hs : 0 < s) (hst : s < t)
    (ht : t < Real.pi / 2) :
    Real.sin (t - s) / (Real.sin t - Real.sin s) =
      Real.cos ((t - s) / 2) / Real.cos ((t + s) / 2) := by
  have hsum : 0 < Real.cos ((t + s) / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hsin : 0 < Real.sin ((t - s) / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  rw [Real.sin_sub_sin]
  have he : Real.sin (t - s) = 2 * Real.sin ((t - s) / 2) * Real.cos ((t - s) / 2) := by
    convert Real.sin_two_mul ((t - s) / 2) using 1
    congr 1
    ring
  rw [he]
  field_simp

/-- Sufficient cosine-sign conditions for the actual arithmetic inequality. -/
theorem condition_of_cosine_signs {γ : ℝ} (hγ : Irrational γ)
    (hlo : 1 / 3 < γ) (hhi : γ < 1 / 2) {k : ℕ} (hk : 2 ≤ k)
    (hm : Real.pi * γ ≤ oddDistance γ (k + 1) ∨
      Real.cos (firstDistance γ k) * Real.cos (Real.pi * γ - oddDistance γ (k + 1)) > Real.cos (Real.pi * γ))
    (hp : Real.pi / 2 ≤ Real.pi * γ + oddDistance γ (k + 1) ∨
      Real.cos (Real.pi * γ) * Real.cos ((firstDistance γ k + secondDistance γ k) / 2) >
        Real.cos ((secondDistance γ k - firstDistance γ k) / 2) *
          Real.cos (Real.pi * γ + oddDistance γ (k + 1))) :
    0 < conditionGap γ k := by
  let a := Real.pi * γ
  let s := firstDistance γ k
  let t := secondDistance γ k
  let d := oddDistance γ (k + 1)
  have hs : 0 < s := firstDistance_pos hγ (by omega)
  have hst : s < t := firstDistance_lt_second hγ hk
  have ht : t < Real.pi / 2 := secondDistance_lt_half_pi hγ hk
  have hd : 0 < d := (oddDistance_bounds hγ (by omega)).1
  have ha : 0 < a := by dsimp [a]; nlinarith [Real.pi_pos]
  have ha' : a < Real.pi / 2 := by dsimp [a]; nlinarith [Real.pi_pos]
  have hsa : s < a := by
    have h := firstDistance_bounds_and_radius hγ hlo hhi hk
    dsimp [s, a]
    linarith [h.1, h.2.1, h.2.2.1]
  have hca : 0 < Real.cos a := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], ha'⟩
  have hcs : 0 < Real.cos s := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hcc : Real.cos a < Real.cos s := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hs.le ha'.le hsa
  have hrpos : 0 < Real.cos a / Real.cos s := div_pos hca hcs
  have hrlt : Real.cos a / Real.cos s < 1 := (div_lt_one hcs).mpr hcc
  have hmeq : minusDeviation γ k = a - Real.arccos (Real.cos a / Real.cos s) := by
    dsimp [minusDeviation, sectionG, rotationRadius, a, s]
    simp only [mul_inv_rev, inv_inv, div_eq_mul_inv]
    ring
  have hminus : minusDeviation γ k < d := by
    rw [hmeq]
    rcases hm with hm | hm
    · have hh := Real.arccos_pos.mpr hrlt
      change a ≤ d at hm
      linarith
    · by_cases had : a ≤ d
      · have hh := Real.arccos_pos.mpr hrlt
        linarith
      · have hac : 0 < a - d := by linarith
        have hadc : a - d < Real.pi := by linarith [Real.pi_pos]
        have hrr : Real.cos a / Real.cos s < Real.cos (a - d) := by
          apply (div_lt_iff₀ hcs).mpr
          change Real.cos s * Real.cos (a - d) > Real.cos a at hm
          nlinarith
        have hh := Real.arccos_lt_arccos (by linarith : -1 ≤ Real.cos a / Real.cos s)
          hrr (Real.cos_le_one (a - d))
        rw [Real.arccos_cos hac.le hadc.le] at hh
        linarith
  let u := (t - s) / 2
  let v := (t + s) / 2
  have hu : 0 < u := by dsimp [u]; linarith
  have hv : 0 < v := by dsimp [v]; linarith
  have hu' : u < Real.pi / 2 := by dsimp [u]; linarith
  have hv' : v < Real.pi / 2 := by dsimp [v]; linarith
  have hcu : 0 < Real.cos u := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hu'⟩
  have hcv : 0 < Real.cos v := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hv'⟩
  have hcuv : Real.cos v ≤ Real.cos u :=
    Real.cos_le_cos_of_nonneg_of_le_pi hu.le (by linarith [Real.pi_pos]) (by dsimp [u, v]; linarith)
  let r := Real.cos a * Real.cos v / Real.cos u
  have hr0 : 0 < r := by dsimp [r]; positivity
  have hr1 : r ≤ 1 := by
    dsimp [r]
    apply (div_le_one hcu).mpr
    calc
      Real.cos a * Real.cos v ≤ 1 * Real.cos v := mul_le_mul_of_nonneg_right (Real.cos_le_one a) hcv.le
      _ ≤ Real.cos u := by simpa only [one_mul] using hcuv
  have hpeq : plusDeviation γ k = Real.arccos r - a := by
    dsimp only [plusDeviation, sectionG]
    rw [sine_quotient_half_angles_general hs hst ht, rotationRadius]
    dsimp only [r, u, v, a, t, s]
    simp only [mul_inv_rev, inv_inv, div_eq_mul_inv]
    congr 2
    ring
  have hplus : plusDeviation γ k < d := by
    rw [hpeq]
    rcases hp with hp | hp
    · have hh := Real.arccos_lt_pi_div_two.mpr hr0
      change Real.pi / 2 ≤ a + d at hp
      linarith
    · by_cases had : Real.pi / 2 ≤ a + d
      · have hh := Real.arccos_lt_pi_div_two.mpr hr0
        linarith
      · have hac : 0 < a + d := by linarith
        have hadc : a + d < Real.pi := by linarith [Real.pi_pos]
        have hrr : Real.cos (a + d) < r := by
          dsimp [r]
          apply (lt_div_iff₀ hcu).mpr
          change Real.cos a * Real.cos ((s + t) / 2) > Real.cos u * Real.cos (a + d) at hp
          have hvv : (s + t) / 2 = v := by dsimp [v]; ring
          rw [hvv] at hp
          nlinarith
        have hh := Real.arccos_lt_arccos (Real.neg_one_le_cos (a + d)) hrr hr1
        rw [Real.arccos_cos hac.le hadc.le] at hh
        linarith
  unfold conditionGap
  change 0 < d - max (minusDeviation γ k) (plusDeviation γ k)
  exact sub_pos.mpr (max_lt hminus hplus)

end ArithmeticSections
