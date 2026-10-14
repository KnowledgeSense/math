import RandomWalkSearch.EndpointNets
import Mathlib.Tactic.FieldSimp

/-! # Exact cardinality and mass of the actual marked translates

The dense/sparse overlap is counted as an actual intersection of Finsets.
No definition substitutes a closed formula for the marked set or its mass.
-/

namespace RandomWalkSearch.Cycle
variable {k : ℕ}

/-- A translated grid whose integer offsets stay below the modulus has no
collisions. This also covers ordinary arcs by choosing spacing one. -/
theorem card_translated_grid_of_le (a : Vertex k) (m q : ℕ) (hq : 0 < q)
    (hbound : m*q ≤ N k) :
    ((Finset.range m).image (fun j : ℕ => a + (j*q : ℕ))).card = m := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj he
  have hcast : ((i*q : ℕ) : Vertex k) = (j*q : ℕ) := add_left_cancel he
  have hv := congrArg ZMod.val hcast
  have hiN : i*q < N k := (Nat.mul_lt_mul_of_pos_right (Finset.mem_range.mp hi) hq).trans_le hbound
  have hjN : j*q < N k := (Nat.mul_lt_mul_of_pos_right (Finset.mem_range.mp hj) hq).trans_le hbound
  have hm : i*q=j*q := by simpa only [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hjN] using hv
  exact Nat.eq_of_mul_eq_mul_right hq hm

theorem D_eq_overlap_spacing (k : ℕ) : D k = k^5*L k := by
  dsimp [D, L]
  ring

theorem interval_card_exact (hk : 0 < k) (a : Vertex k) :
    (interval a).card = k^7 := by
  have hd : D k ≤ N k := pow_le_pow_right₀ hk (by decide : 7 ≤ 8)
  have h := card_translated_grid_of_le a (D k) 1 (by omega) (by simpa using hd)
  simpa [interval, arc, D] using h

theorem progression_card_exact (hk : 0 < k) (a : Vertex k) :
    (progression a).card = k^6 := by
  exact card_translated_grid_of_le a (k^6) (L k) (L_pos hk)
    (le_of_eq (N_eq_sparse k).symm)

/-- The overlap consists exactly of the first `k^5` sparse-grid points. -/
theorem interval_inter_progression (hk : 0 < k) (a : Vertex k) :
    interval a ∩ progression a =
      (Finset.range (k^5)).image (fun j : ℕ => a + (j*L k : ℕ)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hi, hg⟩ := Finset.mem_inter.mp hx
    obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hi
    obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hg
    have hiD : i < D k := Finset.mem_range.mp hi
    have hjK : j < k^6 := Finset.mem_range.mp hj
    have hiN : i < N k := hiD.trans_le (pow_le_pow_right₀ hk (by decide : 7 ≤ 8))
    have hjN : j*L k < N k := by
      rw [N_eq_sparse]
      exact Nat.mul_lt_mul_of_pos_right hjK (L_pos hk)
    have he : (i : Vertex k) = (j*L k : ℕ) := add_left_cancel (hix.trans hjx.symm)
    have hv := congrArg ZMod.val he
    have hij : i=j*L k := by
      simpa only [ZMod.val_natCast_of_lt hiN, ZMod.val_natCast_of_lt hjN] using hv
    have hj5 : j < k^5 := by
      rw [hij, D_eq_overlap_spacing] at hiD
      exact Nat.lt_of_mul_lt_mul_right hiD
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj5, hjx⟩
  · intro hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    have hj5 : j<k^5 := Finset.mem_range.mp hj
    have hj6 : j<k^6 := hj5.trans_le (pow_le_pow_right₀ hk (by decide : 5 ≤ 6))
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_image.mpr
      refine ⟨j*L k, Finset.mem_range.mpr ?_, rfl⟩
      rw [D_eq_overlap_spacing]
      exact Nat.mul_lt_mul_of_pos_right hj5 (L_pos hk)
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj6, rfl⟩

theorem interval_inter_progression_card_exact (hk : 0 < k) (a : Vertex k) :
    (interval a ∩ progression a).card = k^5 := by
  rw [interval_inter_progression hk a]
  apply card_translated_grid_of_le a (k^5) (L k) (L_pos hk)
  rw [← D_eq_overlap_spacing]
  exact pow_le_pow_right₀ hk (by decide : 7 ≤ 8)

/-- Exact cardinality of the genuine translated union. -/
theorem marked_card_exact (hk : 0 < k) (a : Vertex k) :
    (marked a).card = k^7+k^6-k^5 := by
  rw [marked, Finset.card_union, interval_card_exact hk a,
    progression_card_exact hk a, interval_inter_progression_card_exact hk a]

/-- Actual uniform-translate marked mass as a real number. -/
theorem marked_mass_real_exact (hk : 0 < k) (a : Vertex k) :
    ((marked a).card : ℝ)/(N k : ℝ) =
      1/(k : ℝ)+1/(k : ℝ)^2-1/(k : ℝ)^3 := by
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hsub : k^5 ≤ k^7+k^6 :=
    (pow_le_pow_right₀ hk (by decide : 5 ≤ 7)).trans (Nat.le_add_right _ _)
  rw [marked_card_exact hk a]
  simp only [Nat.cast_sub hsub, Nat.cast_add, Nat.cast_pow, N]
  field_simp

open scoped ENNReal

/-- The same actual mass in the extended-expectation codomain. -/
theorem marked_mass_ennreal_exact (hk : 0 < k) (a : Vertex k) :
    ((marked a).card : ℝ≥0∞)/(N k : ℝ≥0∞) =
      ENNReal.ofReal (1/(k : ℝ)+1/(k : ℝ)^2-1/(k : ℝ)^3) := by
  rw [← marked_mass_real_exact hk a,
    ENNReal.ofReal_div_of_pos (show (0 : ℝ) < N k by exact_mod_cast N_pos hk)]
  simp

/-- Literal extended-real mass formula, with subtraction interpreted as the
usual nonnegative truncated subtraction. -/
theorem marked_mass_ennreal_formula (hk : 0 < k) (a : Vertex k) :
    ((marked a).card : ℝ≥0∞)/(N k : ℝ≥0∞) =
      1/(k : ℝ≥0∞)+1/(k : ℝ≥0∞)^2-1/(k : ℝ≥0∞)^3 := by
  have hkp : (0 : ℝ) < k := by exact_mod_cast hk
  rw [marked_mass_ennreal_exact hk a, ENNReal.ofReal_sub _ (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_div_of_pos hkp,
    ENNReal.ofReal_div_of_pos (show (0 : ℝ) < (k : ℝ)^2 by positivity),
    ENNReal.ofReal_div_of_pos (show (0 : ℝ) < (k : ℝ)^3 by positivity)]
  simp [ENNReal.ofReal_pow hkp.le]

end RandomWalkSearch.Cycle

