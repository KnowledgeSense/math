import MainTheorems.DiagonalSchatten.RaySupport

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

theorem one_interior_slope (X : Matrix (Fin 2) J ℝ)
    (hs : (interiorSlopes X).card = 1) :
    ∃ r : ℝ, 0 < r ∧ ∀ j, 0 < X 0 j → 0 < X 1 j → X 1 j = r * X 0 j := by
  classical
  obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hs
  have hm : r ∈ interiorSlopes X := by rw [hr]; simp
  obtain ⟨j, hj, hjr⟩ := Finset.mem_image.mp hm
  have hp := (Finset.mem_filter.mp hj).2
  refine ⟨r, ?_, ?_⟩
  · rw [← hjr]
    exact div_pos hp.2 hp.1
  · intro k hk0 hk1
    have hk : X 1 k / X 0 k ∈ interiorSlopes X :=
      Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk0, hk1⟩, rfl⟩
    rw [hr, Finset.mem_singleton] at hk
    exact (div_eq_iff hk0.ne').mp hk

theorem three_ray_functional_column {h : (Fin 2 → ℝ) → ℝ}
    (hh : ∀ x t, h (t • x) = t ^ 2 * h x) (x : Fin 2 → ℝ)
    (hx0 : 0 ≤ x 0) (hx1 : 0 ≤ x 1) {r : ℝ} (hr : 0 < r)
    (hs : 0 < x 0 → 0 < x 1 → x 1 = r * x 0) :
    h x = x 0 ^ 2 * h ![1, 0] + x 1 ^ 2 * h ![0, 1] +
      (x 0 * x 1) * (h ![1, r] / r - h ![1, 0] / r - r * h ![0, 1]) := by
  by_cases h0 : x 0 = 0
  · have he : x = x 1 • (![0, 1] : Fin 2 → ℝ) := by
      funext i
      fin_cases i <;> simp [h0]
    rw [he, hh]
    simp [Pi.smul_apply, smul_eq_mul]
  by_cases h1 : x 1 = 0
  · have he : x = x 0 • (![1, 0] : Fin 2 → ℝ) := by
      funext i
      fin_cases i <;> simp [h1]
    rw [he, hh]
    simp [Pi.smul_apply, smul_eq_mul]
  · have hp0 : 0 < x 0 := lt_of_le_of_ne hx0 (Ne.symm h0)
    have hp1 : 0 < x 1 := lt_of_le_of_ne hx1 (Ne.symm h1)
    have hs' := hs hp0 hp1
    have he : x = x 0 • (![1, r] : Fin 2 → ℝ) := by
      funext i
      fin_cases i
      · simp
      · simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using hs'
    rw [he, hh]
    simp [Pi.smul_apply, smul_eq_mul]
    field_simp [hr.ne']
    ring

theorem three_ray_objective (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    {r : ℝ} (hr : 0 < r)
    (hs : ∀ j, 0 < X 0 j → 0 < X 1 j → X 1 j = r * X 0 j)
    (h : (Fin 2 → ℝ) → ℝ) (hh : ∀ x t, h (t • x) = t ^ 2 * h x) :
    columnObjective h X = (gramFirst X - gramCross X / r) * h ![1, 0] +
      (gramSecond X - gramCross X * r) * h ![0, 1] +
      (gramCross X / r) * h ![1, r] := by
  unfold columnObjective
  have hcols (j : J) := three_ray_functional_column hh (fun i => X i j)
    (hX 0 j) (hX 1 j) hr (hs j)
  simp_rw [hcols]
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, gramFirst, gramSecond, gramCross]
  ring

theorem three_ray_first_mass_nonnegative (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, 0 ≤ X i j) {r : ℝ} (hr : 0 < r)
    (hs : ∀ j, 0 < X 0 j → 0 < X 1 j → X 1 j = r * X 0 j) :
    0 ≤ gramFirst X - gramCross X / r := by
  have hcol (j : J) : X 0 j * X 1 j ≤ X 0 j ^ 2 * r := by
    by_cases h0 : X 0 j = 0
    · simp [h0]
    by_cases h1 : X 1 j = 0
    · simpa [h1] using mul_nonneg (sq_nonneg (X 0 j)) hr.le
    · rw [hs j (lt_of_le_of_ne (hX 0 j) (Ne.symm h0))
        (lt_of_le_of_ne (hX 1 j) (Ne.symm h1))]
      ring_nf
      exact le_rfl
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hcol j)
  rw [← Finset.sum_mul] at hsum
  apply sub_nonneg.mpr
  exact (div_le_iff₀ hr).mpr hsum

theorem three_ray_second_mass_nonnegative (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, 0 ≤ X i j) {r : ℝ} (_hr : 0 < r)
    (hs : ∀ j, 0 < X 0 j → 0 < X 1 j → X 1 j = r * X 0 j) :
    0 ≤ gramSecond X - gramCross X * r := by
  have hcol (j : J) : (X 0 j * X 1 j) * r ≤ X 1 j ^ 2 := by
    by_cases h0 : X 0 j = 0
    · simpa [h0] using sq_nonneg (X 1 j)
    by_cases h1 : X 1 j = 0
    · simp [h1]
    · rw [hs j (lt_of_le_of_ne (hX 0 j) (Ne.symm h0))
        (lt_of_le_of_ne (hX 1 j) (Ne.symm h1))]
      ring_nf
      exact le_rfl
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hcol j)
  rw [← Finset.sum_mul] at hsum
  exact sub_nonneg.mpr hsum

theorem three_ray_slope_interval (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, 0 ≤ X i j) {r : ℝ} (hr : 0 < r)
    (ha : 0 < gramFirst X) (hc : 0 < gramCross X)
    (hs : ∀ j, 0 < X 0 j → 0 < X 1 j → X 1 j = r * X 0 j) :
    gramCross X / gramFirst X ≤ r ∧ r ≤ gramSecond X / gramCross X := by
  have hA := three_ray_first_mass_nonnegative X hX hr hs
  have hB := three_ray_second_mass_nonnegative X hX hr hs
  constructor
  · apply (div_le_iff₀ ha).mpr
    have he := (div_le_iff₀ hr).mp (show gramCross X / r ≤ gramFirst X by linarith)
    nlinarith
  · apply (le_div_iff₀ hc).mpr
    nlinarith

end

end ResearchMain.DiagonalSchatten
