import MainTheorems.DiagonalSchatten.RaySupport
import MainTheorems.DiagonalSchatten.RayGrouping

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J]

def columnRayKey (X : Matrix (Fin 2) J ℝ) (j : J) : Option ℝ :=
  if X 0 j = 0 then none else some (X 1 j / X 0 j)

def columnRayWeight (X : Matrix (Fin 2) J ℝ) (j : J) : ℝ :=
  if X 0 j = 0 then X 1 j ^ 2 else X 0 j ^ 2

def keyDirection : Option ℝ → Fin 2 → ℝ
  | none => ![0, 1]
  | some r => ![1, r]

def rayKeys (X : Matrix (Fin 2) J ℝ) : Finset (Option ℝ) := by
  classical
  exact ((interiorSlopes X).image some ∪
    (if firstAxisPresent X then {some 0} else ∅)) ∪
    (if secondAxisPresent X then {none} else ∅)

theorem rayKeys_card_le (X : Matrix (Fin 2) J ℝ) : (rayKeys X).card ≤ raySupportCard X := by
  classical
  have h1 := Finset.card_union_le ((interiorSlopes X).image some)
    (if firstAxisPresent X then {some 0} else ∅)
  have h2 := Finset.card_union_le
    ((interiorSlopes X).image some ∪ (if firstAxisPresent X then {some 0} else ∅))
    (if secondAxisPresent X then {none} else ∅)
  have hi := Finset.card_image_le (s := interiorSlopes X) (f := some)
  unfold rayKeys raySupportCard
  by_cases hf : firstAxisPresent X <;> by_cases hs : secondAxisPresent X <;>
    simp only [hf, hs, ite_true, ite_false, Finset.card_singleton, Finset.card_empty] at * <;>
    omega

theorem columnRayKey_mem (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (j : J) (hw : columnRayWeight X j ≠ 0) : columnRayKey X j ∈ rayKeys X := by
  classical
  by_cases h0 : X 0 j = 0
  · have h1 : 0 < X 1 j := by
      have hz : X 1 j ≠ 0 := by intro hz; exact hw (by simp [columnRayWeight, h0, hz])
      exact lt_of_le_of_ne (hX 1 j) (Ne.symm hz)
    have hs : secondAxisPresent X := ⟨j, h0, h1⟩
    simp [columnRayKey, h0, rayKeys, hs]
  · have hp0 : 0 < X 0 j := lt_of_le_of_ne (hX 0 j) (Ne.symm h0)
    by_cases h1 : X 1 j = 0
    · have hf : firstAxisPresent X := ⟨j, hp0, h1⟩
      simp [columnRayKey, h0, h1, rayKeys, hf]
    · have hp1 : 0 < X 1 j := lt_of_le_of_ne (hX 1 j) (Ne.symm h1)
      have hr : X 1 j / X 0 j ∈ interiorSlopes X := by
        apply Finset.mem_image.mpr
        exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp0, hp1⟩, rfl⟩
      unfold rayKeys
      apply Finset.mem_union_left
      apply Finset.mem_union_left
      simp only [columnRayKey, h0, ite_false]
      exact Finset.mem_image.mpr ⟨_, hr, rfl⟩

theorem keyDirection_nonnegative (X : Matrix (Fin 2) J ℝ)
    {q : Option ℝ} (hq : q ∈ rayKeys X) : ∀ i, 0 ≤ keyDirection q i := by
  classical
  rcases Finset.mem_union.mp hq with hq | hq
  · rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hr
      have hp := (Finset.mem_filter.mp hj).2
      intro i
      fin_cases i
      · simp [keyDirection]
      · simpa [keyDirection] using (div_pos hp.2 hp.1).le
    · split_ifs at hq with hf
      · have hq0 : q = some 0 := Finset.mem_singleton.mp hq
        subst q
        intro i
        fin_cases i <;> simp [keyDirection]
      · simp at hq
  · split_ifs at hq with hs
    · have hq0 : q = none := Finset.mem_singleton.mp hq
      subst q
      intro i
      fin_cases i <;> simp [keyDirection]
    · simp at hq

omit [Fintype J] in
theorem columnRayWeight_nonnegative (X : Matrix (Fin 2) J ℝ) (j : J) :
    0 ≤ columnRayWeight X j := by
  unfold columnRayWeight
  split_ifs <;> exact sq_nonneg _

omit [Fintype J] in
theorem columnRayWeight_zero (X : Matrix (Fin 2) J ℝ) (j : J)
    (hw : columnRayWeight X j = 0) : X 0 j = 0 ∧ X 1 j = 0 := by
  by_cases h0 : X 0 j = 0
  · refine ⟨h0, ?_⟩
    simp only [columnRayWeight, h0, ite_true] at hw
    nlinarith [sq_nonneg (X 1 j)]
  · simp only [columnRayWeight, h0, ite_false] at hw
    have hz : X 0 j = 0 := by nlinarith [sq_nonneg (X 0 j)]
    exact (h0 hz).elim

omit [Fintype J] in
theorem columnRay_recover (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j)
    (j : J) (i : Fin 2) :
    Real.sqrt (columnRayWeight X j) * keyDirection (columnRayKey X j) i = X i j := by
  by_cases h0 : X 0 j = 0
  · fin_cases i <;> simp [columnRayWeight, columnRayKey, h0, keyDirection,
      Real.sqrt_sq (hX 1 j)]
  · fin_cases i
    · simp [columnRayWeight, columnRayKey, h0, keyDirection, Real.sqrt_sq (hX 0 j)]
    · simp only [columnRayWeight, columnRayKey, h0, ite_false, keyDirection,
        Real.sqrt_sq (hX 0 j)]
      change X 0 j * (X 1 j / X 0 j) = X 1 j
      field_simp [h0]

theorem finset_two_cover {K : Type*} [DecidableEq K] (s : Finset K)
    (hne : s.Nonempty) (hcard : s.card ≤ 2) :
    ∃ a ∈ s, ∃ b ∈ s, ∀ q ∈ s, q = a ∨ q = b := by
  obtain ⟨a, ha⟩ := hne
  have herase : (s.erase a).card ≤ 1 := by
    rw [Finset.card_erase_of_mem ha]
    omega
  by_cases he : (s.erase a).Nonempty
  · obtain ⟨b, hb⟩ := he
    refine ⟨a, ha, b, Finset.mem_of_mem_erase hb, ?_⟩
    intro q hq
    by_cases hqa : q = a
    · exact Or.inl hqa
    · exact Or.inr ((Finset.card_le_one.mp herase) q
        (Finset.mem_erase.mpr ⟨hqa, hq⟩) b hb)
  · refine ⟨a, ha, a, ha, ?_⟩
    intro q hq
    left
    by_contra hqa
    exact he ⟨q, Finset.mem_erase.mpr ⟨hqa, hq⟩⟩

theorem ray_support_two_replacement (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, 0 ≤ X i j) (hne : (rayKeys X).Nonempty) (hs : raySupportCard X ≤ 2)
    (h : (Fin 2 → ℝ) → ℝ) (hh : ∀ x t, h (t • x) = t ^ 2 * h x) :
    ∃ T : Matrix (Fin 2) (Fin 2) ℝ, (∀ i j, 0 ≤ T i j) ∧
      gramFirst T = gramFirst X ∧ gramSecond T = gramSecond X ∧ gramCross T = gramCross X ∧
      columnObjective h T = columnObjective h X := by
  classical
  obtain ⟨a, ha, b, hb, hcover⟩ := finset_two_cover (rayKeys X) hne
    ((rayKeys_card_le X).trans hs)
  let label : J → Fin 2 := fun j => if columnRayKey X j = a then 0 else 1
  let d : Fin 2 → Fin 2 → ℝ := ![keyDirection a, keyDirection b]
  have hd : ∀ q i, 0 ≤ d q i := by
    intro q i
    fin_cases q
    · exact keyDirection_nonnegative X ha i
    · exact keyDirection_nonnegative X hb i
  have he : X = recoverRows (columnRayWeight X, fun j => d (label j)) := by
    ext i j
    change X i j = Real.sqrt (columnRayWeight X j) * d (label j) i
    by_cases hw : columnRayWeight X j = 0
    · obtain ⟨hz0, hz1⟩ := columnRayWeight_zero X j hw
      fin_cases i <;> simp [hw, hz0, hz1]
    · have hc := hcover (columnRayKey X j) (columnRayKey_mem X hX j hw)
      have hdir : d (label j) = keyDirection (columnRayKey X j) := by
        rcases hc with hc | hc
        · simp [d, label, hc]
        · by_cases hca : columnRayKey X j = a
          · simp [d, label, hca]
          · dsimp [d, label]
            rw [ite_eq_right hca]
            simp [hc]
      rw [hdir]
      exact (columnRay_recover X hX j i).symm
  exact two_ray_replacement X (columnRayWeight X) label d
    (columnRayWeight_nonnegative X) hd he h hh

end

end ResearchMain.DiagonalSchatten
