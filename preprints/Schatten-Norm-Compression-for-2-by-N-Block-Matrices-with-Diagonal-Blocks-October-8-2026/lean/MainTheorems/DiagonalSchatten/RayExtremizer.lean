import MainTheorems.DiagonalSchatten.RayFunctional
import MainTheorems.DiagonalSchatten.FaceExtremizer

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

theorem quarterCircle_has_positive_coordinate {x : Fin 2 → ℝ} (hx : x ∈ quarterCircle) :
    0 < x 0 ∨ 0 < x 1 := by
  by_contra h
  push Not at h
  have h0 : x 0 = 0 := le_antisymm h.1 hx.1
  have h1 : x 1 = 0 := le_antisymm h.2 hx.2.1
  have he := hx.2.2
  simp [h0, h1] at he

namespace RayParameters

variable (g : RayParameters)

theorem continuousOn_functional_quarterCircle
    (hD : ∀ x ∈ quarterCircle, g.denominator x ≠ 0) :
    ContinuousOn g.functional quarterCircle := by
  intro x hx
  exact (g.contDiffAt_functional (n := 1) x (hD x hx)).continuousAt.continuousWithinAt

theorem continuousOn_functional_upper (hk : 0 < g.k) (ha : 0 < g.a)
    (hb : 0 < g.b) (hc : 0 < g.c) : ContinuousOn g.functional quarterCircle := by
  apply g.continuousOn_functional_quarterCircle
  intro x hx
  exact (g.denominator_upper x hk ha hb hc hx.1 hx.2.1
    (quarterCircle_has_positive_coordinate hx)).ne'

theorem continuousOn_functional_lower (hk1 : -1 < g.k) (hk : g.k < 0)
    (ha : 0 < g.a) (hb : 0 < g.b) (hc : g.c < 0) (hdet : g.c ^ 2 < g.a * g.b) :
    ContinuousOn g.functional quarterCircle := by
  apply g.continuousOn_functional_quarterCircle
  intro x hx
  exact (g.denominator_lower x hk1 hk ha hb hc hdet hx.1 hx.2.1
    (quarterCircle_has_positive_coordinate hx)).ne'

variable {J : Type*} [Fintype J]

theorem exists_functional_max {A B C : ℝ}
    (hne : (gramFiber (J := J) A B C).Nonempty)
    (hD : ∀ x ∈ quarterCircle, g.denominator x ≠ 0) (s : ℝ) :
    ∃ X ∈ gramFiber (J := J) A B C, ∀ Y ∈ gramFiber (J := J) A B C,
      columnObjective (fun x => s * g.functional x) Y ≤
        columnObjective (fun x => s * g.functional x) X := by
  apply exists_columnObjective_max hne
  · exact continuousOn_const.mul (g.continuousOn_functional_quarterCircle hD)
  · intro x t
    rw [g.functional_homogeneous]
    ring

theorem contDiffAt_faceObjective {n : WithTop ℕ∞} (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, 0 ≤ X i j)
    (hD : ∀ x, 0 ≤ x 0 → 0 ≤ x 1 → (0 < x 0 ∨ 0 < x 1) → g.denominator x ≠ 0) :
    ContDiffAt ℝ n (faceObjective g.functional X) (facePoint X) := by
  classical
  unfold faceObjective columnObjective
  apply ContDiffAt.sum
  intro j _
  by_cases hz : X 0 j = 0 ∧ X 1 j = 0
  · have hcol (v : FaceIndex X → ℝ) : (fun i => faceRows X v i j) = 0 := by
      funext i
      fin_cases i <;> simp [faceRows, hz.1, hz.2]
    have heq : (fun v : FaceIndex X → ℝ => g.functional (fun i => faceRows X v i j)) =
        (fun _ => g.functional 0) := by
      funext v
      rw [hcol]
    rw [heq]
    exact contDiffAt_const
  · have hp : 0 < X 0 j ∨ 0 < X 1 j := by
      by_contra h
      push Not at h
      exact hz ⟨le_antisymm h.1 (hX 0 j), le_antisymm h.2 (hX 1 j)⟩
    have hcol : ContDiffAt ℝ n (fun v : FaceIndex X → ℝ => fun i => faceRows X v i j)
        (facePoint X) := by
      apply contDiffAt_pi.mpr
      intro i
      exact ((contDiff_apply ℝ ℝ j).comp ((contDiff_apply ℝ (J → ℝ) i).comp
        (contDiff_faceRows X))).contDiffAt
    have hR := faceRows_point X hX
    have hd : g.denominator (fun i => faceRows X (facePoint X) i j) ≠ 0 := by
      rw [hR]
      exact hD (fun i => X i j) (hX 0 j) (hX 1 j) hp
    exact (g.contDiffAt_functional (n := n) _ hd).comp (facePoint X) hcol

theorem signed_faceObjective_contDiffAt {n : WithTop ℕ∞} (X : Matrix (Fin 2) J ℝ)
    (hX : ∀ i j, 0 ≤ X i j)
    (hD : ∀ x, 0 ≤ x 0 → 0 ≤ x 1 → (0 < x 0 ∨ 0 < x 1) → g.denominator x ≠ 0)
    (s : ℝ) : ContDiffAt ℝ n (faceObjective (fun x => s * g.functional x) X) (facePoint X) := by
  have heq : faceObjective (fun x => s * g.functional x) X =
      (fun v => s * faceObjective g.functional X v) := by
    funext v
    simp only [faceObjective, columnObjective, Finset.mul_sum]
  rw [heq]
  exact contDiffAt_const.mul (g.contDiffAt_faceObjective X hX hD)

theorem signed_faceObjective_lagrange {A B C : ℝ} (s : ℝ)
    {X : Matrix (Fin 2) J ℝ} (hX : X ∈ gramFiber A B C)
    (hmax : ∀ Y ∈ gramFiber (J := J) A B C,
      columnObjective (fun x => s * g.functional x) Y ≤
        columnObjective (fun x => s * g.functional x) X)
    (hD : ∀ x, 0 ≤ x 0 → 0 ≤ x 1 → (0 < x 0 ∨ 0 < x 1) → g.denominator x ≠ 0) :
    ∃ (Λ : Fin 3 → ℝ) (Λ0 : ℝ), (Λ, Λ0) ≠ 0 ∧
      (∑ i, Λ i • fderiv ℝ (faceGram X i) (facePoint X)) +
        Λ0 • fderiv ℝ (faceObjective (fun x => s * g.functional x) X) (facePoint X) = 0 :=
  faceObjective_lagrange hX hmax (g.signed_faceObjective_contDiffAt X hX.1 hD s)

end RayParameters

end

end ResearchMain.DiagonalSchatten
