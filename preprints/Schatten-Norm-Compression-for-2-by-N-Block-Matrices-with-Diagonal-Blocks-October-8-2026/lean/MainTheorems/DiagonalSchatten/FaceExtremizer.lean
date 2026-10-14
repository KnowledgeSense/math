import MainTheorems.DiagonalSchatten.FiniteRayMaximum
import Mathlib.Analysis.Calculus.LagrangeMultipliers
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Operations

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise Topology

variable {J : Type*} [Fintype J]

abbrev FaceIndex (X : Matrix (Fin 2) J ℝ) := {ij : Fin 2 × J // 0 < X ij.1 ij.2}

instance (X : Matrix (Fin 2) J ℝ) : Fintype (FaceIndex X) := Fintype.ofFinite _

def facePoint (X : Matrix (Fin 2) J ℝ) : FaceIndex X → ℝ :=
  fun e => X e.1.1 e.1.2

def faceRows (X : Matrix (Fin 2) J ℝ) (v : FaceIndex X → ℝ) : Matrix (Fin 2) J ℝ := by
  classical
  exact Matrix.of fun i j => if h : 0 < X i j then v ⟨(i, j), h⟩ else 0

omit [Fintype J] in
theorem faceRows_point (X : Matrix (Fin 2) J ℝ) (hX : ∀ i j, 0 ≤ X i j) :
    faceRows X (facePoint X) = X := by
  classical
  ext i j
  by_cases h : 0 < X i j
  · simp [faceRows, facePoint, h]
  · have h0 : X i j = 0 := le_antisymm (not_lt.mp h) (hX i j)
    simp [faceRows, h0]

omit [Fintype J] in
theorem faceRows_nonnegative (X : Matrix (Fin 2) J ℝ) (v : FaceIndex X → ℝ)
    (hv : ∀ e, 0 ≤ v e) : ∀ i j, 0 ≤ faceRows X v i j := by
  classical
  intro i j
  simp only [faceRows, Matrix.of_apply]
  split_ifs with h
  · exact hv ⟨(i, j), h⟩
  · exact le_rfl

theorem contDiff_faceRows (X : Matrix (Fin 2) J ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (faceRows X) := by
  classical
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  simp only [faceRows, Matrix.of_apply]
  split_ifs <;> fun_prop

def faceGram (X : Matrix (Fin 2) J ℝ) (i : Fin 3) (v : FaceIndex X → ℝ) : ℝ :=
  ![gramFirst (faceRows X v), gramSecond (faceRows X v), gramCross (faceRows X v)] i

def faceObjective (h : (Fin 2 → ℝ) → ℝ) (X : Matrix (Fin 2) J ℝ)
    (v : FaceIndex X → ℝ) : ℝ := columnObjective h (faceRows X v)

theorem contDiff_faceGram (X : Matrix (Fin 2) J ℝ) (i : Fin 3) {n : WithTop ℕ∞} :
    ContDiff ℝ n (faceGram X i) := by
  have hR : ContDiff ℝ n (faceRows X) := contDiff_faceRows X
  fin_cases i
  · change ContDiff ℝ n (fun v => gramFirst (faceRows X v))
    exact (by unfold gramFirst; fun_prop : ContDiff ℝ n gramFirst).comp hR
  · change ContDiff ℝ n (fun v => gramSecond (faceRows X v))
    exact (by unfold gramSecond; fun_prop : ContDiff ℝ n gramSecond).comp hR
  · change ContDiff ℝ n (fun v => gramCross (faceRows X v))
    exact (by unfold gramCross; fun_prop : ContDiff ℝ n gramCross).comp hR

theorem faceObjective_localMax {a b c : ℝ} {h : (Fin 2 → ℝ) → ℝ}
    {X : Matrix (Fin 2) J ℝ} (hX : X ∈ gramFiber a b c)
    (hmax : ∀ Y ∈ gramFiber (J := J) a b c, columnObjective h Y ≤ columnObjective h X) :
    IsLocalMaxOn (faceObjective h X)
      {v | ∀ i, faceGram X i v = faceGram X i (facePoint X)} (facePoint X) := by
  classical
  have hopen : IsOpen {v : FaceIndex X → ℝ | ∀ e, 0 < v e} := by
    simp only [Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun e => isOpen_lt continuous_const (by fun_prop)
  have hpos : ∀ᶠ v in 𝓝 (facePoint X), ∀ e, 0 < v e :=
    hopen.mem_nhds (fun e => e.2)
  change ∀ᶠ v in 𝓝[{v | ∀ i, faceGram X i v = faceGram X i (facePoint X)}]
      (facePoint X), faceObjective h X v ≤ faceObjective h X (facePoint X)
  filter_upwards [hpos.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with v hv hg
  have hR : faceRows X (facePoint X) = X := faceRows_point X hX.1
  have hA := hg (0 : Fin 3)
  have hB := hg (1 : Fin 3)
  have hC := hg (2 : Fin 3)
  change gramFirst (faceRows X v) = gramFirst (faceRows X (facePoint X)) at hA
  change gramSecond (faceRows X v) = gramSecond (faceRows X (facePoint X)) at hB
  change gramCross (faceRows X v) = gramCross (faceRows X (facePoint X)) at hC
  rw [hR, hX.2.1] at hA
  rw [hR, hX.2.2.1] at hB
  rw [hR, hX.2.2.2] at hC
  have hY : faceRows X v ∈ gramFiber a b c :=
    ⟨faceRows_nonnegative X v (fun e => (hv e).le), hA, hB, hC⟩
  simpa only [faceObjective, hR] using hmax (faceRows X v) hY

theorem faceObjective_lagrange {a b c : ℝ} {h : (Fin 2 → ℝ) → ℝ}
    {X : Matrix (Fin 2) J ℝ} (hX : X ∈ gramFiber a b c)
    (hmax : ∀ Y ∈ gramFiber (J := J) a b c, columnObjective h Y ≤ columnObjective h X)
    (hd : ContDiffAt ℝ 1 (faceObjective h X) (facePoint X)) :
    ∃ (Λ : Fin 3 → ℝ) (Λ0 : ℝ), (Λ, Λ0) ≠ 0 ∧
      (∑ i, Λ i • fderiv ℝ (faceGram X i) (facePoint X)) +
        Λ0 • fderiv ℝ (faceObjective h X) (facePoint X) = 0 := by
  have he : IsLocalExtrOn (faceObjective h X)
      {v | ∀ i, faceGram X i v = faceGram X i (facePoint X)} (facePoint X) :=
    Or.inr (faceObjective_localMax hX hmax)
  exact he.exists_multipliers_of_hasStrictFDerivAt
    (fun i => (contDiff_faceGram X i (n := 1)).hasStrictFDerivAt (by norm_num))
    (hd.hasStrictFDerivAt (by norm_num))

end

end ResearchMain.DiagonalSchatten
