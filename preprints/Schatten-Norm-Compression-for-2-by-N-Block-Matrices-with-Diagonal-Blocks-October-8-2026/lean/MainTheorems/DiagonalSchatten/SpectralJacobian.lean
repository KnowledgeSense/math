import MainTheorems.DiagonalSchatten.SpectralJacobianSign
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

namespace ResearchMain.DiagonalSchatten

noncomputable section

def spectralChartEntries (t w h : ℝ) : Fin 4 → ℝ :=
  ![1 + h * t * w, t - h * w, w - h * t, t * w + h]

def spectralChartTangentT (w h : ℝ) : Fin 4 → ℝ := ![h * w, 1, -h, w]
def spectralChartTangentW (t h : ℝ) : Fin 4 → ℝ := ![h * t, -h, 1, t]
def spectralChartTangentH (t w : ℝ) : Fin 4 → ℝ := ![t * w, -w, -t, 1]

def normalizedSpectralJacobian (p H h t w : ℝ) : Matrix (Fin 3) (Fin 4) ℝ :=
  let d := spectralChartEntries t w h
  let n := spectralChartEntries t w H
  ![fun j => (p - 1) * (H * spectralChartTangentH t w j * d j -
        h * n j * spectralChartTangentH t w j),
    fun j => (p - 2) * t * n j * d j + (1 + t ^ 2) *
      (spectralChartTangentT w H j * d j - (p - 1) * n j * spectralChartTangentT w h j),
    fun j => (p - 2) * w * n j * d j + (1 + w ^ 2) *
      (spectralChartTangentW t H j * d j - (p - 1) * n j * spectralChartTangentW t h j)]

theorem normalizedSpectralJacobian_first_row (p H h t w : ℝ) :
    normalizedSpectralJacobian p H h t w 0 =
      ((p - 1) * t * w * (H - h)) • (![1, -1, -1, 1] : Fin 4 → ℝ) := by
  funext j
  fin_cases j <;>
    simp [normalizedSpectralJacobian, spectralChartEntries, spectralChartTangentH] <;> ring

theorem normalizedSpectralJacobian_sums (p H h t w : ℝ) :
    normalizedSpectralJacobian p H h t w 1 0 +
      normalizedSpectralJacobian p H h t w 1 1 = p * w * (1 + t ^ 2) * (H - h) ∧
    normalizedSpectralJacobian p H h t w 1 0 +
      normalizedSpectralJacobian p H h t w 1 2 = (p - 2) * t * (1 + w ^ 2) * (1 - h * H) ∧
    normalizedSpectralJacobian p H h t w 2 0 +
      normalizedSpectralJacobian p H h t w 2 2 = p * t * (1 + w ^ 2) * (H - h) ∧
    normalizedSpectralJacobian p H h t w 2 0 +
      normalizedSpectralJacobian p H h t w 2 1 = (p - 2) * w * (1 + t ^ 2) * (1 - h * H) := by
  simp [normalizedSpectralJacobian, spectralChartEntries, spectralChartTangentT,
    spectralChartTangentW]
  constructor
  · ring
  constructor
  · ring
  constructor <;> ring

def spectralJacobianMinor (p H h t w : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => normalizedSpectralJacobian p H h t w i j.castSucc

theorem spectralJacobianMinor_det (p H h t w : ℝ) :
    (spectralJacobianMinor p H h t w).det =
      (p - 1) * t ^ 2 * w ^ 2 * (1 + t ^ 2) * (1 + w ^ 2) * (H - h) *
        (p ^ 2 * (H - h) ^ 2 - (p - 2) ^ 2 * (1 - h * H) ^ 2) := by
  let M := normalizedSpectralJacobian p H h t w
  let r := (p - 1) * t * w * (H - h)
  have h0 : M 0 0 = r := by
    simp [M, r, normalizedSpectralJacobian_first_row]
  have h1 : M 0 1 = -r := by
    simp [M, r, normalizedSpectralJacobian_first_row]
  have h2 : M 0 2 = -r := by
    simp [M, r, normalizedSpectralJacobian_first_row]
  have he : (spectralJacobianMinor p H h t w).det =
      r * ((M 1 0 + M 1 1) * (M 2 0 + M 2 2) -
        (M 1 0 + M 1 2) * (M 2 0 + M 2 1)) := by
    rw [Matrix.det_fin_three]
    change M 0 0 * M 1 1 * M 2 2 - M 0 0 * M 1 2 * M 2 1 -
      M 0 1 * M 1 0 * M 2 2 + M 0 1 * M 1 2 * M 2 0 +
      M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0 = _
    rw [h0, h1, h2]
    ring
  obtain ⟨ht1, ht2, hw2, hw1⟩ := normalizedSpectralJacobian_sums p H h t w
  rw [he, ht1, ht2, hw1, hw2]
  dsimp [r]
  ring

theorem spectralJacobianMinor_ne_zero {p h t w : ℝ}
    (hp : 1 < p) (hp2 : p ≠ 2) (hh : 0 < h) (hh1 : h < 1)
    (ht : 0 < t) (hw : 0 < w) :
    (spectralJacobianMinor p (h ^ (p - 1)) h t w).det ≠ 0 := by
  rw [spectralJacobianMinor_det]
  have hpw : h * h ^ (p - 1) = h ^ p := by
    calc
      _ = h ^ (1 : ℝ) * h ^ (p - 1) := by rw [Real.rpow_one]
      _ = h ^ p := by rw [← Real.rpow_add hh]; congr 1; ring
  rw [hpw]
  have hk : p ^ 2 * (h ^ (p - 1) - h) ^ 2 -
      (p - 2) ^ 2 * (1 - h ^ p) ^ 2 ≠ 0 :=
    (spectralJacobianFactor_negative hp hp2 hh hh1).ne
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (mul_ne_zero (by linarith) (pow_ne_zero _ ht.ne')) (pow_ne_zero _ hw.ne'))
      (by positivity)) (by positivity))
        (spectralJacobian_power_difference_ne_zero hp2 hh hh1)) hk

end

end ResearchMain.DiagonalSchatten
