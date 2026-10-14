import MainTheorems.DiagonalSchatten.RealTwoRowPower
import MainTheorems.DiagonalSchatten.CompressionFunctional

namespace ResearchMain.DiagonalSchatten

noncomputable section

open scoped BigOperators Matrix.Norms.Elementwise

variable {J : Type*} [Fintype J] [DecidableEq J]

def realEntryRoot (p : ℝ) (B : Matrix (Fin 2) J ℝ) : Matrix (Fin 2) J ℝ :=
  Matrix.of fun i j => B i j ^ (1 / p)

theorem compressionFunctional_eq_realEntryRoot (p : ℝ) (B : Matrix (Fin 2) J ℝ) :
    compressionFunctional p B = schattenPower p (complexifyRows (realEntryRoot p B)) := rfl

omit [Fintype J] [DecidableEq J] in
theorem continuous_realEntryRoot {p : ℝ} (hp : 0 < p) :
    Continuous (realEntryRoot (J := J) p) := by
  change Continuous (fun B : Matrix (Fin 2) J ℝ => fun i j => B i j ^ (1 / p))
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact (Real.continuous_rpow_const (one_div_pos.mpr hp).le).comp (by fun_prop)

theorem continuous_schattenPower_complexify {p : ℝ} (hp : 0 < p) :
    Continuous (fun X : Matrix (Fin 2) J ℝ => schattenPower p (complexifyRows X)) := by
  have heq : (fun X : Matrix (Fin 2) J ℝ => schattenPower p (complexifyRows X)) =
      (fun X => realGramPlus X ^ (p / 2) + realGramMinus X ^ (p / 2)) :=
    funext (schattenPower_complexify hp)
  rw [heq]
  have hpow : Continuous (fun x : ℝ => x ^ (p / 2)) :=
    Real.continuous_rpow_const (by linarith)
  exact (hpow.comp (by unfold realGramPlus gramFirst gramSecond gramCross; fun_prop)).add
    (hpow.comp (by unfold realGramMinus gramFirst gramSecond gramCross; fun_prop))

theorem continuous_compressionFunctional {p : ℝ} (hp : 0 < p) :
    Continuous (compressionFunctional (J := J) p) := by
  have heq : compressionFunctional (J := J) p =
      (fun X => schattenPower p (complexifyRows X)) ∘ realEntryRoot p := rfl
  rw [heq]
  exact (continuous_schattenPower_complexify hp).comp (continuous_realEntryRoot hp)

omit [DecidableEq J] in
theorem contDiffAt_realEntryRoot {n : WithTop ℕ∞} (p : ℝ) (B : Matrix (Fin 2) J ℝ)
    (hB : ∀ i j, 0 < B i j) : ContDiffAt ℝ n (realEntryRoot p) B := by
  change ContDiffAt ℝ n (fun X : Matrix (Fin 2) J ℝ => fun i j => X i j ^ (1 / p)) B
  apply contDiffAt_pi.mpr
  intro i
  apply contDiffAt_pi.mpr
  intro j
  have hcoord : ContDiffAt ℝ n (fun X : Matrix (Fin 2) J ℝ => X i j) B := by fun_prop
  exact hcoord.rpow_const_of_ne (hB i j).ne'

theorem contDiffAt_compressionFunctional [Nonempty J] {p : ℝ} (hp : 1 < p)
    (B : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j) :
    ContDiffAt ℝ 1 (compressionFunctional p) B := by
  let X := realEntryRoot p B
  have hX : ∀ i j, 0 < X i j := fun i j => Real.rpow_pos_of_pos (hB i j) _
  have hc : 0 < gramCross X :=
    Finset.sum_pos (fun j _ => mul_pos (hX 0 j) (hX 1 j)) Finset.univ_nonempty
  have ha : 0 < gramFirst X :=
    Finset.sum_pos (fun j _ => sq_pos_of_pos (hX 0 j)) Finset.univ_nonempty
  have hb : 0 ≤ gramSecond X := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have heq : compressionFunctional (J := J) p =
      (fun Y => schattenPower p (complexifyRows Y)) ∘ realEntryRoot p := rfl
  rw [heq]
  exact (contDiffAt_schattenPower_complexify hp X hc.ne' (by linarith)).comp B
    (contDiffAt_realEntryRoot p B hB)

theorem contDiffAt_compressionFunctional_fullRank [Nonempty J] {n : WithTop ℕ∞}
    {p : ℝ} (hp : 0 < p) (B : Matrix (Fin 2) J ℝ) (hB : ∀ i j, 0 < B i j)
    (hdet : 0 < gramFirst (realEntryRoot p B) * gramSecond (realEntryRoot p B) -
      gramCross (realEntryRoot p B) ^ 2) : ContDiffAt ℝ n (compressionFunctional p) B := by
  let X := realEntryRoot p B
  have hX : ∀ i j, 0 < X i j := fun i j => Real.rpow_pos_of_pos (hB i j) _
  have hc : 0 < gramCross X :=
    Finset.sum_pos (fun j _ => mul_pos (hX 0 j) (hX 1 j)) Finset.univ_nonempty
  have heq : compressionFunctional (J := J) p =
      (fun Y => schattenPower p (complexifyRows Y)) ∘ realEntryRoot p := rfl
  rw [heq]
  exact (contDiffAt_schattenPower_complexify_fullRank hp X hc.ne' hdet).comp B
    (contDiffAt_realEntryRoot p B hB)

end

end ResearchMain.DiagonalSchatten
