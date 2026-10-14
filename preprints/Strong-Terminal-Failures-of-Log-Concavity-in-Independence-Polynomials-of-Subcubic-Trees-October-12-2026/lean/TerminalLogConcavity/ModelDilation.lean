import TerminalLogConcavity.CoefficientDilation
import TerminalLogConcavity.PathEnvelope
import TerminalLogConcavity.LowerWeights

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial

noncomputable def modelDilationRate (q t : ℕ) : ℝ :=
  Real.exp (4 * (massParameter q + q : ℕ) / (amplifier t : ℝ))
noncomputable def parameterScale (t p : ℕ) : ℝ :=
  Real.exp (2 * (p : ℝ) / (amplifier t : ℝ))

theorem parameterScale_ge_one (t p : ℕ) : 1 ≤ parameterScale t p := by
  apply Real.one_le_exp_iff.mpr
  positivity

theorem scaled_d_square_dilation {q i : ℕ} (hi : i ≤ q) (hq : 1 ≤ q) (t : ℕ) :
    ((Block.scaled t (interfaceParameter q i)).d ^ 2 : ℕ) ≤
      modelDilationRate q t * (amplifier t ^ (2 * interfaceParameter q i) : ℕ) := by
  have ha : 0 < (amplifier t : ℝ) := by exact_mod_cast amplifier_pos t
  have hm : 1 ≤ interfaceParameter q i := by
    unfold interfaceParameter massParameter
    have : 0 < q^2 := by positivity
    omega
  have h := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (Block.scaled t (interfaceParameter q i)).d)
    (Block.scaled_d_upper_exp t hm) 2
  have hex : Real.exp (2 * (interfaceParameter q i : ℝ) / amplifier t) ^ 2 ≤ modelDilationRate q t := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    have hm' : (interfaceParameter q i : ℝ) ≤ (massParameter q + q : ℕ) := by exact_mod_cast interfaceParameter_le hi
    dsimp [modelDilationRate]
    rw [← mul_div_assoc]
    apply (div_le_div_iff_of_pos_right ha).mpr
    nlinarith
  rw [mul_pow] at h
  have h' := mul_le_mul_of_nonneg_left hex (by positivity : (0:ℝ) ≤ ((amplifier t : ℝ)^interfaceParameter q i)^2)
  have hh := h.trans h'
  push_cast
  convert hh using 1 ; rw [← pow_mul] ; ring_nf

noncomputable def ChainNode.parameter (q i : ℕ) : ChainNode → ℕ
  | .site k => siteParameter q i k
  | .coupler => 2*baseCoupling q
noncomputable def ChainNode.lowerWeight (q t i : ℕ) : ChainNode → ℕ[X] × ℕ[X]
  | .site k => lowerSiteWeight q t i k
  | .coupler => lowerCouplerWeight q t

theorem node_model_dilation {q i : ℕ} (hq : 1 ≤ q) (hi : i ≤ q) (t : ℕ) (v : ChainNode) :
    DilationBound (v.upperWeight q t i).1 (v.lowerWeight q t i).1
      (parameterScale t (v.parameter q i)) (modelDilationRate q t) ∧
    DilationBound (v.upperWeight q t i).2 (v.lowerWeight q t i).2
      (parameterScale t (v.parameter q i)) (modelDilationRate q t) := by
  cases v with
  | site k =>
    have hp : 1 ≤ siteParameter q i k := by have := siteParameter_pos (i := i) (k := k) hq; omega
    have hs := parameterScale_ge_one t (siteParameter q i k)
    have hsq := scaled_d_square_dilation hi hq t
    have hP : DilationBound (interfaceUpperP (Block.scaled t (interfaceParameter q i))) (lowerSiteP q t i)
        (parameterScale t (siteParameter q i k)) (modelDilationRate q t) := by
      apply DilationBound.linear hs
      have hh := mul_le_mul_of_nonneg_right hs (show (0:ℝ) ≤ modelDilationRate q t * (amplifier t ^ (2*interfaceParameter q i) : ℕ) by unfold modelDilationRate; positivity)
      push_cast at hsq hh ⊢
      nlinarith
    have hC : DilationBound (C (Block.scaled t (siteParameter q i k)).d)
        (C (amplifier t ^ siteParameter q i k)) (parameterScale t (siteParameter q i k)) (modelDilationRate q t) := by
      apply DilationBound.constant
      simpa only [parameterScale,ChainNode.parameter,Nat.cast_pow,mul_comm] using Block.scaled_d_upper_exp t hp
    exact ⟨hP,hP.add hC⟩
  | coupler =>
    have hp : 1 ≤ 2*baseCoupling q := by
      unfold baseCoupling
      have : 0 < q^2 := by positivity
      omega
    refine ⟨DilationBound.one (parameterScale_ge_one _ _),DilationBound.constant ?_⟩
    simpa only [parameterScale,ChainNode.parameter,Nat.cast_pow,mul_comm] using Block.scaled_d_upper_exp t hp

end TerminalLogConcavity
