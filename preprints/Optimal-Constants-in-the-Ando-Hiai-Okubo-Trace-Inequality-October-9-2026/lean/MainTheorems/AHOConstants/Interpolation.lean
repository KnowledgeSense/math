import MainTheorems.AHOConstants.AnalyticPowers

namespace ResearchMain.AHOConstants

open Set
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

def StripBounded {E : Type*} [NormedAddCommGroup E] (f : ℂ → E) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖f z‖ ≤ C

theorem StripBounded.constant {E : Type*} [NormedAddCommGroup E] (a : E) :
    StripBounded (fun _ : ℂ => a) := ⟨‖a‖, norm_nonneg a, fun _ _ _ => le_rfl⟩

theorem StripBounded.mul {R : Type*} [NormedRing R] {f g : ℂ → R}
    (hf : StripBounded f) (hg : StripBounded g) : StripBounded (fun z => f z * g z) := by
  obtain ⟨a, ha, hf⟩ := hf
  obtain ⟨b, hb, hg⟩ := hg
  refine ⟨a * b, mul_nonneg ha hb, fun z hz₀ hz₁ => ?_⟩
  exact (norm_mul_le _ _).trans (mul_le_mul (hf z hz₀ hz₁) (hg z hz₀ hz₁)
    (norm_nonneg _) ha)

theorem StripBounded.list_product {R : Type*} [NormedRing R] (fs : List (ℂ → R))
    (hf : ∀ f ∈ fs, StripBounded f) :
    StripBounded (fun z => (fs.map (fun f => f z)).prod) := by
  revert hf
  induction fs with
  | nil =>
    intro _
    simpa only [List.map_nil, List.prod_nil] using StripBounded.constant (1 : R)
  | cons f fs ih =>
    intro hf
    have h₁ := hf f (by simp)
    have h₂ := ih (fun g hg => hf g (by simp [hg]))
    simpa only [List.map_cons, List.prod_cons] using h₁.mul h₂

theorem StripBounded.comp {E : Type*} [NormedAddCommGroup E] {f : ℂ → E}
    (hf : StripBounded f) (g : ℂ → ℂ)
    (hg : ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 0 ≤ (g z).re ∧ (g z).re ≤ 1) :
    StripBounded (f ∘ g) := by
  obtain ⟨C, hC, hf⟩ := hf
  exact ⟨C, hC, fun z hz₀ hz₁ => hf (g z) (hg z hz₀ hz₁).1 (hg z hz₀ hz₁).2⟩

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem StripBounded.trace {f : ℂ → Matrix I I ℂ} (hf : StripBounded f) :
    StripBounded (fun z => Matrix.trace (f z)) := by
  let T : Matrix I I ℂ →L[ℂ] ℂ := (Matrix.traceLinearMap I ℂ ℂ).toContinuousLinearMap
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨‖T‖ * C, mul_nonneg (norm_nonneg _) hC, fun z hz₀ hz₁ => ?_⟩
  exact (T.le_opNorm (f z)).trans (mul_le_mul_of_nonneg_left (hf z hz₀ hz₁) (norm_nonneg _))

theorem complexPower_stripBounded {A : Matrix I I ℂ} (hA : A.PosDef) :
    StripBounded (complexPower hA) := complexPower_bounded_strip hA

theorem scalar_three_lines {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hB : StripBounded f) {a b t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (ha : ∀ z : ℂ, z.re = 0 → ‖f z‖ ≤ a)
    (hb : ∀ z : ℂ, z.re = 1 → ‖f z‖ ≤ b) :
    ‖f (t : ℂ)‖ ≤ a ^ (1 - t) * b ^ t := by
  obtain ⟨C, _, hC⟩ := hB
  have hsup : BddAbove ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨C, ?_⟩
    rintro x ⟨z, hz, rfl⟩
    exact hC z hz.1 hz.2
  have hbound := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := f) (z := (t : ℂ)) (l := 0) (u := 1) (by norm_num)
    (show (t : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 from ⟨ht₀, ht₁⟩)
    hf.diffContOnCl hsup (fun z hz => ha z hz) (fun z hz => hb z hz)
  simpa only [Complex.ofReal_re, sub_zero, div_one] using hbound

end ResearchMain.AHOConstants
