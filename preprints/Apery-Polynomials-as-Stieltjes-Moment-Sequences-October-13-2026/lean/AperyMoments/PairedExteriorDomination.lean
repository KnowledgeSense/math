import AperyMoments.PairedExteriorBounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section
namespace AperyMoments
open Complex Set Filter MeasureTheory
open scoped Topology

def exteriorPairedKernel (α δ R : ℝ) (z : ℂ) (y x : ℝ) : ℂ :=
  (Icc δ R)ᶜ.indicator (pairedMomentKernel α y z) x

theorem inverse_sqrt_abs_integrableOn (δ : ℝ) :
    IntegrableOn (fun x:ℝ=>1/Real.sqrt |x|) (Icc (-δ) δ) := by
  have hi := (norm_rpow_locallyIntegrable (by norm_num : (1/2:ℝ)<1)).integrableOn_isCompact
    (k := Icc (-δ) δ) isCompact_Icc
  convert hi using 1
  funext x
  rw [Real.norm_eq_abs,inverse_sqrt_rpow (abs_nonneg x)]
  exact one_div _

theorem exteriorPairedKernel_dominated {α : ℝ} {z : ℂ}
    (hα : 0<α) (hα1 : α≤1) (hz : 0<z.im) :
    ∃ δ R:ℝ, 0<δ ∧ 0<R ∧ δ<R ∧ ∃ B:ℝ→ℝ, Integrable B ∧
      (∀ x,0≤B x) ∧ ∀ᶠ y:ℝ in 𝓝[>] (0:ℝ),
        ∀ᵐ x:ℝ, ‖exteriorPairedKernel α δ R z y x‖≤B x := by
  obtain ⟨ε,A,hε,hA,hzero⟩ := pairedMomentKernel_zero_bound hα hz
  let δ := min (ε/2) 1
  let R := 257+2*|z.re|+δ
  have hδ : 0<δ := by dsimp [δ]; positivity
  have hδε : δ<ε := (min_le_left _ _).trans_lt (by linarith)
  have hR : 0<R := by dsimp [R]; positivity
  have hδR : δ<R := by dsimp [R]; linarith [abs_nonneg z.re]
  obtain ⟨C,hC,hneg⟩ := momentTransform_negative_compact_bound (R := R) hα hα1 hδ
  let D := 4*C/z.im
  have hD : 0≤D := by dsimp [D]; positivity
  let B := fun x:ℝ=>(Icc (-δ) δ).indicator (fun x=>A/Real.sqrt |x|) x+
    (Icc (-R) R).indicator (fun _=>D) x+16/(1+x^2)
  have hB0 (x : ℝ) : 0≤B x := by
    dsimp [B]
    exact add_nonneg (add_nonneg (indicator_nonneg (fun _ _=>by positivity) x)
      (indicator_nonneg (fun _ _=>hD) x)) (by positivity)
  have hBI : Integrable B := by
    have h1 : Integrable ((Icc (-δ) δ).indicator (fun x:ℝ=>A/Real.sqrt |x|)) := by
      apply IntegrableOn.integrable_indicator _ measurableSet_Icc
      change Integrable (fun x:ℝ=>A/Real.sqrt |x|) (volume.restrict (Icc (-δ) δ))
      simpa only [mul_one_div] using (inverse_sqrt_abs_integrableOn δ).const_mul A
    have h2 : Integrable ((Icc (-R) R).indicator (fun _:ℝ=>D)) :=
      continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
    have h3 : Integrable (fun x:ℝ=>16/(1+x^2)) := by
      simpa only [div_eq_mul_inv] using integrable_inv_one_add_sq.const_mul 16
    exact (h1.add h2).add h3
  refine ⟨δ,R,hδ,hR,hδR,B,hBI,hB0,?_⟩
  have hev : ∀ᶠ y:ℝ in 𝓝[>] (0:ℝ), 0<y ∧ y<ε ∧ y≤1 ∧ y≤z.im/2 := by
    filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (Iio_mem_nhds hε),
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0:ℝ)<1)),
      nhdsWithin_le_nhds (Iio_mem_nhds (by positivity : (0:ℝ)<z.im/2))] with y hy hyε hy1 hyz
    exact ⟨hy,hyε,hy1.le,hyz.le⟩
  filter_upwards [hev] with y hy
  have hne : ∀ᵐ x:ℝ,x≠0 := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_eq_eq_singleton] using (measure_singleton (0:ℝ) : volume {(0:ℝ)}=0)
  filter_upwards [hne] with x hx0
  by_cases hx : x∈Icc δ R
  · rw [exteriorPairedKernel,indicator_of_notMem (by simpa using hx),norm_zero]
    exact hB0 x
  · rw [exteriorPairedKernel,indicator_of_mem hx]
    by_cases hsmall : |x|≤δ
    · have hmem : x∈Icc (-δ) δ := abs_le.mp hsmall
      have hb := hzero x y (hsmall.trans_lt hδε) hy.1 hy.2.1 hy.2.2.2 hx0
      dsimp [B]
      rw [indicator_of_mem hmem]
      have hn1 := indicator_nonneg (s := Icc (-R) R) (fun _ _=>hD) x
      have hn2 : 0≤16/(1+x^2) := by positivity
      linarith
    · by_cases hmid : |x|≤R
      · have hxneg : x≤ -δ := by
          have habs := abs_le.mp hmid
          rcases le_total x 0 with hn | hp
          · rw [abs_of_nonpos hn] at hsmall
            linarith
          · exact False.elim (hx ⟨by rw [abs_of_nonneg hp] at hsmall; linarith, habs.2⟩)
        have hm := hneg x y (abs_le.mp hmid).1 hxneg hy.1.le hy.2.2.1
        have hk := pairedCauchyKernel_norm_bound hz hy.1.le hy.2.2.2
          (momentTransform α ((x:ℂ)+y*I)) x
        have hd : ‖pairedMomentKernel α y z x‖≤D := hk.trans
          (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by norm_num)) hz.le)
        dsimp [B]
        rw [indicator_of_mem (show x∈Icc (-R) R from abs_le.mp hmid)]
        have hn1 := indicator_nonneg (s := Icc (-δ) δ) (fun x _=>show 0≤A/Real.sqrt |x| by positivity) x
        have hn2 : 0≤16/(1+x^2) := by positivity
        linarith
      · have hlarge : 256≤|x| := by dsimp [R] at hmid; linarith [abs_nonneg z.re]
        have hxz : 2*|z.re|≤|x| := by dsimp [R] at hmid; linarith
        have hk := pairedMomentKernel_tail_bound hα hα1 hy.1 hlarge hxz
        have hs : 1≤x^2 := by nlinarith [sq_abs x]
        have ht : 8/|x|^2≤16/(1+x^2) := by
          rw [sq_abs]
          apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
          nlinarith
        dsimp [B]
        have hn1 := indicator_nonneg (s := Icc (-δ) δ) (fun x _=>show 0≤A/Real.sqrt |x| by positivity) x
        have hn2 := indicator_nonneg (s := Icc (-R) R) (fun _ _=>hD) x
        linarith

end AperyMoments
