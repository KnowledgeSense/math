import HardCoreActivityThreshold.ScalarFunctions

namespace HardCoreActivityThreshold

theorem logarithm_enclosure (a b l u : ℚ) (ka kb : ℤ) (n : ℕ)
    (ha : 0<a) (hb : 0<b) (hka : 1≤a*2^ka) (hkb : 1≤b*2^kb)
    (hl : l≤scaledLogLower a ka n) (hu : scaledLogUpper b kb n≤u)
    (v : ℝ) (hv : v∈Set.Icc (a : ℝ) (b : ℝ)) :
    Real.log v∈Set.Icc (l : ℝ) (u : ℝ) := by
  have ha' : (0 : ℝ)<a := by exact_mod_cast ha
  have hb' : (0 : ℝ)<b := by exact_mod_cast hb
  have hp : 0<v := ha'.trans_le hv.1
  have hlo := (scaledLog_bounds a ka n ha hka).1
  have hhi := (scaledLog_bounds b kb n hb hkb).2
  have hl' : (l : ℝ)≤scaledLogLower a ka n := by exact_mod_cast hl
  have hu' : (scaledLogUpper b kb n : ℝ)≤u := by exact_mod_cast hu
  exact ⟨hl'.trans (hlo.trans (Real.strictMonoOn_log.monotoneOn ha' hp hv.1)),
    (Real.strictMonoOn_log.monotoneOn hp hb' hv.2).trans (hhi.trans hu')⟩

theorem occupation_remaining_ratio (x : ℝ) (hx : 0<x) :
    criticalActivity/(Real.exp x-1)=criticalActivity*(1-scalarOccupation x)/scalarOccupation x := by
  have hq := (occupation_pos x hx).ne'
  have he := occupation_exp_identity x
  have hr := (exp_sub_one_pos x hx).ne'
  have hc : (1-scalarOccupation x)*Real.exp x=1 := by
    simp [scalarOccupation,Real.exp_neg]
  field_simp
  nlinarith [congrArg (fun t : ℝ => criticalActivity*t) hc,
    congrArg (fun t : ℝ => criticalActivity*(1-scalarOccupation x)*t) he]

theorem remaining_ratio_bounds (a b L U : ℝ) (ha : 0<a) (hb : b<1)
    (hab : a≤b) (hL : 0<L) (hU : L≤U) (q v : ℝ)
    (hq : q∈Set.Icc a b) (hv : v∈Set.Icc L U) :
    v*(1-q)/q∈Set.Icc (L*(1-b)/b) (U*(1-a)/a) := by
  have hqp : 0<q := ha.trans_le hq.1
  have hbp : 0<b := ha.trans_le hab
  have hqc : 0≤1-q := by linarith [hq.2]
  have hvp : 0≤v := hL.le.trans hv.1
  have hUa : 0≤U*(1-a) := mul_nonneg (hL.le.trans hU) (by linarith)
  have hlo1 : L*(1-b)≤v*(1-q) := by nlinarith [hv.1,hq.2]
  have hhi1 : v*(1-q)≤U*(1-a) := by nlinarith [hv.2,hq.1]
  constructor
  · exact div_le_div₀ (mul_nonneg hvp hqc) hlo1 hqp hq.2
  · exact div_le_div₀ hUa hhi1 ha hq.1

end HardCoreActivityThreshold
