import CircleKernel.Definitions

noncomputable section
open Complex MeasureTheory Filter
open scoped Topology
namespace CircleKernel

theorem circleEigenvalue_harmonic (n : ℕ) :
    circleEigenvalue n=4*(harmonic (2*n):ℝ)-2*(harmonic n:ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [circleEigenvalue_succ,ih,show 2*(n+1)=2*n+1+1 by omega,
      harmonic_succ,harmonic_succ,harmonic_succ]
    push_cast
    have hn : (n:ℝ)+1≠0 := by positivity
    have hn2 : 2*(n:ℝ)+1≠0 := by positivity
    field_simp
    ring

def spectralConstant : ℝ := 4*Real.log 2+2*Real.eulerMascheroniConstant

theorem circleEigenvalue_log_limit :
    Tendsto (fun n:ℕ=>circleEigenvalue n-2*Real.log n) atTop (𝓝 spectralConstant) := by
  have htwo : Tendsto (fun n:ℕ=>2*n) atTop atTop :=
    tendsto_atTop_mono (fun n=>by omega : ∀n:ℕ,n≤2*n) tendsto_id
  have h := ((Real.tendsto_harmonic_sub_log.comp htwo).const_mul 4).sub
    (Real.tendsto_harmonic_sub_log.const_mul 2)
  have h' := h.add_const (4*Real.log 2)
  have hc : 4*Real.eulerMascheroniConstant-2*Real.eulerMascheroniConstant+4*Real.log 2=
      spectralConstant := by unfold spectralConstant; ring
  rw [hc] at h'
  apply h'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [circleEigenvalue_harmonic]
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt (by omega : 0<n)
  simp only [Function.comp_apply,Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num : (2:ℝ)≠0) hn0]
  ring

end CircleKernel
