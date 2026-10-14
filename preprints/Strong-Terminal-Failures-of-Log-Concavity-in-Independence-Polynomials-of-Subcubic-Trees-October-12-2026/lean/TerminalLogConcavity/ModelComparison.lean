import TerminalLogConcavity.ModelDilation
import TerminalLogConcavity.ChainLower

namespace TerminalLogConcavity
open Polynomial
open scoped Polynomial BigOperators

noncomputable def chainParameterSum (q i : ℕ) : ℕ :=
  ((chainNodes q).map (ChainNode.parameter q i)).sum

theorem parameterScale_prod (t : ℕ) (l : List ℕ) :
    (l.map (parameterScale t)).prod = parameterScale t l.sum := by
  induction l with
  | nil => simp [parameterScale]
  | cons p l ih =>
    simp only [List.map_cons,List.prod_cons,List.sum_cons,ih,parameterScale,Nat.cast_add]
    rw [← Real.exp_add]
    congr 1
    ring

theorem chain_model_dilation {q i : ℕ} (hq : 1 ≤ q) (hi : i ≤ q) (t : ℕ) :
    DilationBound (upperChain q t i) (lowerChain q t i)
      (parameterScale t (chainParameterSum q i)) (modelDilationRate q t) := by
  have h := (weightedPath_dilation (chainNodes q) (ChainNode.upperWeight q t i)
    (ChainNode.lowerWeight q t i) (fun v => parameterScale t (v.parameter q i))
    (by unfold modelDilationRate; positivity)
    (fun v _ => (show 0 ≤ parameterScale t (v.parameter q i) from (by unfold parameterScale; positivity)))
    (fun v _ => node_model_dilation hq hi t v)).1
  have he : (weightedPath ((chainNodes q).map (ChainNode.lowerWeight q t i))).1 = lowerChain q t i := by
    simp only [chainNodes,map_intersperse,List.map_map,Function.comp_def,ChainNode.lowerWeight,lowerChain]
  rw [he] at h
  have hs : ((chainNodes q).map (fun v => parameterScale t (v.parameter q i))).prod =
      parameterScale t (chainParameterSum q i) := by
    simpa only [List.map_map,Function.comp_def,chainParameterSum] using
      parameterScale_prod t ((chainNodes q).map (ChainNode.parameter q i))
  rw [hs] at h
  exact h

theorem sum_map_intersperse_nat {α : Type*} (f : α → ℕ) (sep : α) (l : List α) :
    ((l.intersperse sep).map f).sum = (l.map f).sum + (l.length-1)*f sep := by
  induction l with
  | nil => simp
  | cons a l ih =>
    cases l with
    | nil => simp
    | cons b l =>
      simp only [List.intersperse_cons_cons,List.map_cons,List.sum_cons,List.length_cons] at *
      rw [ih]
      simp only [Nat.add_sub_cancel]
      ring

theorem chainParameterSum_eq {q : ℕ} (hq : 2 ≤ q) (i : ℕ) :
    chainParameterSum q i = 4*baseCoupling q*(q-1)+i^2 := by
  unfold chainParameterSum chainNodes
  rw [sum_map_intersperse_nat]
  simp only [List.map_map,Function.comp_def,ChainNode.parameter,List.length_map,List.length_range]
  rw [site_parameter_sum_nat hq]
  ring

theorem total_parameterSum_le {q : ℕ} (hq : 2 ≤ q) :
    (∑ i ∈ Finset.range q, chainParameterSum q (i+1)) ≤ 8*q^4 := by
  simp_rw [chainParameterSum_eq hq]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have hs := squareSum_le_cube q
  change q*(4*baseCoupling q*(q-1))+squareSum q ≤ _
  unfold baseCoupling
  have hq' : q-1+1=q := by omega
  have he : q*(4*(2*q^2)*(q-1))+8*q^3 = 8*q^4 := by nlinarith [congrArg (fun x => 8*q^3*x) hq']
  omega

theorem parameterScale_finset_prod {α : Type*} (t : ℕ) (S : Finset α) (f : α → ℕ) :
    (∏ i ∈ S, parameterScale t (f i)) = parameterScale t (∑ i ∈ S, f i) := by
  simp only [parameterScale]
  rw [← Real.exp_sum]
  congr 1
  simp only [Nat.cast_sum,Finset.sum_div,Finset.mul_sum]

theorem upperChain_product_coeff_le {q : ℕ} (hq : 2 ≤ q) (t j : ℕ)
    (ha : 128*q^4 ≤ amplifier t) (hj : j ≤ q) :
    ((∏ i ∈ Finset.range q, upperChain q t (i+1)).coeff j : ℝ) ≤
      2 * ((∏ i ∈ Finset.range q, lowerChain q t (i+1)).coeff j : ℝ) := by
  have h := DilationBound.prod (Finset.range q) (fun i => upperChain q t (i+1))
    (fun i => lowerChain q t (i+1)) (fun i => parameterScale t (chainParameterSum q (i+1)))
    (by unfold modelDilationRate; positivity)
    (fun i _ => by unfold parameterScale; positivity)
    (fun i hi => chain_model_dilation (by omega) (by have := Finset.mem_range.mp hi; omega) t)
  rw [parameterScale_finset_prod] at h
  have hj' := h j
  have hS := total_parameterSum_le hq
  have htotal : 2*(∑ i ∈ Finset.range q, chainParameterSum q (i+1)) +
      4*j*(massParameter q+q) ≤ 26*q^4 := by
    have hjmul := Nat.mul_le_mul_right (4*(massParameter q+q)) hj
    have hp : 16*q^3+4*q^2 ≤ 10*q^4 := by
      have hh : 16*q+4 ≤ 10*q^2 := by nlinarith
      have hh' := Nat.mul_le_mul_right (q^2) hh
      nlinarith only [hh']
    unfold massParameter at *
    nlinarith
  have ha0 : 0 < (amplifier t : ℝ) := by exact_mod_cast amplifier_pos t
  have hfactor : parameterScale t (∑ i ∈ Finset.range q,chainParameterSum q (i+1)) *
      modelDilationRate q t ^ j ≤ 2 := by
    unfold parameterScale modelDilationRate
    rw [← Real.exp_nat_mul,← Real.exp_add]
    apply exp_le_two_of_le_half
    · positivity
    · have hn : (2*(∑ i ∈ Finset.range q,chainParameterSum q (i+1)) : ℕ) +
          (4*j*(massParameter q+q) : ℕ) ≤ (amplifier t : ℝ)/2 := by
        have ht : (2*(∑ i ∈ Finset.range q,chainParameterSum q (i+1)) +4*j*(massParameter q+q) : ℕ) ≤ (26*q^4 : ℕ) := htotal
        have ht' : ((2*(∑ i ∈ Finset.range q,chainParameterSum q (i+1)) +4*j*(massParameter q+q) : ℕ) : ℝ) ≤ 26*(q:ℝ)^4 := by exact_mod_cast ht
        have ha' : 128*(q:ℝ)^4 ≤ amplifier t := by exact_mod_cast ha
        push_cast at ht' ⊢
        nlinarith
      have he : 2*(∑ i ∈ Finset.range q,chainParameterSum q (i+1) : ℕ)/(amplifier t : ℝ) +
          (j:ℝ)*(4*(massParameter q+q : ℕ)/(amplifier t : ℝ)) =
          ((2*(∑ i ∈ Finset.range q,chainParameterSum q (i+1)) +4*j*(massParameter q+q) : ℕ) : ℝ)/(amplifier t : ℝ) := by
        push_cast
        ring
      rw [he]
      apply (div_le_iff₀ ha0).mpr
      push_cast at hn ⊢
      nlinarith
  exact hj'.trans (mul_le_mul_of_nonneg_right hfactor (by positivity))

end TerminalLogConcavity
