import SumsetRanges.ParameterInterval
import SumsetRanges.DenseEndpoint

open Finset Polynomial
namespace SumsetRanges
open scoped Classical

noncomputable def baselineValue (h c b x : ℕ) : ℤ :=
  ((1+X)^c*restrictedPolynomial (denseSet (b-1) x)).coeff h

@[simp] theorem repetitionParameters_zero (h : ℕ) : repetitionParameters h (fun _ => 0)=fun _ => 0 := by
  funext m
  simp [repetitionParameters]
@[simp] theorem sharedParameters_zero (h : ℕ) : sharedParameters h (fun _ => 0)=fun _ => 1 := by
  funext m
  simp [sharedParameters]

theorem baseline_nonfree_bound (h c : ℕ) (hh : 2≤h) (hc : (32*h^3)^10≤c) :
    nonfreeSize h (fun _ => 0) (fun _ => 1)≤c := by
  have hS := (large_caps_positive (by omega : 1≤h) hc).2
  have hn := nonfreeSize_box_bound h c (fun _ => 0) (fun _ => 1) (by omega) hc
    (fun _ _ => Nat.zero_le _) (fun _ _ => by omega)
  have ht := Nat.le_mul_of_pos_left (nonfreeSize h (fun _ => 0) (fun _ => 1)) (by omega : 0<8*h)
  omega

theorem parameterValue_zero (h c b : ℕ) (hh : 2≤h) (hc : (32*h^3)^10≤c) :
    parameterValue h c b (fun _ => 0)=baselineValue h c b (denseMaximum h b) := by
  simp only [parameterValue,repetitionParameters_zero,sharedParameters_zero,Nat.sub_zero,
    largeValue,sparsePolynomial_baseline h c (baseline_nonfree_bound h c hh hc),baselineValue]

theorem parameterValue_dense_baseline (h c b a : ℕ) (hh : 2≤h) (hc : (32*h^3)^10≤c) :
    parameterValue h c b (Function.update (fun _ => 0) (denseIndex h) a)=
      baselineValue h c b (denseMaximum h b-a) := by
  rw [parameterValue_update_dense]
  simp only [repetitionParameters_zero,sharedParameters_zero,largeValue,
    sparsePolynomial_baseline h c (baseline_nonfree_bound h c hh hc),baselineValue]

theorem baseline_interval_realized (h c b : ℕ) (hh : 2≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b)
    (hkc : sparseThreshold (c+b)≤c) (z : ℤ)
    (hz : baselineValue h c b (b-1)≤z)
    (hz' : z≤baselineValue h c b (denseMaximum h b)) :
    ∃B : Finset ℤ,B.card=c+b ∧ (∀a∈B,0≤a ∧ a≤((c+b)^(restrictedExponent h):ℕ)) ∧
      ((restrictedSums B h).card : ℤ)=z := by
  apply parameter_interval_realized h c b hh hc hb hkc z
  · let v := Function.update (fun _ => 0) (denseIndex h) (denseWidth h b)
    have hv : InNatBox (admissibleCaps h c b) v :=
      inNatBox_update _ _ (fun _ => Nat.zero_le _) _ _ (by simp [admissibleCaps])
    have ha := parameter_antitone h c b hh hc hb v (admissibleCaps h c b) hv
      (fun _ => le_refl _) hv
    have he : parameterValue h c b v=baselineValue h c b (b-1) := by
      rw [show v=Function.update (fun _ => 0) (denseIndex h) (denseWidth h b) from rfl,
        parameterValue_dense_baseline h c b _ hh hc]
      have hm := denseMaximum_ge h b (by omega) hb
      have heq : denseMaximum h b-denseWidth h b=b-1 := by unfold denseWidth; omega
      rw [heq]
    rw [he] at ha
    exact ha.trans hz
  · rwa [parameterValue_zero h c b hh hc]

theorem baseline_ordered (h c b : ℕ) (hh : 2≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b) :
    baselineValue h c b (b-1)≤baselineValue h c b (denseMaximum h b) := by
  let v := Function.update (fun _ => 0) (denseIndex h) (denseWidth h b)
  have hv : InNatBox (admissibleCaps h c b) v :=
    inNatBox_update _ _ (fun _ => Nat.zero_le _) _ _ (by simp [admissibleCaps])
  have ha := parameter_antitone h c b hh hc hb (fun _ => 0) v (fun _ => Nat.zero_le _) hv
    (fun _ => Nat.zero_le _)
  rw [parameterValue_zero h c b hh hc] at ha
  change parameterValue h c b (Function.update (fun _ => 0) (denseIndex h) (denseWidth h b))≤_ at ha
  rw [parameterValue_dense_baseline h c b _ hh hc] at ha
  have hm := denseMaximum_ge h b (by omega) hb
  have heq : denseMaximum h b-denseWidth h b=b-1 := by unfold denseWidth; omega
  rwa [heq] at ha

end SumsetRanges
