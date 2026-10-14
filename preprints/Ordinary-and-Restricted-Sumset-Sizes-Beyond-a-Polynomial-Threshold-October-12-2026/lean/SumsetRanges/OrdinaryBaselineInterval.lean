import SumsetRanges.OrdinaryIntervalRealization
import SumsetRanges.OrdinaryBaselineGluing
import SumsetRanges.BaselineInterval

open Finset
namespace SumsetRanges
open scoped Classical

theorem ordinary_baseline_nonfree_bound (h c : ℕ) (hh : 3≤h) (hc : (32*h^3)^10≤c) :
    ordinaryNonfreeSize h (fun _ => 0) (fun _ => 1)≤c := by
  have hS := (large_caps_positive (by omega : 1≤h) hc).2
  have hn := ordinaryNonfreeSize_bound h c (fun _ => 0) (fun _ => 1) (by omega) hc
    (fun _ _ => Nat.zero_le _) (fun _ _ => by omega)
  have ht := Nat.le_mul_of_pos_left (ordinaryNonfreeSize h (fun _ => 0) (fun _ => 1)) (by omega : 0<4*h)
  omega

theorem ordinaryParameterValue_zero (h c b : ℕ) (hh : 3≤h) (hc : (32*h^3)^10≤c) :
    ordinaryParameterValue h c b (fun _ => 0)=ordinaryBaselineValue h c b (denseMaximum h b) := by
  simp only [ordinaryParameterValue,repetitionParameters_zero,sharedParameters_zero,Nat.sub_zero,
    ordinaryValue,ordinarySparseSeries_baseline h c (fun _ => 0) (fun _ => 1) (fun _ _ => rfl) (fun _ _ => rfl) (ordinary_baseline_nonfree_bound h c hh hc),ordinaryBaselineValue]

theorem ordinaryParameterValue_dense_baseline (h c b a : ℕ) (hh : 3≤h) (hc : (32*h^3)^10≤c) :
    ordinaryParameterValue h c b (Function.update (fun _ => 0) (denseIndex (h-1)) a)=
      ordinaryBaselineValue h c b (denseMaximum h b-a) := by
  rw [ordinaryParameterValue_update_dense]
  simp only [repetitionParameters_zero,sharedParameters_zero,ordinaryValue,
    ordinarySparseSeries_baseline h c (fun _ => 0) (fun _ => 1) (fun _ _ => rfl) (fun _ _ => rfl) (ordinary_baseline_nonfree_bound h c hh hc),ordinaryBaselineValue]

theorem ordinary_baseline_interval_realized (h c b : ℕ) (hh : 3≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b)
    (hkc : sparseThreshold (c+b)≤c) (z : ℤ)
    (hz : ordinaryBaselineValue h c b (b-1)≤z)
    (hz' : z≤ordinaryBaselineValue h c b (denseMaximum h b)) :
    ∃B : Finset ℤ,B.card=c+b ∧ (∀a∈B,0≤a ∧ a≤((c+b)^(ordinaryExponent h):ℕ)) ∧
      ((ordinarySums B h).card : ℤ)=z := by
  apply ordinary_parameter_interval_realized h c b hh hc hb hkc z
  · let v := Function.update (fun _ => 0) (denseIndex (h-1)) (denseWidth h b)
    have hv : InNatBox (ordinaryCaps h c b) v :=
      inNatBox_update _ _ (fun _ => Nat.zero_le _) _ _ (by simp [ordinaryCaps])
    have ha := ordinary_parameter_antitone h c b hh hc hb v (ordinaryCaps h c b) hv
      (fun _ => le_refl _) hv
    have he : ordinaryParameterValue h c b v=ordinaryBaselineValue h c b (b-1) := by
      rw [show v=Function.update (fun _ => 0) (denseIndex (h-1)) (denseWidth h b) from rfl,
        ordinaryParameterValue_dense_baseline h c b _ hh hc]
      have hm := denseMaximum_ge h b (by omega) hb
      have heq : denseMaximum h b-denseWidth h b=b-1 := by unfold denseWidth; omega
      rw [heq]
    rw [he] at ha
    exact ha.trans hz
  · rwa [ordinaryParameterValue_zero h c b hh hc]

theorem ordinary_baseline_ordered (h c b : ℕ) (hh : 3≤h) (hc : (32*h^3)^10≤c) (hb : 2≤b) :
    ordinaryBaselineValue h c b (b-1)≤ordinaryBaselineValue h c b (denseMaximum h b) := by
  let v := Function.update (fun _ => 0) (denseIndex (h-1)) (denseWidth h b)
  have hv : InNatBox (ordinaryCaps h c b) v :=
    inNatBox_update _ _ (fun _ => Nat.zero_le _) _ _ (by simp [ordinaryCaps])
  have ha := ordinary_parameter_antitone h c b hh hc hb (fun _ => 0) v (fun _ => Nat.zero_le _) hv
    (fun _ => Nat.zero_le _)
  rw [ordinaryParameterValue_zero h c b hh hc] at ha
  change ordinaryParameterValue h c b (Function.update (fun _ => 0) (denseIndex (h-1)) (denseWidth h b))≤_ at ha
  rw [ordinaryParameterValue_dense_baseline h c b _ hh hc] at ha
  have hm := denseMaximum_ge h b (by omega) hb
  have heq : denseMaximum h b-denseWidth h b=b-1 := by unfold denseWidth; omega
  rwa [heq] at ha

end SumsetRanges
