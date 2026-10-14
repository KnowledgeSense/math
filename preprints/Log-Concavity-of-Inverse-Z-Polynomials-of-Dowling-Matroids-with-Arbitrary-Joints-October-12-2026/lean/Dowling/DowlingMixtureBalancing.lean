import Dowling.DowlingInverseZCandidateFixedRows

noncomputable section
namespace Dowling

/-- One genuine strict balancing step for the raised rising-factorial sequence. -/
theorem dowlingBinomialWeight_strict_step {p : ℝ} (hp : 1<p) (r s : ℕ) (hrs : r<s) :
    dowlingBinomialWeight p r*dowlingBinomialWeight p (s+1) <
      dowlingBinomialWeight p (r+1)*dowlingBinomialWeight p s := by
  have hr := dowlingBinomialWeight_succ p r
  have hs := dowlingBinomialWeight_succ p s
  have hp0 : 0<p := by linarith
  have hbr := dowlingBinomialWeight_pos hp0 r
  have hbs := dowlingBinomialWeight_pos hp0 s
  have hdiff : 0<((s : ℝ)-r)*(p-1)*dowlingBinomialWeight p r*dowlingBinomialWeight p s := by
    apply mul_pos
    · apply mul_pos
      · apply mul_pos
        · exact sub_pos.mpr (by exact_mod_cast hrs)
        · linarith
      · exact hbr
    · exact hbs
  have he : ((r : ℝ)+1)*((s : ℝ)+1)*
      (dowlingBinomialWeight p (r+1)*dowlingBinomialWeight p s-
        dowlingBinomialWeight p r*dowlingBinomialWeight p (s+1))=
      ((s : ℝ)-r)*(p-1)*dowlingBinomialWeight p r*dowlingBinomialWeight p s := by
    linear_combination ((s : ℝ)+1)*dowlingBinomialWeight p s*hr-
      ((r : ℝ)+1)*dowlingBinomialWeight p r*hs
  have hscale : 0<((r : ℝ)+1)*((s : ℝ)+1) := by positivity
  nlinarith

/-- Iterated inward balancing, including an exact equality endpoint. -/
theorem positive_sequence_balance {b : ℕ→ℝ}
    (hstep : ∀ r s, r<s → b r*b (s+1)<b (r+1)*b s)
    (r s u v : ℕ) (hru : r≤u) (huv : u≤v) (hvs : v≤s) (hsum : r+s=u+v) :
    b r*b s≤b u*b v := by
  induction d : u-r generalizing r s u v with
  | zero =>
    have hu : u=r := by omega
    have hv : v=s := by omega
    simp [hu,hv]
  | succ d ih =>
    have hrs : r<s-1 := by omega
    have hs : s-1+1=s := by omega
    have hfirst := hstep r (s-1) hrs
    rw [hs] at hfirst
    exact le_trans (le_of_lt hfirst)
      (ih (r+1) (s-1) u v (by omega) huv (by omega) (by omega) (by omega))

 theorem dowlingBinomialWeight_midpoint {p : ℝ} (hp : 1<p) (r s : ℕ) :
    dowlingBinomialWeight p r*dowlingBinomialWeight p s ≤
      dowlingBinomialWeight p ((r+s)/2)*dowlingBinomialWeight p ((r+s+1)/2) := by
  by_cases hrs : r≤s
  · apply positive_sequence_balance (dowlingBinomialWeight_strict_step hp) r s
    all_goals omega
  · rw [mul_comm (dowlingBinomialWeight p r)]
    apply positive_sequence_balance (dowlingBinomialWeight_strict_step hp) s r
    all_goals omega

 theorem dowlingBinomialWeight_midpoint_strict {p : ℝ} (hp : 1<p) (r s : ℕ)
    (hrs : r+1<s ∨ s+1<r) :
    dowlingBinomialWeight p r*dowlingBinomialWeight p s <
      dowlingBinomialWeight p ((r+s)/2)*dowlingBinomialWeight p ((r+s+1)/2) := by
  rcases hrs with hrs | hrs
  · have h := dowlingBinomialWeight_strict_step hp r (s-1) (by omega)
    rw [show s-1+1=s by omega] at h
    apply lt_of_lt_of_le h
    apply positive_sequence_balance (dowlingBinomialWeight_strict_step hp) (r+1) (s-1)
    all_goals omega
  · have h := dowlingBinomialWeight_strict_step hp s (r-1) (by omega)
    rw [show r-1+1=r by omega,mul_comm (dowlingBinomialWeight p s)] at h
    apply lt_of_lt_of_le h
    apply positive_sequence_balance (dowlingBinomialWeight_strict_step hp) (s+1) (r-1)
    all_goals omega

end Dowling
