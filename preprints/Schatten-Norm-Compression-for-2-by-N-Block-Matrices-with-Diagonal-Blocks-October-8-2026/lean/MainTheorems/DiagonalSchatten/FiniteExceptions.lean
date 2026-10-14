import Mathlib.Analysis.Convex.Deriv
import Mathlib.Tactic

namespace ResearchMain.DiagonalSchatten

theorem monotoneOn_of_deriv_nonneg_off_finset (s : Finset ℝ) {f : ℝ → ℝ} {l r : ℝ}
    (hf : ContinuousOn f (Set.Icc l r))
    (hd : ∀ x ∈ Set.Ioo l r, x ∉ s → DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ Set.Ioo l r, x ∉ s → 0 ≤ deriv f x) :
    MonotoneOn f (Set.Icc l r) := by
  classical
  induction s using Finset.induction_on generalizing l r with
  | empty =>
      apply monotoneOn_of_deriv_nonneg (convex_Icc l r) hf
      · intro x hx
        rw [interior_Icc] at hx
        exact (hd x hx (by simp)).differentiableWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact hp x hx (by simp)
  | @insert c s _ ih =>
      have hrestrict (u v : ℝ) (hlu : l ≤ u) (hvr : v ≤ r)
          (hc : ∀ x ∈ Set.Ioo u v, x ≠ c) : MonotoneOn f (Set.Icc u v) := by
        apply ih (l := u) (r := v) (hf.mono (fun x hx => ⟨hlu.trans hx.1, hx.2.trans hvr⟩))
        · intro x hx hxs
          apply hd x ⟨hlu.trans_lt hx.1, hx.2.trans_le hvr⟩
          simpa only [Finset.mem_insert, not_or] using ⟨hc x hx, hxs⟩
        · intro x hx hxs
          apply hp x ⟨hlu.trans_lt hx.1, hx.2.trans_le hvr⟩
          simpa only [Finset.mem_insert, not_or] using ⟨hc x hx, hxs⟩
      by_cases hcl : c ≤ l
      · exact hrestrict l r le_rfl le_rfl fun x hx => ne_of_gt (hcl.trans_lt hx.1)
      by_cases hrc : r ≤ c
      · exact hrestrict l r le_rfl le_rfl fun x hx => ne_of_lt (hx.2.trans_le hrc)
      have hlc : l < c := lt_of_not_ge hcl
      have hcr : c < r := lt_of_not_ge hrc
      have hleft := hrestrict l c le_rfl hcr.le fun x hx => ne_of_lt hx.2
      have hright := hrestrict c r hlc.le le_rfl fun x hx => ne_of_gt hx.1
      intro x hx y hy hxy
      by_cases hyc : y ≤ c
      · exact hleft ⟨hx.1, hxy.trans hyc⟩ ⟨hy.1, hyc⟩ hxy
      by_cases hcx : c ≤ x
      · exact hright ⟨hcx, hx.2⟩ ⟨hcx.trans hxy, hy.2⟩ hxy
      have hxc : x < c := lt_of_not_ge hcx
      have hcy : c < y := lt_of_not_ge hyc
      exact (hleft ⟨hx.1, hxc.le⟩ ⟨hlc.le, le_rfl⟩ hxc.le).trans
        (hright ⟨le_rfl, hcr.le⟩ ⟨hcy.le, hy.2⟩ hcy.le)

theorem antitoneOn_of_deriv_nonpos_off_finset (s : Finset ℝ) {f : ℝ → ℝ} {l r : ℝ}
    (hf : ContinuousOn f (Set.Icc l r))
    (hd : ∀ x ∈ Set.Ioo l r, x ∉ s → DifferentiableAt ℝ f x)
    (hp : ∀ x ∈ Set.Ioo l r, x ∉ s → deriv f x ≤ 0) :
    AntitoneOn f (Set.Icc l r) := by
  have hmono : MonotoneOn (-f) (Set.Icc l r) :=
    monotoneOn_of_deriv_nonneg_off_finset s hf.neg
      (fun x hx hs => (hd x hx hs).neg)
      (fun x hx hs => by rw [deriv.neg]; exact neg_nonneg.mpr (hp x hx hs))
  intro x hx y hy hxy
  have h := hmono hx hy hxy
  simpa only [Pi.neg_apply, neg_le_neg_iff] using h

theorem convexOn_of_second_deriv_nonneg_off_finset (s : Finset ℝ) {f : ℝ → ℝ} {l r : ℝ}
    (hf : ContinuousOn f (Set.Icc l r))
    (hd : ∀ x ∈ Set.Icc l r, DifferentiableAt ℝ f x)
    (hc : ContinuousOn (deriv f) (Set.Icc l r))
    (hd2 : ∀ x ∈ Set.Ioo l r, x ∉ s → DifferentiableAt ℝ (deriv f) x)
    (hp : ∀ x ∈ Set.Ioo l r, x ∉ s → 0 ≤ deriv (deriv f) x) :
    ConvexOn ℝ (Set.Icc l r) f := by
  apply MonotoneOn.convexOn_of_deriv (convex_Icc l r) hf
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableWithinAt
  · exact (monotoneOn_of_deriv_nonneg_off_finset s hc hd2 hp).mono interior_subset

theorem concaveOn_of_second_deriv_nonpos_off_finset (s : Finset ℝ) {f : ℝ → ℝ} {l r : ℝ}
    (hf : ContinuousOn f (Set.Icc l r))
    (hd : ∀ x ∈ Set.Icc l r, DifferentiableAt ℝ f x)
    (hc : ContinuousOn (deriv f) (Set.Icc l r))
    (hd2 : ∀ x ∈ Set.Ioo l r, x ∉ s → DifferentiableAt ℝ (deriv f) x)
    (hp : ∀ x ∈ Set.Ioo l r, x ∉ s → deriv (deriv f) x ≤ 0) :
    ConcaveOn ℝ (Set.Icc l r) f := by
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc l r) hf
  · intro x hx
    exact (hd x (interior_subset hx)).differentiableWithinAt
  · exact (antitoneOn_of_deriv_nonpos_off_finset s hc hd2 hp).mono interior_subset

end ResearchMain.DiagonalSchatten
