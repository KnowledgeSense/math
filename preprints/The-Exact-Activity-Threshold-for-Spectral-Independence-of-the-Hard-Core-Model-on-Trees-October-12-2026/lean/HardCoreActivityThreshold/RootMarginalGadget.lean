import HardCoreActivityThreshold.RootOddsApproximation
import Mathlib.Topology.Order.IntermediateValue

/-! The finite-tree root-marginal gadget is proved, rather than imported as an assumption. -/
namespace HardCoreActivityThreshold
open Forest
attribute [local instance] Classical.propDecidable

theorem occupation_fixedpoint_exists {a : ℝ} (ha : 0 < a) (d : ℕ) (hd : 0 < d) :
    ∃ p ∈ Set.Ioo (0 : ℝ) 1, p = a * (1-p)^d := by
  let f : ℝ → ℝ := fun p => p - a*(1-p)^d
  have hc : Continuous f := by fun_prop
  have h0 : f 0 < 0 := by dsimp [f]; simpa using neg_lt_zero.mpr ha
  have h1 : 0 < f 1 := by simp [f, Nat.ne_of_gt hd]
  obtain ⟨p, hp, hfp⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hc.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f 0) (f 1) from ⟨h0.le, h1.le⟩)
  refine ⟨p, ⟨?_, ?_⟩, ?_⟩
  · by_contra! h
    have hp0 : p = 0 := le_antisymm h hp.1
    rw [hp0] at hfp
    linarith
  · by_contra! h
    have hp1 : p = 1 := le_antisymm hp.2 h
    rw [hp1] at hfp
    linarith
  · dsimp [f] at hfp
    linarith

theorem occupation_fixedpoint_unique {a p q : ℝ} (ha : 0 < a) (d : ℕ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hpf : p = a*(1-p)^d) (hqf : q = a*(1-q)^d) : p = q := by
  suffices h : ∀ x y : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → y ∈ Set.Ioo (0 : ℝ) 1 →
      x = a*(1-x)^d → y = a*(1-y)^d → x ≤ y by
    exact le_antisymm (h p q hp hq hpf hqf) (h q p hq hp hqf hpf)
  intro x y hx hy hxf hyf
  by_contra! hxy
  have hpw := pow_le_pow_left₀ (by linarith [hx.2] : 0 ≤ 1-x) (by linarith : 1-x ≤ 1-y) d
  have hm := mul_le_mul_of_nonneg_left hpw ha.le
  linarith

theorem occupation_fixedpoint_existsUnique {a : ℝ} (ha : 0 < a) (d : ℕ) (hd : 0 < d) :
    ∃! p : ℝ, p ∈ Set.Ioo (0 : ℝ) 1 ∧ p = a*(1-p)^d := by
  obtain ⟨p, hp, hf⟩ := occupation_fixedpoint_exists ha d hd
  refine ⟨p, ⟨hp, hf⟩, ?_⟩
  intro q hq
  exact occupation_fixedpoint_unique ha d hq.1 hp hq.2 hf

theorem occupation_fixedpoint_to_odds {a p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (d : ℕ) (hd : 0 < d) (hpf : p = a*(1-p)^d) :
    a = (p/(1-p)) * (1+p/(1-p))^(d-1) := by
  have hn : 1-p ≠ 0 := by linarith [hp.2]
  have he : 1 + p/(1-p) = 1/(1-p) := by field_simp; ring
  rw [he, one_div, inv_pow]
  have hdp : (1-p)^d = (1-p)^(d-1)*(1-p) := by
    conv_lhs => rw [show d = (d-1)+1 by omega]
    rw [pow_succ]
  rw [hdp] at hpf
  field_simp
  nlinarith

theorem odds_to_probability_lipschitz {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) :
    |r/(1+r) - s/(1+s)| ≤ |r-s| := by
  have h1r : 0 < 1+r := by positivity
  have h1s : 0 < 1+s := by positivity
  have he : r/(1+r) - s/(1+s) = (r-s)/((1+r)*(1+s)) := by field_simp; ring
  rw [he, abs_div, abs_of_pos (mul_pos h1r h1s)]
  apply (div_le_iff₀ (mul_pos h1r h1s)).mpr
  have hd : 1 ≤ (1+r)*(1+s) := by nlinarith [mul_nonneg hr hs]
  nlinarith [abs_nonneg (r-s)]

/-- For every positive accuracy there is an actual finite constant-activity tree
whose unpinned root marginal approximates the prescribed recursion fixed point. -/
theorem finite_tree_root_marginal_gadget {a p : ℝ} (ha : 0 < a)
    (d : ℕ) (hd : 0 < d) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (hpf : p = a*(1-p)^d)
    {epsilon : ℝ} (he : 0 < epsilon) :
    ∃ A : ForestExpr, (ForestExpr.root A).graph.IsTree ∧
      |marginal (hardCoreLaw (ForestExpr.root A).graph (fun _ => a) (fun _ => ha)) none - p| < epsilon := by
  let w := p/(1-p)
  have hw : 0 < w := div_pos hp.1 (sub_pos.mpr hp.2)
  have hfix : a = w*(1+w)^(d-1) := occupation_fixedpoint_to_odds hp d hd hpf
  obtain ⟨A, hA⟩ := exists_rootOdds_approximation ha hw (d-1) hfix he
  refine ⟨A, A.root_graph_isTree, ?_⟩
  rw [root_marginal_from_odds A ha]
  have hpw : p = w/(1+w) := by
    dsimp [w]
    have hn : 1-p ≠ 0 := by linarith [hp.2]
    field_simp
    ring
  conv_lhs => rhs; rw [hpw]
  exact (odds_to_probability_lipschitz (rootOdds_pos A ha).le hw.le).trans_lt hA

end HardCoreActivityThreshold
