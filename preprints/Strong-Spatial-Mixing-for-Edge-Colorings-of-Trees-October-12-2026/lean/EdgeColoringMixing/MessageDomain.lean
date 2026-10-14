import EdgeColoringMixing.MarginalLower

set_option autoImplicit false

/-! The exact availability recursion and its invariant domain from Section 3. -/
namespace EdgeColoringMixing
open Finset WeightedInjection

/-- The convex availability domain, with the original degree parameter. -/
structure MessageDomain (Δ q : ℕ) (A : Fin q → ℝ) : Prop where
  nonneg : ∀ c, 0 ≤ A c
  le_one : ∀ c, A c ≤ 1
  mass : (q : ℝ) - Δ + 1 ≤ ∑ c, A c

namespace MessageDomain
variable {Δ q : ℕ} {A B : Fin q → ℝ}

theorem convex_combination (hA : MessageDomain Δ q A) (hB : MessageDomain Δ q B)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθ' : θ ≤ 1) :
    MessageDomain Δ q (fun c => (1 - θ) * A c + θ * B c) := by
  refine ⟨fun c => add_nonneg (mul_nonneg (by linarith) (hA.nonneg c))
    (mul_nonneg hθ (hB.nonneg c)), ?_, ?_⟩
  · intro c
    nlinarith [hA.le_one c, hB.le_one c]
  · simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
    nlinarith [hA.mass, hB.mass]

end MessageDomain

/-- Child availability is zeroed on the colors pinned at the parent vertex. -/
noncomputable def maskedWeights {d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) (i : Fin d) (c : Fin q) : ℝ :=
  if c ∈ F then 0 else A i c

/-- The actual weighted-injection availability map, expressed by partition ratios. -/
noncomputable def availabilityStep {d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) (c : Fin q) : ℝ :=
  if c ∈ F then 0 else
    partition (withoutColor (maskedWeights F A) c) / partition (maskedWeights F A)

theorem maskedWeights_rowSurplus {Δ d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) (hA : ∀ i, MessageDomain Δ q (A i))
    (hdegree : F.card + d + 1 ≤ Δ) (hs : 0 < (q : ℝ) - 2 * Δ + 2) :
    RowSurplus (maskedWeights F A) ((q : ℝ) - 2 * Δ + 2) := by
  classical
  refine ⟨hs, ?_, ?_, ?_⟩
  · intro i c
    unfold maskedWeights
    split_ifs
    · rfl
    · exact (hA i).nonneg c
  · intro i c
    unfold maskedWeights
    split_ifs
    · norm_num
    · exact (hA i).le_one c
  · intro i
    have hremoved : (∑ c ∈ F, A i c) ≤ (F.card : ℝ) := by
      calc
        _ ≤ ∑ _c ∈ F, (1 : ℝ) := sum_le_sum (fun c _ => (hA i).le_one c)
        _ = _ := by simp
    have hsum : (∑ c, maskedWeights F A i c) = (∑ c, A i c) - ∑ c ∈ F, A i c := by
      have hp : (∑ c : Fin q, if c ∈ F then A i c else 0) = ∑ c ∈ F, A i c := by
        simp
      calc
        _ = ∑ c, (A i c - if c ∈ F then A i c else 0) := by
          apply sum_congr rfl
          intro c _
          by_cases hc : c ∈ F <;> simp [maskedWeights, hc]
        _ = _ := by rw [sum_sub_distrib, hp]
    have hd : (F.card : ℝ) + d + 1 ≤ Δ := by exact_mod_cast hdegree
    rw [hsum]
    linarith [(hA i).mass]

namespace WeightedInjection

theorem mean_eq_zero_of_weight_zero {d q : ℕ} (W : Fin d → Fin q → ℝ)
    (hn : ∀ i c, 0 ≤ W i c) (hZ : 0 < partition W) (i : Fin d) (c : Fin q)
    (hc : W i c = 0) : mean (law W hn hZ) i c = 0 := by
  classical
  unfold mean FiniteLaw.expectation
  apply Finset.sum_eq_zero
  intro σ _
  by_cases hi : σ i = c
  · have hw : weight W σ = 0 := by
      apply Finset.prod_eq_zero (mem_univ i)
      simpa [hi] using hc
    simp [law, hw]
  · simp [cell, hi]

theorem colorMean_eq_zero_of_column_zero {d q : ℕ} (W : Fin d → Fin q → ℝ)
    (hn : ∀ i c, 0 ≤ W i c) (hZ : 0 < partition W) (c : Fin q)
    (hc : ∀ i, W i c = 0) : colorMean (law W hn hZ) c = 0 := by
  unfold colorMean
  exact Finset.sum_eq_zero (fun i _ => mean_eq_zero_of_weight_zero W hn hZ i c (hc i))

theorem colorMean_total {d q : ℕ} (μ : FiniteLaw (Injection d q)) :
    ∑ c, colorMean μ c = d := by
  unfold colorMean
  rw [Finset.sum_comm]
  simp

end WeightedInjection

theorem availabilityStep_eq {d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) {s : ℝ} (hW : RowSurplus (maskedWeights F A) s)
    (c : Fin q) :
    availabilityStep F A c =
      (if c ∈ F then 0 else 1) - colorMean (law _ hW.nonneg (partition_pos _ hW)) c := by
  classical
  by_cases hc : c ∈ F
  · have hzero := colorMean_eq_zero_of_column_zero _ hW.nonneg (partition_pos _ hW) c
      (fun i => by simp [maskedWeights, hc])
    simp [availabilityStep, hc, hzero]
  · simp only [availabilityStep, hc, ite_false]
    exact color_unused_probability _ hW.nonneg (partition_pos _ hW) c

theorem availabilityStep_mass {d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) {s : ℝ} (hW : RowSurplus (maskedWeights F A) s) :
    (∑ c, availabilityStep F A c) = (q : ℝ) - F.card - d := by
  classical
  simp_rw [availabilityStep_eq F A hW]
  rw [Finset.sum_sub_distrib, colorMean_total]
  have hp : (∑ c : Fin q, if c ∈ F then (1 : ℝ) else 0) = (F.card : ℝ) := by
    simp
  have hpoint (c : Fin q) : (if c ∈ F then (0 : ℝ) else 1) =
      1 - if c ∈ F then 1 else 0 := by
    by_cases hc : c ∈ F <;> simp [hc]
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib, hp]
  simp

theorem availabilityStep_bounds {d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) {s : ℝ} (hW : RowSurplus (maskedWeights F A) s)
    (c : Fin q) (hc : c ∉ F) :
    s / ((d : ℝ) + s) ≤ availabilityStep F A c ∧ availabilityStep F A c ≤ 1 := by
  rw [availabilityStep_eq F A hW c, ite_eq_right hc]
  constructor
  · have h := colorMean_le _ hW c
    have hds : 0 < (d : ℝ) + s := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hW.positive
    have heq : 1 - (d : ℝ) / (d + s) = s / (d + s) := by
      field_simp
      ring
    linarith
  · linarith [colorMean_nonneg (law _ hW.nonneg (partition_pos _ hW)) c]

theorem availabilityStep_mem_domain {Δ d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) (hA : ∀ i, MessageDomain Δ q (A i))
    (hdegree : F.card + d + 1 ≤ Δ) (hs : 0 < (q : ℝ) - 2 * Δ + 2) :
    MessageDomain Δ q (availabilityStep F A) := by
  classical
  let hW := maskedWeights_rowSurplus F A hA hdegree hs
  refine ⟨?_, ?_, ?_⟩
  · intro c
    by_cases hc : c ∈ F
    · simp [availabilityStep, hc]
    · exact (div_nonneg hs.le (by positivity)).trans (availabilityStep_bounds F A hW c hc).1
  · intro c
    by_cases hc : c ∈ F
    · simp [availabilityStep, hc]
    · exact (availabilityStep_bounds F A hW c hc).2
  · rw [availabilityStep_mass F A hW]
    have hd : (F.card : ℝ) + d + 1 ≤ Δ := by exact_mod_cast hdegree
    linarith

/-- Every unpinned output coordinate is bounded away from zero after one exact level. -/
theorem availabilityStep_uniform_lower {Δ d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) {s : ℝ} (hW : RowSurplus (maskedWeights F A) s)
    (hd : d ≤ Δ) (c : Fin q) (hc : c ∉ F) :
    s / ((Δ : ℝ) + s) ≤ availabilityStep F A c := by
  have hds : 0 < (d : ℝ) + s := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hW.positive
  have hden : (d : ℝ) + s ≤ Δ + s := by
    have h : (d : ℝ) ≤ Δ := by exact_mod_cast hd
    linarith
  exact (div_le_div_of_nonneg_left hW.positive.le hds hden).trans
    (availabilityStep_bounds F A hW c hc).1

/-- A color with no available child cell has availability exactly one. -/
theorem availabilityStep_eq_one {d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) {s : ℝ} (hW : RowSurplus (maskedWeights F A) s)
    (c : Fin q) (hc : c ∉ F) (hzero : ∀ i, A i c = 0) :
    availabilityStep F A c = 1 := by
  rw [availabilityStep_eq F A hW c]
  have hz := colorMean_eq_zero_of_column_zero _ hW.nonneg (partition_pos _ hW) c
    (fun i => by simp [maskedWeights, hc, hzero i])
  simp [hc, hz]

/-- The quantitative upper half of the two-level buffer, with the release's b₀. -/
theorem availabilityStep_uniform_upper {Δ d q : ℕ} (F : Finset (Fin q))
    (A : Fin d → Fin q → ℝ) {s : ℝ} (hW : RowSurplus (maskedWeights F A) s)
    (hd : d ≤ Δ) (c : Fin q) (hc : c ∉ F) (i : Fin d)
    (hi : s / ((Δ : ℝ) + s) ≤ A i c) :
    availabilityStep F A c ≤ 1 - s * (s + 1) / ((q : ℝ) * ((Δ : ℝ) + s)^2) := by
  have hq : 0 < (q : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt c.isLt
  have hds : 0 < (d : ℝ) + s := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hW.positive
  have hΔs : 0 < (Δ : ℝ) + s := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) hW.positive
  have hden : (d : ℝ) + s ≤ Δ + s := by
    have h : (d : ℝ) ≤ Δ := by exact_mod_cast hd
    linarith
  have ht : 0 < s + 1 := by linarith [hW.positive]
  let μ := law _ hW.nonneg (partition_pos _ hW)
  have hmean : s * (s + 1) / ((q : ℝ) * ((Δ : ℝ) + s)^2) ≤ mean μ i c := by
    calc
      _ = (s / ((Δ : ℝ) + s) * (s + 1)) / ((q : ℝ) * ((Δ : ℝ) + s)) := by
        field_simp
      _ ≤ (s / ((Δ : ℝ) + s) * (s + 1)) / ((q : ℝ) * ((d : ℝ) + s)) :=
        div_le_div_of_nonneg_left (mul_nonneg (div_nonneg hW.positive.le hΔs.le) ht.le)
          (mul_pos hq hds) (mul_le_mul_of_nonneg_left hden hq.le)
      _ ≤ (A i c * (s + 1)) / ((q : ℝ) * ((d : ℝ) + s)) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hi ht.le) (mul_pos hq hds).le
      _ = (maskedWeights F A i c * (s + 1)) / ((q : ℝ) * ((d : ℝ) + s)) := by
        simp [maskedWeights, hc]
      _ ≤ _ := marginal_ge _ hW i c
  have hcol : mean μ i c ≤ colorMean μ c :=
    Finset.single_le_sum (fun j _ => mean_nonneg μ j c) (mem_univ i)
  rw [availabilityStep_eq F A hW c, ite_eq_right hc]
  change 1 - colorMean μ c ≤ _
  linarith

/-- Lemma 6.1: the support is fixed, and all varying coordinates lie in a compact
subinterval of (0,1), after two exact recursion levels. -/
theorem availabilityStep_buffer {Δ d q : ℕ} (F : Finset (Fin q))
    (Fchild : Fin d → Finset (Fin q)) (A : Fin d → Fin q → ℝ) {s : ℝ}
    (hW : RowSurplus (maskedWeights F A) s) (hd : d ≤ Δ)
    (hz : ∀ i c, c ∈ Fchild i → A i c = 0)
    (hl : ∀ i c, c ∉ Fchild i → s / ((Δ : ℝ) + s) ≤ A i c) (c : Fin q) :
    (c ∈ F → availabilityStep F A c = 0) ∧
    (c ∉ F → (∀ i, c ∈ Fchild i) → availabilityStep F A c = 1) ∧
    (c ∉ F → (∃ i, c ∉ Fchild i) →
      s / ((Δ : ℝ) + s) ≤ availabilityStep F A c ∧
      availabilityStep F A c ≤ 1 - s * (s + 1) / ((q : ℝ) * ((Δ : ℝ) + s)^2)) := by
  classical
  refine ⟨fun hc => by simp [availabilityStep, hc], ?_, ?_⟩
  · intro hc hall
    exact availabilityStep_eq_one F A hW c hc (fun i => hz i c (hall i))
  · intro hc hex
    obtain ⟨i, hi⟩ := hex
    exact ⟨availabilityStep_uniform_lower F A hW hd c hc,
      availabilityStep_uniform_upper F A hW hd c hc i (hl i c hi)⟩

end EdgeColoringMixing
