import EdgeColoringMixing.FiniteProbability
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.LineGraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option autoImplicit false

/-! Actual finite proper edge colorings, common-domain pinnings, and line-graph distance. -/
namespace EdgeColoringMixing

open Finset

universe u
variable {V : Type u} [Fintype V]

noncomputable instance edgeDecidableEq (G : SimpleGraph V) : DecidableEq G.edgeSet :=
  Classical.decEq _

noncomputable instance edgeFintype (G : SimpleGraph V) : Fintype G.edgeSet :=
  Fintype.ofFinite G.edgeSet

/-- A proper edge coloring assigns different colors to distinct incident edges. -/
def Proper (G : SimpleGraph V) (q : ℕ) (σ : G.edgeSet → Fin q) : Prop :=
  ∀ e f, G.lineGraph.Adj e f → σ e ≠ σ f

/-- The pinning is a function on precisely the specified common domain. -/
def Agrees {G : SimpleGraph V} {q : ℕ} (Λ : Finset G.edgeSet)
    (τ : Λ → Fin q) (σ : G.edgeSet → Fin q) : Prop :=
  ∀ f : Λ, σ f = τ f

/-- Every coloring counted here is an actual coloring of all the tree's edges. -/
noncomputable def completions (G : SimpleGraph V) (q : ℕ) (Λ : Finset G.edgeSet)
    (τ : Λ → Fin q) : Finset (G.edgeSet → Fin q) := by
  classical
  exact univ.filter (fun σ => Proper G q σ ∧ Agrees Λ τ σ)

/-- Feasibility means existence of an actual proper extension. -/
def Feasible (G : SimpleGraph V) (q : ℕ) (Λ : Finset G.edgeSet)
    (τ : Λ → Fin q) : Prop := ∃ σ, Proper G q σ ∧ Agrees Λ τ σ

@[simp] theorem mem_completions {G : SimpleGraph V} {q : ℕ} {Λ : Finset G.edgeSet}
    {τ : Λ → Fin q} {σ : G.edgeSet → Fin q} :
    σ ∈ completions G q Λ τ ↔ Proper G q σ ∧ Agrees Λ τ σ := by
  classical
  simp [completions]

theorem feasible_iff_completions_nonempty {G : SimpleGraph V} {q : ℕ}
    {Λ : Finset G.edgeSet} {τ : Λ → Fin q} :
    Feasible G q Λ τ ↔ (completions G q Λ τ).Nonempty := by
  simp only [Feasible, Finset.Nonempty, mem_completions]

/-- The uniform conditional law, as an explicit normalized counting measure. -/
noncomputable def pinnedLaw (G : SimpleGraph V) (q : ℕ) (Λ : Finset G.edgeSet)
    (τ : Λ → Fin q) (hτ : Feasible G q Λ τ) : FiniteLaw (G.edgeSet → Fin q) := by
  classical
  let S := completions G q Λ τ
  have hS : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.mpr (feasible_iff_completions_nonempty.mp hτ)
  refine ⟨fun σ => if σ ∈ S then 1 / (S.card : ℝ) else 0, ?_, ?_⟩
  · intro σ
    split_ifs
    · positivity
    · rfl
  · simp only [← Finset.sum_filter]
    have hf : univ.filter (fun σ => σ ∈ S) = S := by ext; simp
    rw [hf]
    simp only [Finset.sum_const, nsmul_eq_mul, one_div]
    exact mul_inv_cancel₀ hS.ne'

/-- The single-edge color marginal of the uniform conditional law. -/
noncomputable def marginal (G : SimpleGraph V) (q : ℕ) (Λ : Finset G.edgeSet)
    (τ : Λ → Fin q) (hτ : Feasible G q Λ τ) (e : G.edgeSet) (c : Fin q) : ℝ :=
  (pinnedLaw G q Λ τ hτ).eventMass (fun σ => σ e = c)

/-- Total variation on the finite common color palette. -/
noncomputable def totalVariation {q : ℕ} (p p' : Fin q → ℝ) : ℝ :=
  (∑ c, |p c - p' c|) / 2

theorem marginal_nonneg (G : SimpleGraph V) (q : ℕ) (Λ : Finset G.edgeSet)
    (τ : Λ → Fin q) (hτ : Feasible G q Λ τ) (e : G.edgeSet) (c : Fin q) :
    0 ≤ marginal G q Λ τ hτ e c :=
  (pinnedLaw G q Λ τ hτ).eventMass_nonneg _

theorem marginal_sum_one (G : SimpleGraph V) (q : ℕ) (Λ : Finset G.edgeSet)
    (τ : Λ → Fin q) (hτ : Feasible G q Λ τ) (e : G.edgeSet) :
    ∑ c, marginal G q Λ τ hτ e c = 1 := by
  classical
  unfold marginal FiniteLaw.eventMass
  rw [Finset.sum_comm]
  have hsum (σ : G.edgeSet → Fin q) :
      (∑ c : Fin q, if σ e = c then (pinnedLaw G q Λ τ hτ).mass σ else 0) =
      (pinnedLaw G q Λ τ hτ).mass σ := by
    rw [Finset.sum_ite_eq]
    simp
  calc
    _ = ∑ σ, (pinnedLaw G q Λ τ hτ).mass σ := by
      apply Finset.sum_congr rfl
      intro σ _
      convert hsum σ using 1
      apply Finset.sum_congr rfl
      intro c _
      by_cases h : σ e = c <;> simp [h]
    _ = 1 := (pinnedLaw G q Λ τ hτ).sum_one

theorem totalVariation_le_one {q : ℕ} (p p' : Fin q → ℝ)
    (hp : ∀ c, 0 ≤ p c) (hp' : ∀ c, 0 ≤ p' c)
    (hs : ∑ c, p c = 1) (hs' : ∑ c, p' c = 1) :
    totalVariation p p' ≤ 1 := by
  unfold totalVariation
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  calc
    ∑ c, |p c - p' c| ≤ ∑ c, (p c + p' c) := by
      apply Finset.sum_le_sum
      intro c _
      exact abs_le.mpr ⟨by linarith [hp c], by linarith [hp' c]⟩
    _ = 1 * 2 := by rw [Finset.sum_add_distrib, hs, hs']; norm_num

theorem marginal_totalVariation_le_one (G : SimpleGraph V) (q : ℕ)
    (Λ : Finset G.edgeSet) (τ τ' : Λ → Fin q)
    (hτ : Feasible G q Λ τ) (hτ' : Feasible G q Λ τ') (e : G.edgeSet) :
    totalVariation (marginal G q Λ τ hτ e) (marginal G q Λ τ' hτ' e) ≤ 1 :=
  totalVariation_le_one _ _ (marginal_nonneg G q Λ τ hτ e)
    (marginal_nonneg G q Λ τ' hτ' e) (marginal_sum_one G q Λ τ hτ e)
    (marginal_sum_one G q Λ τ' hτ' e)

/-- Distance in the actual line graph to the set where two common-domain pins differ.
The infimum over an empty disagreement set is infinity. -/
noncomputable def disagreementDistance (G : SimpleGraph V) {q : ℕ}
    (Λ : Finset G.edgeSet) (τ τ' : Λ → Fin q) (e : G.edgeSet) : ℕ∞ := by
  classical
  exact ⨅ f : Λ, if τ f ≠ τ' f then G.lineGraph.edist e f else ⊤

/-- The convention κ^∞ = 0, including the absence of disagreements. -/
noncomputable def distanceDecay (κ : ℝ) (ℓ : ℕ∞) : ℝ :=
  if ℓ = ⊤ then 0 else κ ^ ℓ.toNat

/-- The maximum degree bound is imposed on the original tree. -/
def DegreeBound (G : SimpleGraph V) (Δ : ℕ) : Prop :=
  ∀ v, Nat.card (G.neighborSet v) ≤ Δ

/-- Strong spatial mixing for every finite tree, with constants outside the tree quantifier. -/
def StrongSpatialMixing (Δ q : ℕ) (C κ : ℝ) : Prop :=
  ∀ (V : Type u) (_ : Fintype V) (G : SimpleGraph V), G.IsTree → DegreeBound G Δ →
    ∀ (Λ : Finset G.edgeSet) (τ τ' : Λ → Fin q)
      (hτ : Feasible G q Λ τ) (hτ' : Feasible G q Λ τ') (e : G.edgeSet),
      e ∉ Λ →
      totalVariation (marginal G q Λ τ hτ e) (marginal G q Λ τ' hτ' e) ≤
        C * distanceDecay κ (disagreementDistance G Λ τ τ' e)

/-- The precise scope of Theorem 1.2 in the pinned 12 October 2026 release.
This is a statement, not a proof or an assumed bridge. -/
def ReleaseMainTheorem : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ Δ₀ : ℕ, ∃ κ : ℝ, 0 < κ ∧ κ < 1 ∧
    ∀ Δ q : ℕ, Δ₀ ≤ Δ → ((3 + Real.sqrt 5) / 2 + ε) * Δ ≤ q →
      ∃ C : ℝ, 0 ≤ C ∧ StrongSpatialMixing.{u} Δ q C κ

omit [Fintype V] in
@[simp] theorem disagreementDistance_self (G : SimpleGraph V) {q : ℕ}
    (Λ : Finset G.edgeSet) (τ : Λ → Fin q) (e : G.edgeSet) :
    disagreementDistance G Λ τ τ e = ⊤ := by
  simp [disagreementDistance]

@[simp] theorem totalVariation_self {q : ℕ} (p : Fin q → ℝ) :
    totalVariation p p = 0 := by
  simp [totalVariation]

/-- Identical pinnings have exactly identical conditioned marginals. -/
theorem same_pinning_bound (G : SimpleGraph V) {q : ℕ}
    (Λ : Finset G.edgeSet) (τ : Λ → Fin q) (hτ : Feasible G q Λ τ)
    (e : G.edgeSet) (C κ : ℝ) :
    totalVariation (marginal G q Λ τ hτ e) (marginal G q Λ τ hτ e) ≤
      C * distanceDecay κ (disagreementDistance G Λ τ τ e) := by
  simp [distanceDecay]

end EdgeColoringMixing
