import EdgeColoringMixing.RootMessageDecay
import EdgeColoringMixing.ObservedCounting
import EdgeColoringMixing.ObservedPlacement
import EdgeColoringMixing.SideBudgets
import EdgeColoringMixing.Parameters
import EdgeColoringMixing.InterpolationContraction

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! Assembly of actual common-domain finite-tree strong spatial mixing. -/
namespace EdgeColoringMixing
open Finset RootedCounting ActualColorings PinningForbidden ObservedCounting
universe u

/-- The exact rooted-message endpoint estimate implies SSM for the original
uniform edge-coloring law, with its original common domain and line-graph distance. -/
theorem strongSpatialMixing_of_rootMessageDecay {Δ q : ℕ} {κ E : ℝ}
    (hs : 0 < (q : ℝ) - 2 * Δ + 2) (hκ : 0 < κ) (hκ1 : κ < 1)
    (hdecay : RootMessageDecay.{u} Δ q κ E) :
    StrongSpatialMixing.{u} Δ q (mixingPrefactor q ((q : ℝ) - 2 * Δ + 2) E κ) κ := by
  classical
  intro V _ G hG hΔ Λ τ τ' hτ hτ' e he
  let ef : FreeEdge G Λ := ⟨e, he⟩
  let T := observedTree G Λ ef
  let F := fun σ : Λ → Fin q => fun v : observedComponent G Λ ef =>
    forbidden G q Λ σ v.1
  have hT : T.IsTree := observedTree_isTree G Λ hG.isAcyclic ef
  have hfull (σ : Λ → Fin q) (hσ : Feasible G q Λ σ) : Nonempty (Coloring T q (F σ)) :=
    observedTree_coloring_nonempty G q Λ σ hσ ef
  have hbudget (σ : Λ → Fin q) : VertexBudget Δ q T (F σ) :=
    fun v => observed_vertex_budget G q Λ σ hΔ ef v
  obtain ⟨⟨x, y⟩, hxyval⟩ := Sym2.mk_surjective (observedEdge G Λ ef).1
  change s(x,y) = (observedEdge G Λ ef).1 at hxyval
  have hxy : T.Adj x y := by
    apply T.mem_edgeSet.mp
    rw [hxyval]
    exact (observedEdge G Λ ef).2
  have heobs : (⟨s(x,y), hxy⟩ : T.edgeSet) = observedEdge G Λ ef := Subtype.ext hxyval
  let A := fun (r : observedComponent G Λ ef) (σ : Λ → Fin q) =>
    rootAvailability (G := sideGraph (G := T) x y r) (sideRoot x y r) q (fun v => F σ v.1)
  have hsidefull (r : observedComponent G Λ ef) (σ : Λ → Fin q) (hσ : Feasible G q Λ σ) :
      Nonempty (Coloring (sideGraph (G := T) x y r) q (fun v => F σ v.1)) :=
    side_coloring_nonempty (hfull σ hσ) x y r
  have hsidebudget (r : observedComponent G Λ ef) (σ : Λ → Fin q) :
      VertexBudget Δ q (sideGraph (G := T) x y r) (fun v => F σ v.1) :=
    side_vertexBudget (hbudget σ) x y r
  have hsideroot (r z : observedComponent G Λ ef) (σ : Λ → Fin q)
      (hrz : s(r,z) = s(x,y)) (hAdj : T.Adj r z) :
      RootBudget Δ q (sideGraph (G := T) x y r) (sideRoot x y r) (fun v => F σ v.1) :=
    side_rootBudget (hbudget σ) x y r z hrz hAdj
  have hdomain (r z : observedComponent G Λ ef) (σ : Λ → Fin q)
      (hσ : Feasible G q Λ σ) (hrz : s(r,z) = s(x,y)) (hAdj : T.Adj r z) :
      MessageDomain Δ q (A r σ) :=
    rootAvailability_mem_domain (sideGraph_isTree hT x y r) (sideRoot x y r) q Δ _
      (hsidefull r σ hσ) (hsideroot r z σ hrz hAdj)
  have hmarginal (σ : Λ → Fin q) (hσ : Feasible G q Λ σ) :
      marginal G q Λ σ hσ e = observedMarginal (A x σ) (A y σ) := by
    funext c
    have hc := coloring_marginal_eq_observedMarginal hT hxy q (F σ) (hfull σ hσ) c
    rw [heobs] at hc
    exact (marginal_eq_observedTree_ratio G q Λ σ hσ ef c).trans hc
  apply buffer_distanceDecay_bound hs hκ hκ1
    (marginal_totalVariation_le_one G q Λ τ τ' hτ hτ' e)
  · intro htop
    have hequal (r : observedComponent G Λ ef) (hr : r ∈ s(x,y)) : A r τ = A r τ' := by
      apply rootAvailability_eq_of_distance_top G Λ τ τ' e
        (sideGraph (G := T) x y r) (sideGraph_isTree hT x y r) (sideRoot x y r)
        (observedSidePlacement G Λ ef x y r hxy heobs hr) _ _
      · intro v hv
        exact forbidden_eq_of_incident_agreement G q Λ τ τ' v.1.1 hv
      · exact hsidefull r τ hτ
      · exact hsidefull r τ' hτ'
      · exact htop
    rw [hmarginal τ hτ, hmarginal τ' hτ', hequal x (by simp), hequal y (by simp)]
    exact totalVariation_self _
  · intro n hn hn3
    have hcut : ((n - 1 : ℕ) : ℕ∞) < disagreementDistance G Λ τ τ' e := by
      rw [hn]
      exact_mod_cast (by omega : n - 1 < n)
    have hsidebound (r z : observedComponent G Λ ef) (hr : r ∈ s(x,y))
        (hrz : s(r,z) = s(x,y)) (hAdj : T.Adj r z) :
        (∑ c, |A r τ c - A r τ' c|) ≤ Real.sqrt q / 2 * (κ^(n - 1 - 2) * E) := by
      apply hdecay (side (G := T) x y r) inferInstance (sideGraph (G := T) x y r)
        (sideGraph_isTree hT x y r) (sideRoot x y r) _ _
        (hsidefull r τ hτ) (hsidefull r τ' hτ')
        (hsidebudget r τ) (hsidebudget r τ')
        (hsideroot r z τ hrz hAdj) (hsideroot r z τ' hrz hAdj)
        (n - 1) (by omega)
      exact observedSide_agreeToDepth G Λ τ τ' ef x y r hxy heobs hr (n - 1) hcut
    have hx := hsidebound x y (by simp) rfl hxy
    have hy := hsidebound y x (by simp) Sym2.eq_swap hxy.symm
    rw [hmarginal τ hτ, hmarginal τ' hτ']
    calc
      _ ≤ ((∑ c, |A x τ c - A x τ' c|) + (∑ c, |A y τ c - A y τ' c|)) /
          ((q : ℝ) - 2 * Δ + 2) :=
        observed_marginal_tv_bound (hdomain x y τ hτ rfl hxy)
          (hdomain y x τ hτ Sym2.eq_swap hxy.symm)
          (hdomain x y τ' hτ' rfl hxy) (hdomain y x τ' hτ' Sym2.eq_swap hxy.symm) hs
      _ ≤ (Real.sqrt q / 2 * (κ^(n - 1 - 2) * E) +
          Real.sqrt q / 2 * (κ^(n - 1 - 2) * E)) / ((q : ℝ) - 2 * Δ + 2) :=
        div_le_div_of_nonneg_right (add_le_add hx hy) hs.le
      _ = Real.sqrt q * E / ((q : ℝ) - 2 * Δ + 2) * κ^(n - 3) := by
        have hnsub : n - 1 - 2 = n - 3 := by omega
        rw [hnsub]
        ring

/-- The original 12 October 2026 strong spatial mixing theorem for uniform
proper edge colorings on all finite trees. The contraction rate depends only
on ε, and the prefactor depends only on ε, Δ and q. -/
theorem release_main_theorem : ReleaseMainTheorem.{u} := by
  intro ε hε
  obtain ⟨N, hN⟩ := release_parameter_choice hε
  obtain ⟨hκ, hκ1⟩ := contractionRate_bounds hε
  refine ⟨N, contractionRate ε, hκ, hκ1, ?_⟩
  intro Δ q hΔ hq
  obtain ⟨hdegree, hs, _hsratio, hfirst, hsecond, hthird, _hδ, _hδmargin, hgain⟩ :=
    hN Δ q hΔ hq
  have P : ContractionBudget Δ q (contractionRate ε) := by
    refine ⟨by omega, hs, hκ.le, hfirst, hsecond, ?_, ?_⟩
    · simpa only [columnError] using hthird
    · simpa only [releaseColumnMultiplier, columnError] using hgain
  refine ⟨mixingPrefactor q ((q : ℝ) - 2 * Δ + 2)
      (bufferEnergyConstant Δ q ((q : ℝ) - 2 * Δ + 2)) (contractionRate ε),
    mixingPrefactor_nonneg _ _ _ _, ?_⟩
  exact strongSpatialMixing_of_rootMessageDecay hs hκ hκ1 (rootMessageDecay_of_budget P)

end EdgeColoringMixing
