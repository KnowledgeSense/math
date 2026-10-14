import MainTheorems.ProductKernel
import MainTheorems.PrefixPoints

namespace ResearchMain.SIBO

open scoped BigOperators

variable {E : Type*} [DecidableEq E] {ι : Type*} [Fintype ι]
variable {G : ι → Type*} [∀ t, AddCommGroup (G t)]

def Feasible (ψ : ∀ t, E → G t) (F : ∀ t, Finset (G t)) (B : Finset E) : Prop :=
  ∀ t, (∑ e ∈ B, ψ t e) ∉ F t

/-- The proximity upper bound holds for all finite forbidden sets and arbitrary abelian labels. -/
theorem sibo_proximity (M : Matroid E) (hSI : IsSIBO M)
    (ψ : ∀ t, E → G t) (F : ∀ t, Finset (G t))
    (hfeasible : ∃ B : Finset E, M.IsBase (B : Set E) ∧ Feasible ψ F B)
    (A : Finset E) (hA : M.IsBase (A : Set E)) :
    ∃ B : Finset E, M.IsBase (B : Set E) ∧ Feasible ψ F B ∧
      (A \ B).card ≤ (∏ t, ((F t).card + 1)) - 1 := by
  classical
  have hex : ∃ n : ℕ, ∃ B : Finset E,
      M.IsBase (B : Set E) ∧ Feasible ψ F B ∧ (A \ B).card = n := by
    obtain ⟨B, hB, hF⟩ := hfeasible
    exact ⟨_, B, hB, hF, rfl⟩
  obtain ⟨B, hB, hF, hdist⟩ := Nat.find_spec hex
  have hmin (C : Finset E) (hC : M.IsBase (C : Set E)) (hFC : Feasible ψ F C) :
      (A \ B).card ≤ (A \ C).card := by
    rw [hdist]
    exact Nat.find_min' hex ⟨C, hC, hFC, rfl⟩
  obtain ⟨o, hv⟩ := hSI A B hA hB
  let label (t : ι) (C : Finset E) := ∑ e ∈ C, ψ t e
  let T (t : ι) := (F t).image (fun f => f - label t B)
  have hzero (t : ι) : 0 ∉ T t := by
    intro h
    obtain ⟨f, hf, heq⟩ := Finset.mem_image.mp h
    have heq' : f = label t B := sub_eq_zero.mp heq
    apply hF t
    change label t B ∈ F t
    rwa [heq'] at hf
  have hcard (t : ι) : (T t).card = (F t).card := by
    apply Finset.card_image_of_injective
    intro x y h
    exact sub_left_inj.mp h
  let s (j : Fin ((A \ B).card + 1)) (t : ι) :=
    ∑ i ∈ indexInterval o.n 0 (o.prefixBoundary j), (ψ t (o.a i) - ψ t (o.b i))
  have hupper (i j : Fin ((A \ B).card + 1)) (hij : i < j) :
      ∃ t, s j t - s i t ∈ T t := by
    have hp : o.prefixBoundary i ≤ o.prefixBoundary j :=
      (o.prefixBoundary_strictMono hij).le
    let C := o.exchange (o.prefixBoundary i) (o.prefixBoundary j)
    have hC : M.IsBase (C : Set E) := hv _ _ hp (o.prefixBoundary_le j)
    obtain ⟨a, ha, haB⟩ := o.interval_contains_distinct hij
    have hcloser : (A \ C).card < (A \ B).card := o.exchange_closer M hB hv _ _ a ha haB
    have hinfeasible : ∃ t, label t C ∈ F t := by
      by_contra! h
      exact (Nat.not_lt_of_ge (hmin C hC h)) hcloser
    obtain ⟨t, ht⟩ := hinfeasible
    refine ⟨t, Finset.mem_image.mpr ⟨label t C, ht, ?_⟩⟩
    have heq := o.exchange_label M hB hv (ψ t) (o.prefixBoundary i) (o.prefixBoundary j)
    rw [interval_sum _ hp] at heq
    change label t C = label t B + (s j t - s i t) at heq
    rw [heq]
    abel
  have hbound := multi_forbidden_interval_bound T hzero s hupper
  simp only [hcard] at hbound
  exact ⟨B, hB, hF, hbound⟩

/-- In the singleton case the sharp universal upper bound is `2^k - 1`. -/
theorem singleton_sibo_proximity (M : Matroid E) (hSI : IsSIBO M)
    (ψ : ∀ t, E → G t) (f : ∀ t, G t)
    (hfeasible : ∃ B : Finset E, M.IsBase (B : Set E) ∧
      ∀ t, (∑ e ∈ B, ψ t e) ≠ f t)
    (A : Finset E) (hA : M.IsBase (A : Set E)) :
    ∃ B : Finset E, M.IsBase (B : Set E) ∧
      (∀ t, (∑ e ∈ B, ψ t e) ≠ f t) ∧ (A \ B).card ≤ 2 ^ Fintype.card ι - 1 := by
  classical
  have h := sibo_proximity M hSI ψ (fun t => {f t})
    (by simpa [Feasible] using hfeasible) A hA
  simpa [Feasible] using h

end ResearchMain.SIBO
