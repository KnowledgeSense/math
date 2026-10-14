import HardCoreActivityThreshold.SubcriticalPartition

namespace HardCoreActivityThreshold

open Finset

theorem occupation_log_one_add (r : ℝ) (hr : 0<r) :
    scalarOccupation (Real.log (1+r))=r/(1+r) := by
  unfold scalarOccupation
  rw [Real.exp_neg,Real.exp_log (by linarith : (0 : ℝ)<1+r)]
  field_simp
  ring

theorem subcriticalPotential_log_one_add (Λ r : ℝ) (hΛ : 0<Λ) (hr : 0<r) :
    subcriticalPotential Λ (Real.log (1+r))=Real.log (Λ/r) := by
  unfold subcriticalPotential
  rw [Real.exp_log (by linarith : (0 : ℝ)<1+r)]
  rw [show 1+r-1=r by ring,Real.log_div hΛ.ne' hr.ne']

theorem activity_contraction (Λ : ℝ) (hΛ : 0<Λ) (hL : Λ<criticalActivity) :
    ∃γ : ℝ,0<γ ∧ γ<1 ∧ ∀n : ℕ,∀r y : Fin n → ℝ,
      (∀i,0<r i ∧ r i≤Λ) → (∀i,0≤y i ∧ y i≤Real.log (Λ/r i)) →
      (∑i,(r i/(1+r i))^2*potential (y i))≤
        γ*potential (∑i,Real.log (1+r i)) := by
  obtain ⟨γ,hγ,hγ1,hcon⟩ := subcritical_partition_contraction Λ hΛ hL
  refine ⟨γ,hγ,hγ1,?_⟩
  intro n r y hr hy
  let a : Fin n → ℝ := fun i => Real.log (1+r i)
  have ha : ∀i,0<a i ∧ a i≤subcriticalEndpoint Λ := by
    intro i
    constructor
    · exact Real.log_pos (by linarith [(hr i).1])
    · apply Real.strictMonoOn_log.monotoneOn
        (by change 0<1+r i; linarith [(hr i).1])
        (by change 0<1+Λ; linarith)
      linarith [(hr i).2]
  have hc := hcon n a ha
  have hs : (∑i,(r i/(1+r i))^2*potential (y i))≤∑i,subcriticalFunction Λ (a i) := by
    apply sum_le_sum
    intro i _
    dsimp [subcriticalFunction,a]
    rw [occupation_log_one_add _ (hr i).1,subcriticalPotential_log_one_add Λ _ hΛ (hr i).1]
    exact mul_le_mul_of_nonneg_left (potential_strictMono.monotone (hy i).2) (sq_nonneg _)
  exact hs.trans hc

end HardCoreActivityThreshold
