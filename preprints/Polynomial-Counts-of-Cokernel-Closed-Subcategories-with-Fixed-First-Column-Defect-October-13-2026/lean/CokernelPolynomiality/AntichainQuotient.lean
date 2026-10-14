import CokernelPolynomiality.AntichainSuffixSums
import Mathlib.LinearAlgebra.Pi

noncomputable section
namespace CokernelPolynomiality

def antichainQuotient {m : ℕ} (b : ℕ) (c d : Fin (m+1) → ℕ) (i : ℕ) :
    (∀ j, intervalSpace (c j) (d j) i) →ₗ[ℂ]
      (∀ j, intervalSpace (antichainOutputStart b c j) (d j) i) :=
  LinearMap.pi (fun j =>
    (intervalComponent (c j) (d j) (antichainOutputStart b c j) (d j) i).comp
      (LinearMap.proj j : (∀ t, intervalSpace (c t) (d t) i) →ₗ[ℂ] _)-
    if h : j.val < m then
      (intervalComponent (c ⟨j.val+1,by omega⟩) (d ⟨j.val+1,by omega⟩)
        (antichainOutputStart b c j) (d j) i).comp
        (LinearMap.proj ⟨j.val+1,by omega⟩ : (∀ t, intervalSpace (c t) (d t) i) →ₗ[ℂ] _)
    else 0)

@[simp] theorem antichainQuotient_castSucc {m : ℕ} (b : ℕ) (c d : Fin (m+1) → ℕ)
    (i : ℕ) (y : ∀ j, intervalSpace (c j) (d j) i) (k : Fin m) :
    (antichainQuotient b c d i y k.castSucc).val=
      if intervalActive (c k.succ) (d k.castSucc) i then (y k.castSucc).val-(y k.succ).val else 0 := by
  simp only [antichainQuotient,LinearMap.pi_apply,Fin.val_castSucc,k.isLt,dite_true,
    LinearMap.sub_apply,LinearMap.comp_apply,LinearMap.proj_apply,Submodule.coe_sub,
    intervalComponent_val,antichainOutputStart_castSucc]
  change (if intervalActive (c k.succ) (d k.castSucc) i then (y k.castSucc).val else 0)-
    (if intervalActive (c k.succ) (d k.castSucc) i then (y k.succ).val else 0)=_
  split <;> simp_all

@[simp] theorem antichainQuotient_last {m : ℕ} (b : ℕ) (c d : Fin (m+1) → ℕ)
    (i : ℕ) (y : ∀ j, intervalSpace (c j) (d j) i) :
    (antichainQuotient b c d i y (Fin.last m)).val=
      if intervalActive (b+1) (d (Fin.last m)) i then (y (Fin.last m)).val else 0 := by
  simp [antichainQuotient,intervalComponent_val]

def antichainLift {m : ℕ} (b : ℕ) (c d : Fin (m+1) → ℕ) (i : ℕ)
    (hc : Monotone c) (hd : Antitone d) (hcb : ∀ j, c j ≤ b)
    (z : ∀ j, intervalSpace (antichainOutputStart b c j) (d j) i)
    (j : Fin (m+1)) : intervalSpace (c j) (d j) i := by
  refine ⟨finSuffixSum (fun k => (z k).val) j,?_⟩
  by_cases hj : intervalActive (c j) (d j) i
  · simp [intervalSpace,hj]
  · have hz : finSuffixSum (fun k => (z k).val) j=0 := by
      apply Finset.sum_eq_zero
      intro k _
      by_cases hjk : j ≤ k
      · rw [ite_eq_left hjk]
        apply intervalSpace_val_zero
        intro hki
        apply hj
        exact ⟨(antichainOutputStart_ge b c hc hcb j k hjk).trans hki.1,
          hki.2.trans (hd hjk)⟩
      · rw [ite_eq_right hjk]
    simp [intervalSpace,hj,hz]

@[simp] theorem antichainLift_val {m : ℕ} (b : ℕ) (c d : Fin (m+1) → ℕ) (i : ℕ)
    (hc : Monotone c) (hd : Antitone d) (hcb : ∀ j, c j ≤ b)
    (z : ∀ j, intervalSpace (antichainOutputStart b c j) (d j) i) (j : Fin (m+1)) :
    (antichainLift b c d i hc hd hcb z j).val=finSuffixSum (fun k => (z k).val) j := rfl

theorem antichainQuotient_surjective {m : ℕ} (b : ℕ) (c d : Fin (m+1) → ℕ) (i : ℕ)
    (hc : Monotone c) (hd : Antitone d) (hcb : ∀ j, c j ≤ b) :
    Function.Surjective (antichainQuotient b c d i) := by
  intro z
  refine ⟨antichainLift b c d i hc hd hcb z,?_⟩
  funext j
  apply Subtype.ext
  induction j using Fin.lastCases with
  | last =>
    rw [antichainQuotient_last,antichainLift_val,finSuffixSum_last]
    by_cases h : intervalActive (b+1) (d (Fin.last m)) i
    · rw [ite_eq_left h]
    · rw [ite_eq_right h]
      exact (intervalSpace_val_zero (by simpa using h) (z (Fin.last m))).symm
  | cast j =>
    rw [antichainQuotient_castSucc,antichainLift_val,antichainLift_val,finSuffixSum_castSucc]
    by_cases h : intervalActive (c j.succ) (d j.castSucc) i
    · rw [ite_eq_left h]
      ring
    · rw [ite_eq_right h]
      exact (intervalSpace_val_zero (by simpa using h) (z j.castSucc)).symm

end CokernelPolynomiality
