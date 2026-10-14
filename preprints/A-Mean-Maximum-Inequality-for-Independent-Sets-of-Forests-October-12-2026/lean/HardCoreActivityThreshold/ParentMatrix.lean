import HardCoreActivityThreshold.TriangularFactorization

namespace HardCoreActivityThreshold
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem matrix_product_nonzero (A B : Matrix V V ℝ) (u v : V)
    (h : (A*B) u v≠0) : ∃w,A u w≠0 ∧ B w v≠0 := by
  by_contra! hn
  apply h
  rw [mul_apply]
  apply sum_eq_zero
  intro w _
  by_cases hw : A u w=0
  · rw [hw,zero_mul]
  · rw [hn w hw,mul_zero]

theorem parent_power_rank (B : Matrix V V ℝ) (rank : V → ℕ)
    (hB : ∀u v,B u v≠0 → rank v<rank u) :
    ∀k : ℕ,∀u v,(B^k) u v≠0 → rank v+k≤rank u := by
  intro k
  induction k with
  | zero =>
    intro u v huv
    have he : u=v := by
      by_contra hn
      exact huv (by simp [pow_zero,hn])
    subst v
    simp
  | succ k ih =>
    intro u v huv
    rw [pow_succ'] at huv
    obtain ⟨w,hw,hv⟩ := matrix_product_nonzero B (B^k) u v huv
    have h1 := hB u w hw
    have h2 := ih w v hv
    omega

theorem parent_matrix_nilpotent (B : Matrix V V ℝ) (rank : V → ℕ) (N : ℕ)
    (hB : ∀u v,B u v≠0 → rank v<rank u) (hN : ∀u,rank u<N) : B^N=0 := by
  ext u v
  by_contra! hn
  have hne : (B^N) u v≠0 := by simpa using hn
  have h := parent_power_rank B rank hB N u v hne
  have hu := hN u
  omega

theorem parent_power_unique (B : Matrix V V ℝ)
    (hB : ∀u v w,B u v≠0 → B u w≠0 → v=w) :
    ∀k : ℕ,∀u v w,(B^k) u v≠0 → (B^k) u w≠0 → v=w := by
  intro k
  induction k with
  | zero =>
    intro u v w hv hw
    have huv : u=v := by
      by_contra hn
      exact hv (by simp [pow_zero,hn])
    have huw : u=w := by
      by_contra hn
      exact hw (by simp [pow_zero,hn])
    exact huv.symm.trans huw
  | succ k ih =>
    intro u v w hv hw
    rw [pow_succ'] at hv hw
    obtain ⟨a,ha,hav⟩ := matrix_product_nonzero B (B^k) u v hv
    obtain ⟨b,hb,hbw⟩ := matrix_product_nonzero B (B^k) u w hw
    have hab := hB u a b ha hb
    subst b
    exact ih a v w hav hbw

theorem parent_power_sparse (B : Matrix V V ℝ)
    (hB : ∀u v w,B u v≠0 → B u w≠0 → v=w) (k : ℕ) :
    ∀u v w,v≠w → (B^k) u v*(B^k) u w=0 := by
  intro u v w hvw
  by_cases hv : (B^k) u v=0
  · rw [hv,zero_mul]
  · have hw : (B^k) u w=0 := by
      by_contra hn
      exact hvw (parent_power_unique B hB k u v w hv hn)
    rw [hw,mul_zero]

end HardCoreActivityThreshold
