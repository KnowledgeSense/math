import HardCoreActivityThreshold.ParentMatrix

namespace HardCoreActivityThreshold
open Finset Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem sparse_product_column_square (A B : Matrix V V ℝ)
    (hrow : ∀u v w,v≠w → A u v*A u w=0) (w : V) :
    (∑u,((A*B) u w)^2)=∑v,(∑u,(A u v)^2)*(B v w)^2 := by
  calc
    _=∑u,∑v,(A u v)^2*(B v w)^2 := by
      apply sum_congr rfl
      intro u _
      exact sparse_square_sum (A u) (fun v => B v w) (hrow u)
    _=∑v,(∑u,(A u v)^2)*(B v w)^2 := by rw [sum_comm]; simp_rw [sum_mul]

 theorem weighted_column_decay (B : Matrix V V ℝ) (w : V → ℝ) (A γ : ℝ)
    (hA : 0≤A) (hγ : 0≤γ)
    (hrow : ∀u v z,B u v≠0 → B u z≠0 → v=z)
    (hfirst : ∀v,(∑u,(B u v)^2)≤A*w v)
    (hlocal : ∀v,(∑u,(B u v)^2*w u)≤γ*w v) :
    ∀k : ℕ,∀v,(∑u,((B^(k+1)) u v)^2)≤A*γ^k*w v := by
  intro k
  induction k with
  | zero => intro v; simpa using hfirst v
  | succ k ih =>
    intro v
    rw [pow_succ]
    rw [sparse_product_column_square (B^(k+1)) B (parent_power_sparse B hrow (k+1))]
    calc
      _≤∑u,(A*γ^k*w u)*(B u v)^2 :=
        sum_le_sum (fun u _ => mul_le_mul_of_nonneg_right (ih u) (sq_nonneg _))
      _=(A*γ^k)*(∑u,(B u v)^2*w u) := by
        rw [mul_sum]
        apply sum_congr rfl
        intro u _
        ring
      _≤(A*γ^k)*(γ*w v) :=
        mul_le_mul_of_nonneg_left (hlocal v) (mul_nonneg hA (pow_nonneg hγ _))
      _=A*γ^(k+1)*w v := by rw [pow_succ]; ring

 theorem weighted_column_uniform (B : Matrix V V ℝ) (w : V → ℝ) (A W γ : ℝ)
    (hA : 0≤A) (hγ : 0≤γ) (hw : ∀v,w v≤W)
    (hrow : ∀u v z,B u v≠0 → B u z≠0 → v=z)
    (hfirst : ∀v,(∑u,(B u v)^2)≤A*w v)
    (hlocal : ∀v,(∑u,(B u v)^2*w u)≤γ*w v) :
    ∀h : ℕ,0<h → ∀v,(∑u,((B^h) u v)^2)≤(A*W)*γ^(h-1) := by
  intro h hh v
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hh)
  change (∑u,((B^(k+1)) u v)^2)≤(A*W)*γ^k
  have hdec := weighted_column_decay B w A γ hA hγ hrow hfirst hlocal k v
  have hm := mul_le_mul_of_nonneg_left (hw v) (mul_nonneg hA (pow_nonneg hγ k))
  nlinarith

end HardCoreActivityThreshold
