import Dowling.DowlingRetainedNontrivialStrict

noncomputable section
namespace Dowling
open Finset

theorem weightedMixtureCoefficient_linear (U V : ℕ→ℝ) (a b p : ℝ) (n k : ℕ) :
    weightedMixtureCoefficient (fun j=>a*U j+b*V j) p n k=
      a*weightedMixtureCoefficient U p n k+b*weightedMixtureCoefficient V p n k := by
  by_cases hk : k≤n
  · simp only [weightedMixtureCoefficient,ite_eq_left hk]
    simp only [add_mul,Finset.sum_add_distrib,← Finset.mul_sum,mul_assoc]
  · simp [weightedMixtureCoefficient,hk]

theorem weightedMixtureCoefficient_symm (W : ℕ→ℝ) (p : ℝ) (n k : ℕ) (hk : k≤n) :
    weightedMixtureCoefficient W p n (n-k)=weightedMixtureCoefficient W p n k := by
  simp only [weightedMixtureCoefficient,ite_eq_left hk,ite_eq_left (Nat.sub_le n k),
    Nat.sub_sub_self hk,min_comm (n-k) k]
  apply sum_congr rfl
  intro j hj
  ring

theorem retainedNontrivialWeight_linear (a θ : ℝ) (n j : ℕ) :
    retainedNontrivialWeight a θ n j=(1-θ)*dowlingBaseWeight a n j+θ*jointlessWeight a n j := by
  unfold retainedNontrivialWeight jointlessWeight
  ring

theorem retainedNontrivialScalar_linear (a θ : ℝ) (n k : ℕ) :
    retainedNontrivialScalar a θ n k=
      (1-θ)*weightedMixtureCoefficient (dowlingBaseWeight a n) (a+1) n k+
      θ*weightedMixtureCoefficient (jointlessWeight a n) (a+1) n k := by
  unfold retainedNontrivialScalar
  rw [show retainedNontrivialWeight a θ n = (fun j=>(1-θ)*dowlingBaseWeight a n j+θ*jointlessWeight a n j) from funext (retainedNontrivialWeight_linear a θ n)]
  exact weightedMixtureCoefficient_linear _ _ _ _ _ _ _

theorem retainedNontrivialScalar_symm (a θ : ℝ) (n k : ℕ) (hk : k≤n) :
    retainedNontrivialScalar a θ n (n-k)=retainedNontrivialScalar a θ n k :=
  weightedMixtureCoefficient_symm _ _ _ _ hk

theorem dowlingBaseWeight_row {a : ℝ} (ha : 0<a) (n k : ℕ) :
    weightedMixtureCoefficient (dowlingBaseWeight a n) (a+1) n k=
      dowlingScalarCoefficient a n k := by
  rw [dowlingScalarCoefficient_raised ha]
  by_cases hk : k≤n
  · simp only [weightedMixtureCoefficient,dowlingWeightedCoefficient,ite_eq_left hk,
      dowlingBaseWeight,Finset.mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  · simp [weightedMixtureCoefficient,dowlingWeightedCoefficient,hk]

theorem retainedNontrivialScalar_linear_full {a : ℝ} (ha : 0<a) (θ : ℝ) (n k : ℕ) :
    retainedNontrivialScalar a θ n k=(1-θ)*dowlingScalarCoefficient a n k+
      θ*weightedMixtureCoefficient (jointlessWeight a n) (a+1) n k := by
  rw [retainedNontrivialScalar_linear,dowlingBaseWeight_row ha]

end Dowling
