import AperyMoments.Reciprocal
import AperyMoments.AlternatingBinomial
import Mathlib.Data.Nat.Choose.Central

noncomputable section
open scoped BigOperators
namespace AperyMoments

/-- The finite even-moment expression of the heterogeneous angular convolution. -/
def spectralMomentCoefficient (m : ℕ) (α : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m+1), ((2*m).choose (2*j) : ℝ) *
    (j.centralBinom : ℝ)^2 * α^(m-j) * ((m-j).centralBinom : ℝ)

theorem spectral_binomial_factor (n r k : ℕ) (hr : r ≤ n) (hk : k ≤ r) :
    (2*n-k).choose k * (2*(n-k)).choose (2*(n-r)) * (r-k).centralBinom =
      (2*n-r).choose r * r.choose k * (2*n-k).choose (r-k) := by
  have h1 := Nat.choose_mul (n := 2*n-k) (k := 2*r-k) (s := k) (by omega)
  have h2 := Nat.choose_mul (n := 2*r-k) (k := r) (s := k) hk
  have h3 := Nat.choose_mul (n := 2*n-k) (k := 2*r-k) (s := r-k) (by omega)
  have hs1 : (2*(n-k)).choose (2*(n-r)) = (2*(n-k)).choose (2*(r-k)) :=
    Nat.choose_symm_of_eq_add (by omega)
  have hs2 : (2*r-k).choose r = (2*r-k).choose (r-k) :=
    Nat.choose_symm_of_eq_add (by omega)
  have e1 : 2*n-k-k=2*(n-k) := by omega
  have e2 : 2*r-k-k=2*(r-k) := by omega
  have e3 : 2*n-k-(r-k)=2*n-r := by omega
  have e4 : 2*r-k-(r-k)=r := by omega
  rw [e1,e2] at h1
  rw [e2] at h2
  rw [e3,e4] at h3
  rw [hs1, Nat.centralBinom]
  calc
    _ = (2*n-k).choose (2*r-k) * ((2*r-k).choose k * (2*(r-k)).choose (r-k)) := by rw [← h1]; ring
    _ = (2*n-k).choose (2*r-k) * ((2*r-k).choose r * r.choose k) := by rw [← h2]
    _ = ((2*n-r).choose r * r.choose k) * (2*n-k).choose (r-k) := by rw [hs2]; nlinarith [h3]

theorem reciprocal_binomial_factor (n r : ℕ) (hr : r ≤ n) :
    n.choose r * (2*n-r).choose n = (2*n-r).choose r * (n-r).centralBinom := by
  have h := Nat.choose_mul (n := 2*n-r) (k := n) (s := r) hr
  have he : 2*n-r-r=2*(n-r) := by omega
  rw [he] at h
  simpa only [Nat.centralBinom, Nat.mul_comm] using h

theorem triangle_reflect_swap (n : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ k ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n-k+1), f k j) =
      ∑ r ∈ Finset.range (n+1), ∑ k ∈ Finset.range (r+1), f k (n-r) := by
  change (∑ k ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n-k+1), (fun a : Σ _ : ℕ, ℕ => f a.1 a.2) ⟨k,j⟩) =
    ∑ r ∈ Finset.range (n+1), ∑ k ∈ Finset.range (r+1), (fun a : Σ _ : ℕ, ℕ => f a.2 (n-a.1)) ⟨r,k⟩
  rw [← Finset.sum_sigma (Finset.range (n+1)) (fun k => Finset.range (n-k+1)) (fun a : Σ _ : ℕ, ℕ => f a.1 a.2),
    ← Finset.sum_sigma (Finset.range (n+1)) (fun r => Finset.range (r+1)) (fun a : Σ _ : ℕ, ℕ => f a.2 (n-a.1))]
  apply Finset.sum_bij (fun a _ => ⟨n-a.2,a.1⟩)
  · intro a ha
    simp only [Finset.mem_sigma, Finset.mem_range] at ha ⊢
    omega
  · intro a ha b hb he
    simp only [Finset.mem_sigma, Finset.mem_range] at ha hb
    have h1 := congrArg Sigma.fst he
    have h2 := congrArg Sigma.snd he
    apply Sigma.ext
    · exact h2
    · have : a.2=b.2 := by dsimp at h1; omega
      exact heq_of_eq this
  · intro b hb
    simp only [Finset.mem_sigma, Finset.mem_range] at hb
    refine ⟨⟨b.2,n-b.1⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range]
      omega
    · apply Sigma.ext
      · dsimp; omega
      · rfl
  · intro a ha
    simp only [Finset.mem_sigma, Finset.mem_range] at ha
    change f a.1 a.2 = f a.1 (n-(n-a.2))
    congr 1
    omega

theorem reciprocal_spectral_coefficients (n : ℕ) (α : ℝ) :
    (∑ k ∈ Finset.range (n+1), (-α)^k * ((2*n-k).choose k : ℝ) *
      spectralMomentCoefficient (n-k) α) = reciprocalPolynomial n α := by
  unfold spectralMomentCoefficient reciprocalPolynomial
  simp only [Finset.mul_sum]
  rw [triangle_reflect_swap]
  apply Finset.sum_congr rfl
  intro r hrange
  have hr : r ≤ n := by simpa using Finset.mem_range.mp hrange
  have hsum : (∑ k ∈ Finset.range (r+1),
      (-α)^k * ((2*n-k).choose k : ℝ) *
      (((2*(n-k)).choose (2*(n-r)) : ℝ) * ((n-r).centralBinom : ℝ)^2 *
        α^(n-k-(n-r)) * ((n-k-(n-r)).centralBinom : ℝ))) =
      ((n-r).centralBinom : ℝ)^2 * ((2*n-r).choose r : ℝ) * α^r *
        ∑ k ∈ Finset.range (r+1), (-1:ℝ)^k * r.choose k * (2*n-k).choose (r-k) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hkRange
    have hk : k ≤ r := by simpa using Finset.mem_range.mp hkRange
    have he : n-k-(n-r)=r-k := by omega
    have hp : α^k * α^(r-k)=α^r := by rw [← pow_add, Nat.add_sub_of_le hk]
    have hf := congrArg (fun a : ℕ => (a : ℝ)) (spectral_binomial_factor n r k hr hk)
    simp only [Nat.cast_mul] at hf
    rw [he,neg_pow]
    calc
      _ = (-1:ℝ)^k *
          (((2*n-k).choose k : ℝ) * (2*(n-k)).choose (2*(n-r)) * (r-k).centralBinom) *
          ((n-r).centralBinom : ℝ)^2 * (α^k * α^(r-k)) := by ring
      _ = _ := by rw [hf,hp]; ring
  rw [hsum, alternating_binomial_convolution (2*n) r (by omega)]
  have hf := congrArg (fun a : ℕ => (a : ℝ)) (reciprocal_binomial_factor n r hr)
  simp only [Nat.cast_mul] at hf
  rw [hf]
  ring

end AperyMoments
