import Dowling.ActualApexWeightsSingleKernel

noncomputable section
namespace Dowling
open PowerSeries
open scoped Classical

theorem apexSingleRaised_row (n k : ℕ) :
    quadraticWeightedRow (apexSingleRaised n) 2 n k=
      (1/(n : ℝ))*quadraticWeightedRow (apexSingleUnraised n) 1 n k := by
  rw [quadraticWeightedRow_raise (a := 1) (by norm_num)]
  norm_num only [show (1 : ℝ)+1=2 by norm_num]
  change _=(1/(n : ℝ))*quadraticWeightedRow (fun j =>
    1*(apexSingleUnraised n j/(n+1-2*j)-
      if j=0 then 0 else apexSingleUnraised n (j-1)/(n+1-2*(j-1)))) 2 n k
  rw [← quadraticWeightedRow_scalar]
  apply congrArg (fun v => quadraticWeightedRow v 2 n k)
  funext j
  simp [apexSingleRaised]

theorem apex_single_coeff (n k : ℕ) (hn : 2≤n) :
    (((1+Polynomial.X)*fullY Unit (n-1)).coeff k : ℝ)=
      (n.factorial : ℝ)*quadraticWeightedRow (apexSingleRaised n) 2 n k := by
  have hp : (((1+Polynomial.X)*fullY Unit (n-1)).map (Int.castRingHom ℝ))=
      Polynomial.C ((n-1).factorial : ℝ)*coeff n (quadraticWeightedKernel (apexSingleUnraised n) 1) := by
    rw [Polynomial.map_mul,fullY_unit_kernel,apexSingleUnraised_coeff n (by omega)]
    have hs : (((n-1 : ℕ) : ℝ)+1)/2=(n : ℝ)/2 := by rw [Nat.cast_sub (by omega),Nat.cast_one]; ring
    rw [hs]
    simp only [Polynomial.map_add,Polynomial.map_one,Polynomial.map_X]
    ring
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff k) hp
  rw [Polynomial.coeff_map,Polynomial.coeff_C_mul,quadraticWeightedKernel_coeff] at hc
  change (((1+Polynomial.X)*fullY Unit (n-1)).coeff k : ℝ)=_ at hc
  rw [hc,apexSingleRaised_row]
  have hf : (n.factorial : ℝ)=(n : ℝ)*((n-1).factorial : ℝ) := by
    exact_mod_cast (Nat.mul_factorial_pred (by omega : n≠0)).symm
  have hn0 : (n : ℝ)≠0 := by exact_mod_cast (show n≠0 by omega)
  rw [hf]
  field_simp

theorem apexRaisedWeight_one (n j : ℕ) (hn : 2≤n) (hj : 2*j≤n) :
    apexRaisedWeight n 1 j=apexSingleRaised n j := by
  apply quadraticWeightedRow_weights_unique (a := 2) (by norm_num) _ _ n _ j hj
  intro k
  let i : Fin n := ⟨0,by omega⟩
  have h := apex_actual_coeff_raised (G := Unit) hn ({i} : Set (Fin n)) ⟨i,Set.mem_singleton i⟩ k
  rw [configurationY_single_joint,apex_single_coeff n k hn] at h
  simp only [Set.toFinset_singleton,Finset.card_singleton] at h
  exact (mul_left_cancel₀ (by positivity : (n.factorial : ℝ)≠0) h).symm

end Dowling
