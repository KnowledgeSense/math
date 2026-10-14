import PenneyDensity.Convergence
import PenneyDensity.PositiveBoundaryMass

noncomputable section
namespace PenneyDensity
open Filter
open scoped Topology

 theorem boundary_probability_le_limit {ρ : ℝ} (hρ : Tendsto density atTop (𝓝 ρ)) (K : ℕ) :
    boundaryProbability K≤ρ+4*(1/2 : ℝ)^K := by
  have hp : Tendsto (fun k : ℕ => (1/2 : ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto (fun n : ℕ => collisionCoefficient K*(1/2 : ℝ)^(n-2*K)) atTop (𝓝 0) := by
    simpa using (hp.comp (tendsto_sub_atTop_nat (2*K))).const_mul (collisionCoefficient K)
  have hh : boundaryProbability K-4*(1/2 : ℝ)^K≤ρ := by
    apply ge_of_tendsto (show Tendsto (fun n => density n+collisionCoefficient K*(1/2 : ℝ)^(n-2*K))
      atTop (𝓝 ρ) by simpa using hρ.add ht)
    filter_upwards [eventually_gt_atTop (2*K)] with n hn
    have ha := (abs_le.mp (density_local_approximation hn)).1
    linarith
  linarith

 theorem density_limit_cylinder_lower_bound {ρ : ℝ} (hρ : Tendsto density atTop (𝓝 ρ))
    (L : ℕ) (hL : 0<L) : (1/2 : ℝ)^(4*L)*(1-8*(1/2 : ℝ)^(2*L))≤ρ := by
  have hp : Tendsto (fun k : ℕ => (1/2 : ℝ)^k) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto (fun K => ρ+4*(1/2 : ℝ)^K) atTop (𝓝 ρ) := by
    simpa using (hp.const_mul 4).const_add ρ
  apply ge_of_tendsto ht
  filter_upwards [eventually_ge_atTop L] with K hK
  exact (boundary_probability_lower_bound hL hK).trans (boundary_probability_le_limit hρ K)

 def positiveLowerBound : ℝ := (1/2 : ℝ)^32*(1-10*(1/2 : ℝ)^16)

 theorem positiveLowerBound_pos : 0<positiveLowerBound := by norm_num [positiveLowerBound]

 theorem density_limit_positive {ρ : ℝ} (hρ : Tendsto density atTop (𝓝 ρ)) :
    positiveLowerBound≤ρ ∧ 0<ρ := by
  have hs := density_limit_cylinder_lower_bound hρ 8 (by omega)
  have hb : positiveLowerBound≤(1/2 : ℝ)^(4*8)*(1-8*(1/2 : ℝ)^(2*8)) := by
    norm_num [positiveLowerBound]
  have hle := hb.trans hs
  exact ⟨hle,lt_of_lt_of_le positiveLowerBound_pos hle⟩

 theorem density_has_positive_limit : ∃ ρ : ℝ,Tendsto density atTop (𝓝 ρ) ∧
    positiveLowerBound≤ρ ∧ 0<ρ := by
  obtain ⟨ρ,hρ⟩ := density_has_limit
  exact ⟨ρ,hρ,density_limit_positive hρ⟩

end PenneyDensity
