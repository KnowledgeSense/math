import PenneyDensity.PositiveLimit

noncomputable section
namespace PenneyDensity
open Filter
open scoped Topology
attribute [local instance] Classical.propDecidable

 def diagonalDecomposition (n : ℕ) :
    {p : WordOfLength n × WordOfLength n // PropertyR (toWord p.1) (toWord p.2)} ≃
    {p : WordOfLength n × WordOfLength n // p.1≠p.2 ∧ PropertyR (toWord p.1) (toWord p.2)} ⊕
      WordOfLength n where
  toFun p := if he : p.val.1=p.val.2 then Sum.inr p.val.1 else Sum.inl ⟨p.val,he,p.property⟩
  invFun p := match p with
    | Sum.inl p => ⟨p.val,p.property.2⟩
    | Sum.inr v => ⟨(v,v),diagonal_propertyR (toWord v)⟩
  left_inv p := by
    by_cases he : p.val.1=p.val.2
    · simp only [dite_eq_left he]
      apply Subtype.ext
      exact Prod.ext rfl he
    · simp only [dite_eq_right he]
  right_inv p := by
    cases p with
    | inl p => simp only [dite_eq_right p.property.1]
    | inr v => simp

 theorem diagonal_density_identity (n : ℕ) :
    distinctDensity n=density n-(1/2 : ℝ)^n := by
  have hc := Nat.card_congr (diagonalDecomposition n)
  rw [Nat.card_sum] at hc
  have hw : Nat.card (WordOfLength n)=2^n := by
    simp only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_bool,Fintype.card_fin]
  rw [hw] at hc
  unfold distinctDensity density
  rw [hc,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,add_div]
  have hp : (2 : ℝ)^n/4^n=(1/2 : ℝ)^n := by
    rw [← div_pow]
    congr 1
    norm_num
  rw [hp]
  ring

 def distinctNormalizedDensity (n : ℕ) : ℝ :=
  (Nat.card {p : WordOfLength n × WordOfLength n //
    p.1≠p.2 ∧ PropertyR (toWord p.1) (toWord p.2)} : ℝ)/(4^n-2^n)

 theorem distinct_denominator_pos {n : ℕ} (hn : 0<n) : 0<(4 : ℝ)^n-2^n := by
  have hh : (2 : ℝ)^n<4^n := pow_lt_pow_left₀ (by norm_num) (by norm_num) (by omega)
  linarith

 theorem distinct_normalized_identity {n : ℕ} (hn : 0<n) :
    distinctNormalizedDensity n=(density n-(1/2 : ℝ)^n)/(1-(1/2 : ℝ)^n) := by
  rw [← diagonal_density_identity]
  unfold distinctNormalizedDensity distinctDensity
  have h4 : (4 : ℝ)^n≠0 := pow_ne_zero _ (by norm_num)
  have hd : (4 : ℝ)^n-2^n≠0 := ne_of_gt (distinct_denominator_pos hn)
  have hp : (1/2 : ℝ)^n=2^n/4^n := by rw [← div_pow]; congr 1; norm_num
  rw [hp]
  field_simp

 theorem distinct_density_tendsto {ρ : ℝ} (hρ : Tendsto density atTop (𝓝 ρ)) :
    Tendsto distinctDensity atTop (𝓝 ρ) := by
  have hp : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have he : distinctDensity=(fun n => density n-(1/2 : ℝ)^n) := funext diagonal_density_identity
  rw [he]
  simpa using hρ.sub hp

 theorem distinct_normalized_tendsto {ρ : ℝ} (hρ : Tendsto density atTop (𝓝 ρ)) :
    Tendsto distinctNormalizedDensity atTop (𝓝 ρ) := by
  have hp : Tendsto (fun n : ℕ => (1/2 : ℝ)^n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht : Tendsto (fun n => (density n-(1/2 : ℝ)^n)/(1-(1/2 : ℝ)^n)) atTop (𝓝 ρ) := by
    simpa only [sub_zero,div_one,Pi.div_apply] using! (hρ.sub hp).div (tendsto_const_nhds.sub hp) (by norm_num : (1 : ℝ)-0≠0)
  apply ht.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (distinct_normalized_identity hn).symm

end PenneyDensity
