import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace EdgeColoringMixing

noncomputable def surplusThreshold : ℝ := (Real.sqrt 5-1)/2
noncomputable def surplusRatio (ε : ℝ) : ℝ := surplusThreshold+ε
noncomputable def limitingGain (ε : ℝ) : ℝ := 1/(surplusRatio ε*(1+surplusRatio ε))
noncomputable def contractionRate (ε : ℝ) : ℝ := Real.sqrt ((1+limitingGain ε)/2)
noncomputable def perturbationMargin (ε : ℝ) : ℝ := Real.sqrt ((1+limitingGain ε)/(2*limitingGain ε))-1

theorem surplusThreshold_pos : 0<surplusThreshold := by
  have h := Real.sq_sqrt (show (0 : ℝ)≤5 by norm_num)
  have h0 := Real.sqrt_nonneg (5 : ℝ)
  unfold surplusThreshold
  nlinarith

theorem surplusThreshold_identity : surplusThreshold*(1+surplusThreshold)=1 := by
  have h := Real.sq_sqrt (show (0 : ℝ)≤5 by norm_num)
  unfold surplusThreshold
  nlinarith

theorem surplusRatio_pos {ε : ℝ} (hε : 0<ε) : 0<surplusRatio ε := by
  unfold surplusRatio
  linarith [surplusThreshold_pos]

theorem limitingGain_bounds {ε : ℝ} (hε : 0<ε) : 0<limitingGain ε ∧ limitingGain ε<1 := by
  have hc := surplusRatio_pos hε
  have hd : 1<surplusRatio ε*(1+surplusRatio ε) := by
    have ht := surplusThreshold_identity
    have h0 := surplusThreshold_pos
    unfold surplusRatio
    nlinarith [sq_nonneg ε]
  unfold limitingGain
  constructor
  · positivity
  · exact (div_lt_one (by positivity)).mpr hd

theorem contractionRate_bounds {ε : ℝ} (hε : 0<ε) : 0<contractionRate ε ∧ contractionRate ε<1 := by
  obtain ⟨hf0,hf1⟩ := limitingGain_bounds hε
  unfold contractionRate
  constructor
  · exact Real.sqrt_pos.2 (by linarith)
  · exact (Real.sqrt_lt' zero_lt_one).2 (by nlinarith)

theorem perturbationMargin_pos {ε : ℝ} (hε : 0<ε) : 0<perturbationMargin ε := by
  obtain ⟨hf0,hf1⟩ := limitingGain_bounds hε
  have hx : 1<(1+limitingGain ε)/(2*limitingGain ε) := (lt_div_iff₀ (by positivity)).2 (by linarith)
  unfold perturbationMargin
  have h := (Real.lt_sqrt (show (0 : ℝ)≤1 by norm_num)).2 (by simpa using hx)
  linarith

theorem perturbation_contraction_identity {ε : ℝ} (hε : 0<ε) :
    (1+perturbationMargin ε)^2*limitingGain ε=(contractionRate ε)^2 := by
  obtain ⟨hf0,hf1⟩ := limitingGain_bounds hε
  have hp : 0≤(1+limitingGain ε)/(2*limitingGain ε) := by positivity
  unfold perturbationMargin contractionRate
  rw [show 1+(Real.sqrt ((1+limitingGain ε)/(2*limitingGain ε))-1)=
      Real.sqrt ((1+limitingGain ε)/(2*limitingGain ε)) by ring,
      Real.sq_sqrt hp,Real.sq_sqrt (by positivity)]
  field_simp [ne_of_gt hf0]

noncomputable def harmonicHeight (D : ℕ) : ℝ := 1+(harmonic (D-2) : ℝ)

theorem harmonicHeight_le (D : ℕ) : harmonicHeight D≤2+Real.log D := by
  have hm : (harmonic (D-2) : ℝ)≤harmonic D := by
    unfold harmonic
    push_cast
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le D 2))
    intro i _ _
    positivity
  have hl := harmonic_le_one_add_log D
  unfold harmonicHeight
  linarith

theorem harmonicHeight_nonneg (D : ℕ) : 0≤harmonicHeight D := by
  unfold harmonicHeight harmonic
  push_cast
  positivity

open Filter in
theorem harmonicHeight_div_rpow_tendsto {r : ℝ} (hr : 0<r) :
    Tendsto (fun D : ℕ => harmonicHeight D/(D : ℝ)^r) atTop (nhds 0) := by
  have hlog := (isLittleO_log_rpow_atTop hr).tendsto_div_nhds_zero
  have hinv := (tendsto_rpow_atTop hr).inv_tendsto_atTop
  have hupper : Tendsto (fun D : ℕ => (2+Real.log (D : ℝ))/(D : ℝ)^r) atTop (nhds 0) := by
    have h := ((hinv.const_mul 2).add hlog).comp tendsto_natCast_atTop_atTop
    simpa [add_div,div_eq_mul_inv,add_mul,Function.comp_def] using h
  apply squeeze_zero (fun D => div_nonneg (harmonicHeight_nonneg D) (Real.rpow_nonneg (Nat.cast_nonneg D) r))
    (fun D => div_le_div_of_nonneg_right (harmonicHeight_le D) (Real.rpow_nonneg (Nat.cast_nonneg D) r)) hupper

open Filter in
theorem harmonicHeight_div_tendsto :
    Tendsto (fun D : ℕ => harmonicHeight D/(D : ℝ)) atTop (nhds 0) := by
  simpa using harmonicHeight_div_rpow_tendsto (r := 1) zero_lt_one

open Filter in
theorem harmonicHeight_sq_div_tendsto :
    Tendsto (fun D : ℕ => (harmonicHeight D)^2/(D : ℝ)) atTop (nhds 0) := by
  have h : Tendsto (fun D : ℕ => harmonicHeight D/Real.sqrt (D : ℝ)) atTop (nhds 0) := by
    simpa [Real.sqrt_eq_rpow] using harmonicHeight_div_rpow_tendsto (r := 1/2) (by norm_num)
  have hp := h.pow 2
  simpa [div_pow,Real.sq_sqrt (Nat.cast_nonneg _)] using hp


open Filter in
theorem eventual_parameter_budget (c L ζ : ℝ) (hc : 0<c) (hL : 0<L) (hζ : 0<ζ) :
    ∃ N : ℕ, ∀ D : ℕ, N≤D → 3≤D ∧
      8*harmonicHeight D≤c*(D : ℝ) ∧
      4*L*(D : ℝ)*(harmonicHeight D)^2≤(c*(D : ℝ))^2 ∧
      (L/c^2* (harmonicHeight D/(D : ℝ))+1/(c*(D : ℝ)))≤
        min (1/5) (ζ/(1+1/c)) := by
  have hm : 0<min (1/5 : ℝ) (ζ/(1+1/c)) := by positivity
  have h1 := harmonicHeight_div_tendsto.eventually
    (eventually_lt_nhds (show (0 : ℝ)<c/8 by positivity))
  have h2 := harmonicHeight_sq_div_tendsto.eventually
    (eventually_lt_nhds (show (0 : ℝ)<c^2/(4*L) by positivity))
  have hi : Tendsto (fun D : ℕ => 1/(c*(D : ℝ))) atTop (nhds 0) := by
    have h := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop.const_mul (1/c)
    simpa [div_eq_mul_inv,mul_inv_rev,mul_comm] using h
  have hb : Tendsto (fun D : ℕ => L/c^2*(harmonicHeight D/(D : ℝ))+1/(c*(D : ℝ))) atTop (nhds 0) := by
    simpa using (harmonicHeight_div_tendsto.const_mul (L/c^2)).add hi
  have h3 := hb.eventually (eventually_lt_nhds hm)
  have he : ∀ᶠ D : ℕ in atTop,3≤D ∧
      8*harmonicHeight D≤c*(D : ℝ) ∧
      4*L*(D : ℝ)*(harmonicHeight D)^2≤(c*(D : ℝ))^2 ∧
      (L/c^2* (harmonicHeight D/(D : ℝ))+1/(c*(D : ℝ)))≤min (1/5) (ζ/(1+1/c)) := by
    filter_upwards [eventually_ge_atTop 3,h1,h2,h3] with D hD ha hb hd
    have hDp : (0 : ℝ)<D := by exact_mod_cast (show 0<D by omega)
    have ha' := (div_lt_iff₀ hDp).mp ha
    have hb' := (div_lt_iff₀ hDp).mp hb
    have hb'' : 4*L*(harmonicHeight D)^2≤c^2*(D : ℝ) := by
      have hpos : 0<4*L := by positivity
      have := (mul_le_mul_of_nonneg_left hb'.le hpos.le)
      have heq : (4*L)*(c^2/(4*L)*(D : ℝ))=c^2*(D : ℝ) := by field_simp
      rw [heq] at this
      nlinarith
    refine ⟨hD,by nlinarith,?_,hd.le⟩
    have hh := mul_le_mul_of_nonneg_right hb'' hDp.le
    nlinarith
  exact Filter.eventually_atTop.mp he


theorem palette_envelope (c D s q : ℝ) (hc : 0<c) (hD : 3≤D)
    (hs : c*D≤s) (hq : q=s+2*D-2) :
    q*(D+s)/(s+1)^2≤(1+2/c)*(1+1/c) := by
  have hDp : 0<D := by linarith
  have hsp : 0<s := lt_of_lt_of_le (mul_pos hc hDp) hs
  have ht : 0<s+1 := by positivity
  have hqp : 0≤q := by rw [hq]; linarith
  have h1 : q/(s+1)≤1+2/c := by
    apply (div_le_iff₀ ht).2
    apply (mul_le_mul_iff_right₀ hc).mp
    have he : c*((1+2/c)*(s+1))=(c+2)*(s+1) := by field_simp
    rw [he,hq]
    nlinarith
  have h2 : (D+s)/(s+1)≤1+1/c := by
    apply (div_le_iff₀ ht).2
    apply (mul_le_mul_iff_right₀ hc).mp
    have he : c*((1+1/c)*(s+1))=(c+1)*(s+1) := by field_simp
    rw [he]
    nlinarith
  calc
    q*(D+s)/(s+1)^2=(q/(s+1))*((D+s)/(s+1)) := by rw [div_mul_div_comm,pow_two]
    _≤(1+2/c)*(1+1/c) := mul_le_mul h1 h2 (by positivity) (by positivity)

theorem degree_contraction_ratio (c D s : ℝ) (hc : 0<c) (hD : 3≤D)
    (hs : c*D≤s) :
    (D-1)*D/((D+s)*(s+1))≤1/(c*(1+c)) := by
  have hDp : 0<D := by linarith
  have hsp : 0<s := lt_of_lt_of_le (mul_pos hc hDp) hs
  have ht : 0<(D+s)*(s+1) := by positivity
  have hb : 0<c*(1+c) := by positivity
  apply (div_le_div_iff₀ ht hb).2
  have hprod : (1+c)*D*(c*D)≤(D+s)*(s+1) :=
    mul_le_mul (by nlinarith) (by linarith) (by positivity) (by positivity)
  have hh : (D-1)*D*(c*(1+c))≤(1+c)*D*(c*D) := by nlinarith [mul_pos hc (show 0<1+c by positivity)]
  nlinarith


theorem column_budget_bound (c D s L M h : ℝ) (hc : 0<c) (hD : 3≤D)
    (hs : c*D≤s) (hL : 0≤L) (hLM : L≤M) (hh : 0≤h) :
    L*(D-1)*h/(s+1)^2+1/(s+1)≤M/c^2*(h/D)+1/(c*D) := by
  have hDp : 0<D := by linarith
  have hcD : 0<c*D := mul_pos hc hDp
  have hsp : 0<s := hcD.trans_le hs
  have hM : 0≤M := hL.trans hLM
  have ht : c*D≤s+1 := by linarith
  have hd : (c*D)^2≤(s+1)^2 := by nlinarith
  have hn : L*(D-1)*h≤M*D*h := by
    apply mul_le_mul_of_nonneg_right _ hh
    exact mul_le_mul hLM (by linarith) (by linarith) hM
  have hb : L*(D-1)*h/(s+1)^2≤M/c^2*(h/D) := by
    calc
      _≤M*D*h/(s+1)^2 := div_le_div_of_nonneg_right hn (sq_nonneg _)
      _≤M*D*h/(c*D)^2 := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hcD) hd
      _=M/c^2*(h/D) := by field_simp
  exact add_le_add hb (one_div_le_one_div_of_le hcD ht)

theorem surplus_factor_bound (c D s : ℝ) (hc : 0<c) (hD : 0<D) (hs : c*D≤s) :
    (D+s)/s≤1+1/c := by
  have hsp := (mul_pos hc hD).trans_le hs
  have hr : D/s≤1/c := (div_le_div_iff₀ hsp hc).2 (by nlinarith)
  have he : (D+s)/s=1+D/s := by field_simp; ring
  rw [he]
  linarith


/-- A degree cutoff depending only on the fixed surplus ratio closes all three column
conditions and the perturbation budget, uniformly in the palette size. -/
theorem uniform_column_parameters (c ζ : ℝ) (hc : 0<c) (hζ : 0<ζ) :
    ∃ N : ℕ, ∀ D : ℕ, N≤D → ∀ s q : ℝ, c*(D : ℝ)≤s →
      q=s+2*(D : ℝ)-2 →
      let L := 22+8*(q*((D : ℝ)+s)/(s+1)^2)
      let b := L*((D : ℝ)-1)*harmonicHeight D/(s+1)^2
      3≤D ∧ 8*harmonicHeight D≤s+1 ∧
      4*L*(D : ℝ)*(harmonicHeight D)^2≤(s+1)^2 ∧
      b+1/(s+1)≤1/5 ∧ (b+1/(s+1))*((D : ℝ)+s)/s≤ζ := by
  let M : ℝ := 22+8*((1+2/c)*(1+1/c))
  have hM : 0<M := by dsimp [M]; positivity
  obtain ⟨N,hN⟩ := eventual_parameter_budget c M ζ hc hM hζ
  refine ⟨N,?_⟩
  intro D hD s q hs hq L b
  obtain ⟨hD3,hfirst,hsecond,hbudget⟩ := hN D hD
  have hDr : (3 : ℝ)≤D := by exact_mod_cast hD3
  have hDp : (0 : ℝ)<D := by linarith
  have hcD : 0<c*(D : ℝ) := mul_pos hc hDp
  have hsp : 0<s := hcD.trans_le hs
  have hD1 : 0≤(D : ℝ)-1 := by linarith
  have hh0 := harmonicHeight_nonneg D
  have hqp : 0≤q := by rw [hq]; linarith
  have hL : 0≤L := by dsimp [L]; positivity
  have hLM : L≤M := by
    have hv := palette_envelope c D s q hc hDr hs hq
    dsimp [L,M]
    linarith
  have hb := column_budget_bound c D s L M (harmonicHeight D) hc hDr hs hL hLM (harmonicHeight_nonneg D)
  change b+1/(s+1)≤_ at hb
  have hbmin := hb.trans hbudget
  have hδ : b+1/(s+1)≤ζ/(1+1/c) := hbmin.trans (min_le_right _ _)
  have hb0 : 0≤b+1/(s+1) := by dsimp [b]; positivity
  have hf := surplus_factor_bound c D s hc hDp hs
  refine ⟨hD3,by linarith,?_,hbmin.trans (min_le_left _ _),?_⟩
  · have hm : 4*L*(D : ℝ)*(harmonicHeight D)^2≤4*M*(D : ℝ)*(harmonicHeight D)^2 := by gcongr
    have ht : (c*(D : ℝ))^2≤(s+1)^2 := by nlinarith
    exact hm.trans (hsecond.trans ht)
  · have hmul := mul_le_mul_of_nonneg_left hf hb0
    have ht := (le_div_iff₀ (show 0<1+1/c by positivity)).mp hδ
    calc
      _=(b+1/(s+1))*(((D : ℝ)+s)/s) := by ring
      _≤(b+1/(s+1))*(1+1/c) := hmul
      _≤ζ := ht


theorem perturbed_degree_contraction {ε δ D s : ℝ} (hε : 0<ε) (hD : 3≤D)
    (hs : surplusRatio ε*D≤s) (hδ0 : 0≤δ) (hδ : δ≤perturbationMargin ε) :
    (1+δ)^2*((D-1)*D/((D+s)*(s+1)))≤(contractionRate ε)^2 := by
  have hc := surplusRatio_pos hε
  have hz := perturbationMargin_pos hε
  have hDp : 0<D := by linarith
  have hsp : 0<s := (mul_pos hc hDp).trans_le hs
  have hD1 : 0≤D-1 := by linarith
  have hratio := degree_contraction_ratio (surplusRatio ε) D s hc hD hs
  change (D-1)*D/((D+s)*(s+1))≤limitingGain ε at hratio
  have hsq : (1+δ)^2≤(1+perturbationMargin ε)^2 := by nlinarith
  calc
    _≤(1+perturbationMargin ε)^2*limitingGain ε :=
      mul_le_mul hsq hratio (by positivity) (sq_nonneg _)
    _=(contractionRate ε)^2 := perturbation_contraction_identity hε

/-- The original asymptotic threshold, with a cutoff uniform over all larger palettes. -/
theorem release_parameter_choice {ε : ℝ} (hε : 0<ε) :
    ∃ N : ℕ, ∀ D q : ℕ, N≤D → ((3+Real.sqrt 5)/2+ε)*(D : ℝ)≤q →
      let s := (q : ℝ)-2*(D : ℝ)+2
      let L := 22+8*((q : ℝ)*((D : ℝ)+s)/(s+1)^2)
      let b := L*((D : ℝ)-1)*harmonicHeight D/(s+1)^2
      let δ := (b+1/(s+1))*((D : ℝ)+s)/s
      3≤D ∧ 0<s ∧ surplusRatio ε*(D : ℝ)≤s ∧
      8*harmonicHeight D≤s+1 ∧
      4*L*(D : ℝ)*(harmonicHeight D)^2≤(s+1)^2 ∧ b+1/(s+1)≤1/5 ∧
      0≤δ ∧ δ≤perturbationMargin ε ∧
      (1+δ)^2*(((D : ℝ)-1)*(D : ℝ)/(((D : ℝ)+s)*(s+1)))≤(contractionRate ε)^2 := by
  have hc := surplusRatio_pos hε
  obtain ⟨N,hN⟩ := uniform_column_parameters (surplusRatio ε) (perturbationMargin ε) hc (perturbationMargin_pos hε)
  refine ⟨N,?_⟩
  intro D q hDN hq s L b δ
  have hs : surplusRatio ε*(D : ℝ)≤s := by
    dsimp [s,surplusRatio,surplusThreshold]
    nlinarith
  have he : (q : ℝ)=s+2*(D : ℝ)-2 := by dsimp [s]; ring
  obtain ⟨hD3,hfirst,hsecond,hbudget,hδ⟩ := hN D hDN s q hs he
  have hDr : (3 : ℝ)≤D := by exact_mod_cast hD3
  have hDp : (0 : ℝ)<D := by linarith
  have hsp : 0<s := (mul_pos hc hDp).trans_le hs
  have hL : 0≤L := by dsimp [L]; positivity
  have hD1 : 0≤(D : ℝ)-1 := by linarith
  have hh := harmonicHeight_nonneg D
  have hb : 0≤b := by dsimp [b]; positivity
  have hδ0 : 0≤δ := by dsimp [δ]; positivity
  exact ⟨hD3,hsp,hs,hfirst,hsecond,hbudget,hδ0,hδ,
    perturbed_degree_contraction hε hDr hs hδ0 hδ⟩

end EdgeColoringMixing
