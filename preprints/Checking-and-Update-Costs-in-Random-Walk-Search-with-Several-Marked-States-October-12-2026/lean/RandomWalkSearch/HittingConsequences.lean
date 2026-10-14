import RandomWalkSearch.ConsecutiveEndpoints
import RandomWalkSearch.Restoration

/-! # Actual stationary hitting costs and the no-uniform-split consequence

The hitting cost is the supremum of counters from the genuinely stopped lazy
walk. The corollary needs only the upper bound derived from actual exit times;
it does not define the hitting cost by a closed formula.
-/
noncomputable section
namespace RandomWalkSearch.Cycle
open MeasureTheory LazyWalk
open scoped ENNReal BigOperators
variable {k : ℕ}

theorem card_arc_of_le (x : Vertex k) (d : ℕ) (hd : d ≤ N k) : (arc x d).card = d := by
  classical
  rw [arc, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj he
  have hcast : (i : Vertex k) = j := add_left_cancel he
  have hv := congrArg ZMod.val hcast
  simpa only [ZMod.val_natCast_of_lt ((Finset.mem_range.mp hi).trans_le hd),
    ZMod.val_natCast_of_lt ((Finset.mem_range.mp hj).trans_le hd)] using hv

def markedMass [NeZero (N k)] (a : Vertex k) : ℝ≥0∞ := (marked a).card / (N k : ℝ≥0∞)

theorem markedMass_ge (hk : 0 < k) [NeZero (N k)] (a : Vertex k) :
    (1 : ℝ≥0∞) / k ≤ markedMass a := by
  have hd : D k ≤ N k := by
    exact pow_le_pow_right₀ hk (by decide : 7 ≤ 8)
  have hc : D k ≤ (marked a).card := by
    rw [← card_arc_of_le a (D k) hd]
    exact Finset.card_le_card Finset.subset_union_left
  have hN : (N k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (N_pos hk).ne'
  have hk0 : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  have hd0 : (D k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (D_pos hk).ne'
  have hr : (D k : ℝ≥0∞) / N k = 1 / k := by
    rw [N_eq_dense]
    push_cast
    rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hk0) (Or.inr hd0), ← mul_assoc,
      mul_comm (D k : ℝ≥0∞) (k : ℝ≥0∞)⁻¹, mul_assoc,
      ENNReal.mul_inv_cancel hd0 (ENNReal.natCast_ne_top _), mul_one, one_div]
  rw [← hr]
  exact mul_le_mul (show (D k : ℝ≥0∞) ≤ (marked a).card by exact_mod_cast hc)
    (le_rfl : (N k : ℝ≥0∞)⁻¹ ≤ (N k : ℝ≥0∞)⁻¹) (by positivity) (by positivity)

structure HitState (k : ℕ) where
  vertex : Vertex k
  elapsed : ℕ

def hitAdvance (a : Vertex k) (s : HitState k) (q : Fin 4) : HitState k :=
  if s.vertex ∈ marked a then s else ⟨s.vertex + (increment q).value, s.elapsed + 1⟩

def hitRun (a z : Vertex k) : (n : ℕ) → Tape n → HitState k
  | 0, _ => ⟨z, 0⟩
  | n+1, t => hitAdvance a (hitRun a z n t.1) t.2

/-- The actual first marked-vertex hitting cost, including zero when started
marked and infinity if the trajectory never reaches a marked vertex. -/
def hittingENN (a z : Vertex k) (w : ℕ → Fin 4) : ℝ≥0∞ :=
  ⨆ n, ((hitRun a z n (prefixTape n w)).elapsed : ℝ≥0∞)

theorem hitRun_before (a z : Vertex k) (w : ℕ → Fin 4) (n : ℕ)
    (hn : ∀ t<n, z + (integerWalk w t : Vertex k) ∉ marked a) :
    hitRun a z n (prefixTape n w) = ⟨z + (integerWalk w n : Vertex k), n⟩ := by
  induction n with
  | zero => simp [hitRun, integerWalk]
  | succ n ih =>
    have hh := ih (fun t ht => hn t (by omega))
    simp [hitRun, prefixTape, hh, hitAdvance, hn n (by omega), integerWalk, add_assoc]

theorem hitRun_at_first (a z : Vertex k) (w : ℕ → Fin 4) (t : ℕ)
    (ht : z + (integerWalk w t : Vertex k) ∈ marked a)
    (hbefore : ∀ j<t, z + (integerWalk w j : Vertex k) ∉ marked a) (n : ℕ) :
    hitRun a z n (prefixTape n w) =
      ⟨z + (integerWalk w (min n t) : Vertex k), min n t⟩ := by
  induction n with
  | zero => simp [hitRun, integerWalk]
  | succ n ih =>
    by_cases hn : n<t
    · have hm : min n t=n := Nat.min_eq_left hn.le
      have hm' : min (n+1) t=n+1 := Nat.min_eq_left (by omega)
      simp [hitRun, prefixTape, ih, hm, hm', hitAdvance, hbefore n hn, integerWalk, add_assoc]
    · have hm : min n t=t := Nat.min_eq_right (by omega)
      have hm' : min (n+1) t=t := Nat.min_eq_right (by omega)
      simp [hitRun, prefixTape, ih, hm, hm', hitAdvance, ht]

theorem hittingENN_at_first (a z : Vertex k) (w : ℕ → Fin 4) (t : ℕ)
    (ht : z + (integerWalk w t : Vertex k) ∈ marked a)
    (hbefore : ∀ j<t, z + (integerWalk w j : Vertex k) ∉ marked a) :
    hittingENN a z w = t := by
  unfold hittingENN
  simp only [hitRun_at_first a z w t ht hbefore]
  apply le_antisymm
  · exact iSup_le (fun n => by exact_mod_cast (Nat.min_le_right n t))
  · simpa only [min_self] using
      le_iSup (fun n : ℕ => ((min n t : ℕ) : ℝ≥0∞)) t

theorem hittingENN_of_no_hit (a z : Vertex k) (w : ℕ → Fin 4)
    (hn : ∀ t, z + (integerWalk w t : Vertex k) ∉ marked a) :
    hittingENN a z w = ∞ := by
  unfold hittingENN
  simp only [hitRun_before a z w _ (fun t _ => hn t), ENNReal.iSup_natCast]

theorem hittingENN_le_of_hit (a z : Vertex k) (w : ℕ → Fin 4) (t : ℕ)
    (ht : z + (integerWalk w t : Vertex k) ∈ marked a) : hittingENN a z w ≤ t := by
  have he : ∃s, z + (integerWalk w s : Vertex k) ∈ marked a := ⟨t,ht⟩
  have hfirst := Nat.find_spec he
  have hmin := Nat.find_min' he ht
  unfold hittingENN
  apply iSup_le
  intro n
  rw [hitRun_at_first a z w (Nat.find he) hfirst (fun j hj => Nat.find_min he hj) n]
  exact_mod_cast (Nat.min_le_right n (Nat.find he)).trans hmin

theorem mem_trail_iff (z : ℕ → Vertex k) (w : ℕ → ℕ → Fin 4) (n : ℕ) (x : Vertex k) :
    x ∈ (EndpointPolicy.trail (lazyTapes z w) n).visited ↔
      ∃ t≤n, x = z 0 + (integerWalk (w 0) t : Vertex k) := by
  induction n with
  | zero => simp [EndpointPolicy.trail, integerWalk, lazyTapes]
  | succ n ih =>
    rw [EndpointPolicy.trail, History.visited_cons_update, Finset.mem_insert, ih, lazy_trajectory]
    constructor
    · rintro (he | ⟨t,ht,he⟩)
      · exact ⟨n+1,le_rfl,he⟩
      · exact ⟨t,by omega,he⟩
    · rintro ⟨t,ht,he⟩
      by_cases heq : t=n+1
      · exact Or.inl (by simpa [heq] using he)
      · exact Or.inr ⟨t,by omega,he⟩

variable [NeZero (N k)] [NeZero (L k)]

theorem hittingENN_le_exit (hk : 0<k) (a z : Vertex k) (w : ℕ → Fin 4) :
    hittingENN a z w ≤ exitENN (L k) w := by
  classical
  by_cases he : ∃n, (L k : ℤ) ≤ |integerWalk w n|
  · let t := Nat.find he
    have ht := first_exit_boundary he
    rw [exitENN_at_first w ht (fun j hj => lt_of_not_ge (Nat.find_min he hj))]
    have hc := covers_phase_at_exit (L k) (L_dvd_N k) (fun _ => z) (fun _ => w) t ht
    obtain ⟨x,hx,hphase⟩ := hc (phase (L k) (L_dvd_N k) a)
    obtain ⟨s,hs,hxs⟩ := (mem_trail_iff (fun _ => z) (fun _ => w) t x).mp hx
    have hm : x ∈ marked a := Finset.mem_union_right _ ((mem_progression_iff_phase hk a x).mpr hphase)
    have hh := hittingENN_le_of_hit a z w s (hxs ▸ hm)
    exact hh.trans (by exact_mod_cast hs)
  · rw [exitENN_of_no_exit (L k) w he]
    exact le_top

variable {Ω : Type*} [MeasurableSpace Ω]

omit [NeZero (N k)] [NeZero (L k)] in
theorem measurable_hittingENN (μ : Measure Ω) (w : Ω → ℕ → Fin 4)
    (hlaw : IID μ w) (a z : Vertex k) : Measurable fun ω => hittingENN a z (w ω) := by
  apply Measurable.iSup
  intro n
  exact measurable_finite_prefix μ w hlaw n (fun t => ((hitRun a z n t).elapsed : ℝ≥0∞))

theorem lintegral_hitting_le (μ : Measure Ω) (w : Ω → ℕ → Fin 4)
    (hlaw : IID μ w) (hk : 0<k) (a z : Vertex k) :
    (∫⁻ ω, hittingENN a z (w ω) ∂μ) ≤ ENNReal.ofReal (2*(L k : ℝ)^2) := by
  exact (lintegral_mono (fun ω => hittingENN_le_exit hk a z (w ω))).trans_eq
    (lintegral_exitENN μ w hlaw (L k))

/-- Hitting time from genuine uniform stationarity; it includes marked starts
and is not conditioned on the initial vertex being unmarked. -/
def stationaryHitting (μ : Measure Ω) (w : Ω → ℕ → Fin 4) (a : Vertex k) : ℝ≥0∞ :=
  (∑ z : Vertex k, ∫⁻ ω, hittingENN a z (w ω) ∂μ) / N k

theorem stationaryHitting_le (μ : Measure Ω) (w : Ω → ℕ → Fin 4)
    (hlaw : IID μ w) (hk : 0<k) (a : Vertex k) :
    stationaryHitting μ w a ≤ ENNReal.ofReal (2*(L k : ℝ)^2) := by
  have hN : (N k : ℝ≥0∞) ≠ 0 := by exact_mod_cast (N_pos hk).ne'
  have hs := Finset.sum_le_sum (s := (Finset.univ : Finset (Vertex k)))
    (fun z _ => lintegral_hitting_le μ w hlaw hk a z)
  have hh := mul_le_mul hs (le_rfl : (N k : ℝ≥0∞)⁻¹ ≤ (N k : ℝ≥0∞)⁻¹)
  simpa [stationaryHitting, Finset.sum_const, nsmul_eq_mul, ZMod.card,
    mul_comm (N k : ℝ≥0∞), ← div_eq_mul_inv,
    ENNReal.mul_div_cancel_right hN (ENNReal.natCast_ne_top _)] using hh

omit [NeZero (N k)] [NeZero (L k)] in
/-- The source threshold 66C already follows from the genuine upper bound
H≤2L², so the no-split conclusion does not rely on stipulating an H formula. -/
theorem no_uniform_split_arithmetic (C a c : ℝ) (hC : 1 ≤ C)
    (hk : 66*C ≤ k) (ha : a ≤ 2*C*(k:ℝ)^4) (hc : c ≤ C*k) :
    c/(L k : ℝ) + a/(N k : ℝ) < 1/64 := by
  have hk66 : (66:ℝ) ≤ k := by linarith
  have hkpos : (0:ℝ) < k := by linarith
  have hk0 := ne_of_gt hkpos
  have hcu : c/(k:ℝ)^2 ≤ C/k := by
    calc
      _ ≤ (C*k)/(k:ℝ)^2 := div_le_div_of_nonneg_right hc (by positivity)
      _ = _ := by field_simp
  have hau : a/(k:ℝ)^8 ≤ 2*C/(k:ℝ)^4 := by
    calc
      _ ≤ (2*C*(k:ℝ)^4)/(k:ℝ)^8 := div_le_div_of_nonneg_right ha (by positivity)
      _ = _ := by field_simp
  have hcsmall : C/(k:ℝ) ≤ 1/66 := (div_le_iff₀ hkpos).mpr (by linarith)
  have hk3 : (128:ℝ) ≤ (k:ℝ)^3 := by
    have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤66) hk66 3
    norm_num at hp
    linarith
  have hk4 : 128*(k:ℝ) ≤ (k:ℝ)^4 := by
    have hm := mul_le_mul_of_nonneg_left hk3 hkpos.le
    nlinarith
  have hasmall : 2*C/(k:ℝ)^4 ≤ 1/4224 :=
    (div_le_iff₀ (by positivity)).mpr (by nlinarith)
  simp only [L,N,Nat.cast_pow]
  linarith

/-- The original no-uniform-single-marked-cost-split conclusion, stated using
actual marked mass and actual hitting time from uniform stationarity. -/
theorem Randomized.no_uniform_split (A : Randomized k Ω) (μ : Measure Ω)
    [IsProbabilityMeasure μ] (hobs : A.Observable) (hlaw : A.LazyLaw μ)
    (b : ℕ) (hb : 1≤b) (hk : 16*(b+1)≤k) (C : ℝ) (hC : 1≤C)
    (hkC : 66*C≤k) (hA : A.Restoration b)
    (hs : ∀a, (1:ℝ≥0∞)/2 ≤ A.success μ a) (a₀ : Vertex k) :
    ¬ (A.averageUpdates μ ≤ ENNReal.ofReal C * stationaryHitting μ (fun ω => A.increments ω 0) a₀ ∧
       A.averageChecks μ ≤ ENNReal.ofReal C / markedMass a₀) := by
  rintro ⟨ha,hc⟩
  have hkpos : 0<k := by omega
  have hCn : 0≤C := by linarith
  have hH := stationaryHitting_le μ (fun ω => A.increments ω 0) (hlaw 0) hkpos a₀
  have haB : A.averageUpdates μ ≤ ENNReal.ofReal (2*C*(k:ℝ)^4) := by
    have h := ha.trans (mul_le_mul (le_rfl : ENNReal.ofReal C ≤ ENNReal.ofReal C)
      hH (by positivity) (by positivity))
    have he : C*(2*(L k:ℝ)^2) = 2*C*(k:ℝ)^4 := by simp [L]; ring
    simpa only [← ENNReal.ofReal_mul hCn, he] using h
  have hcB : A.averageChecks μ ≤ ENNReal.ofReal (C*k) := by
    have h := hc.trans (ENNReal.div_le_div_left (markedMass_ge hkpos a₀) (ENNReal.ofReal C))
    simpa [div_eq_mul_inv, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hCn] using h
  have haFin : A.averageUpdates μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top haB
  have hcFin : A.averageChecks μ ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcB
  have har := ENNReal.toReal_mono ENNReal.ofReal_ne_top haB
  have hcr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hcB
  rw [ENNReal.toReal_ofReal (by positivity)] at har hcr
  have hsmall := no_uniform_split_arithmetic C (A.averageUpdates μ).toReal
    (A.averageChecks μ).toReal hC hkC har hcr
  have hN : (N k:ℝ≥0∞)≠0 := by exact_mod_cast (N_pos hkpos).ne'
  have hL : (L k:ℝ≥0∞)≠0 := by exact_mod_cast (L_pos hkpos).ne'
  have hmain := A.restoration_lower_bound μ hobs b hb hk hA hs
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.div_ne_top hcFin hL, ENNReal.div_ne_top haFin hN⟩) hmain
  rw [ENNReal.toReal_add (ENNReal.div_ne_top hcFin hL) (ENNReal.div_ne_top haFin hN)] at hr
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast] at hr
  norm_num at hr
  exact (not_lt_of_ge hr) hsmall

end RandomWalkSearch.Cycle
