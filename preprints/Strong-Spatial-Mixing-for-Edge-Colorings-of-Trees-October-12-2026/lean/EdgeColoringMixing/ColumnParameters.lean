import EdgeColoringMixing.Parameters

set_option autoImplicit false
namespace EdgeColoringMixing

noncomputable def columnError (L t : ℝ) (k : ℕ) : ℝ :=
  L*((k : ℝ)-1)*harmonicHeight k/t^2

theorem harmonicHeight_mono {k D : ℕ} (hk : k≤D) : harmonicHeight k≤harmonicHeight D := by
  unfold harmonicHeight harmonic
  push_cast
  gcongr

theorem columnError_nonneg {L t : ℝ} (hL : 0≤L) {k : ℕ} (hk : 1≤k) :
    0≤columnError L t k := by
  have hk1 : 0≤(k : ℝ)-1 := by
    have : (1 : ℝ)≤k := by exact_mod_cast hk
    linarith
  have hh := harmonicHeight_nonneg k
  unfold columnError
  positivity

theorem columnError_mono {L t : ℝ} (hL : 0≤L) {k D : ℕ} (hk : 1≤k) (hkD : k≤D) :
    columnError L t k≤columnError L t D := by
  have hD1 : 0≤(D : ℝ)-1 := by
    have : (1 : ℝ)≤D := by exact_mod_cast hk.trans hkD
    linarith
  have hh := harmonicHeight_nonneg k
  have hkd : (k : ℝ)-1≤(D : ℝ)-1 := by
    have : (k : ℝ)≤D := by exact_mod_cast hkD
    linarith
  unfold columnError
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hkd hL)
    (harmonicHeight_mono hkD) hh (mul_nonneg hL hD1)

theorem columnError_two {t V : ℝ} (hV : 0≤V) :
    10/t^2≤columnError (22+8*V) t 2 := by
  simp only [columnError,harmonicHeight,Nat.reduceSubDiff,harmonic_zero,Rat.cast_zero,Nat.cast_ofNat]
  norm_num
  apply div_le_div_of_nonneg_right _ (sq_nonneg t)
  linarith

theorem harmonicHeight_step {k : ℕ} (hk : 3≤k) :
    harmonicHeight k-harmonicHeight (k-1)=1/((k : ℝ)-2) := by
  have he : k-2=(k-1-2)+1 := by omega
  unfold harmonicHeight
  rw [he,harmonic_succ]
  push_cast
  have hn : ((k-1-2+1 : ℕ) : ℝ)=(k : ℝ)-2 := by
    rw [←he,Nat.cast_sub (by omega)]
    norm_num
  push_cast at hn
  rw [hn]
  ring

theorem columnError_difference {L t : ℝ} {k : ℕ} (hk : 3≤k) :
    ((k : ℝ)-2)*columnError L t k-((k : ℝ)-1)*columnError L t (k-1)=L*((k : ℝ)-1)/t^2 := by
  have hk2 : (k : ℝ)-2≠0 := by
    have : (3 : ℝ)≤k := by exact_mod_cast hk
    linarith
  have hh := harmonicHeight_step hk
  unfold columnError
  rw [Nat.cast_sub (by omega : 1≤k),Nat.cast_one]
  calc
    _=L*((k : ℝ)-1)*((k : ℝ)-2)*(harmonicHeight k-harmonicHeight (k-1))/t^2 := by ring
    _=L*((k : ℝ)-1)/t^2 := by rw [hh]; field_simp


theorem columnError_recursion {t V : ℝ} (ht : 0<t) (hV : 0≤V) {k D : ℕ}
    (hk : 3≤k) (hkD : k≤D)
    (hfirst : 8*harmonicHeight D≤t)
    (hsecond : 4*(22+8*V)*(D : ℝ)*(harmonicHeight D)^2≤t^2) :
    (1+4*V)*((k : ℝ)-1)/t^2+2*columnError (22+8*V) t k/t+
      (columnError (22+8*V) t k)^2≤
      ((k : ℝ)-2)*columnError (22+8*V) t k-
      ((k : ℝ)-1)*columnError (22+8*V) t (k-1) := by
  let L : ℝ := 22+8*V
  let A : ℝ := L*((k : ℝ)-1)/t^2
  have hL : 0<L := by dsimp [L]; positivity
  have hkr : (3 : ℝ)≤k := by exact_mod_cast hk
  have hkDr : (k : ℝ)≤D := by exact_mod_cast hkD
  have hk1 : 0≤(k : ℝ)-1 := by linarith
  have hh := harmonicHeight_nonneg k
  have hhD := harmonicHeight_nonneg D
  have hmono := harmonicHeight_mono hkD
  have hA : 0≤A := by dsimp [A]; positivity
  have hbase : (1+4*V)*((k : ℝ)-1)/t^2≤A/2 := by
    have hcoef : 1+4*V≤L/2 := by dsimp [L]; linarith
    have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hk1) (sq_nonneg t)
    dsimp [A]
    convert h using 1; ring
  have he : columnError L t k=A*harmonicHeight k := by dsimp [columnError,A]; ring
  have hlin : 2*columnError L t k/t≤A/4 := by
    have hrat : 2*harmonicHeight k/t≤1/4 := (div_le_iff₀ ht).2 (by linarith)
    calc
      _=A*(2*harmonicHeight k/t) := by rw [he]; ring
      _≤A*(1/4) := mul_le_mul_of_nonneg_left hrat hA
      _=A/4 := by ring
  have hsq : (columnError L t k)^2≤A/4 := by
    have hb : 4*L*((k : ℝ)-1)*(harmonicHeight k)^2≤t^2 := by
      have hprod : ((k : ℝ)-1)*(harmonicHeight k)^2≤(D : ℝ)*(harmonicHeight D)^2 :=
        mul_le_mul (by linarith) (by nlinarith) (sq_nonneg _) (by linarith)
      calc
        _=(4*L)*(((k : ℝ)-1)*(harmonicHeight k)^2) := by ring
        _≤(4*L)*((D : ℝ)*(harmonicHeight D)^2) := mul_le_mul_of_nonneg_left hprod (by positivity)
        _=4*L*(D : ℝ)*(harmonicHeight D)^2 := by ring
        _≤t^2 := by simpa [L] using hsecond
    have hrat : A*(harmonicHeight k)^2≤1/4 := by
      dsimp [A]
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (sq_pos_of_pos ht)).2
      nlinarith
    calc
      _=A*(A*(harmonicHeight k)^2) := by rw [he]; ring
      _≤A*(1/4) := mul_le_mul_of_nonneg_left hrat hA
      _=A/4 := by ring
  rw [columnError_difference hk]
  change _≤A
  change (1+4*V)*((k : ℝ)-1)/t^2+2*columnError L t k/t+(columnError L t k)^2≤A
  linarith



theorem columnError_spectral_cap {L t : ℝ} (hL : 0≤L) {k D : ℕ}
    (hk : 2≤k) (hkD : k≤D) (hbudget : columnError L t D+1/t≤1/5) :
    (columnError L t k+1/t)/((k : ℝ)-1)≤((k : ℝ)-1)/(3*(k : ℝ)-1) := by
  have hkr : (2 : ℝ)≤k := by exact_mod_cast hk
  have hk1 : 0<(k : ℝ)-1 := by linarith
  have hk3 : 0<3*(k : ℝ)-1 := by linarith
  have hb : columnError L t k+1/t≤1/5 := by
    have hm := columnError_mono (t := t) hL (show 1≤k by omega) hkD
    linarith
  calc
    _≤(1/5)/((k : ℝ)-1) := div_le_div_of_nonneg_right hb hk1.le
    _≤((k : ℝ)-1)/(3*(k : ℝ)-1) := by
      apply (div_le_div_iff₀ hk1 hk3).2
      nlinarith [sq_nonneg ((k : ℝ)-2)]

end EdgeColoringMixing
