import ArithmeticSections.BestApproximation
import ArithmeticSections.SecondDistance

namespace ArithmeticSections

/-- A unimodular numerator permutes the residue classes, with representatives 1,...,q. -/
theorem grid_representative {p q u v : ℤ} (hq : 0 < q)
    (hbez : p * u + q * v = 1) (j : ℤ) :
    ∃ r : ℕ, 1 ≤ r ∧ (r : ℤ) ≤ q ∧ ∃ z : ℤ, p * r - j = q * z := by
  let a : ℤ := u * j - 1
  let r : ℤ := a % q + 1
  have hrpos : 0 < r := by dsimp [r]; have := Int.emod_nonneg a (ne_of_gt hq); omega
  have hrle : r ≤ q := by dsimp [r]; have := Int.emod_lt_of_pos a hq; omega
  have hr : (r.toNat : ℤ) = r := Int.toNat_of_nonneg hrpos.le
  refine ⟨r.toNat, by omega, by omega, -v * j - p * (a / q), ?_⟩
  rw [hr]
  have ha := Int.emod_add_mul_ediv a q
  dsimp [a, r] at *
  nlinarith [congrArg (fun x : ℤ => x * j) hbez, congrArg (fun x : ℤ => p * x) ha]

/-- The two consecutive grid points have different representatives. -/
theorem grid_representatives_ne {p q j z z' : ℤ} {r s : ℕ}
    (hq : 2 ≤ q) (hr : p * r - j = q * z)
    (hs : p * s - (j + 1) = q * z') : r ≠ s := by
  intro he
  rw [he] at hr
  have hd : q ∣ (1 : ℤ) := ⟨z - z', by nlinarith⟩
  have := Int.le_of_dvd (by norm_num : (0 : ℤ) < 1) hd
  omega

/-- A grid point adjacent to qθ/2 gives a small odd-multiple distance. -/
theorem grid_distance_bound {θ : ℝ} {p q j z : ℤ} {r : ℕ}
    (hq : 0 < q) (hr : 1 ≤ r) (hrq : (r : ℤ) ≤ q)
    (hrep : p * r - j = q * z)
    (hj : |(j : ℝ) - q * θ / 2| ≤ 1)
    (herr : |(q : ℝ) * θ - p| < 1 / (q : ℝ)) :
    integerDistance (((r : ℝ) - 1 / 2) * θ) < 2 / (q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrqR : (r : ℝ) ≤ q := by exact_mod_cast hrq
  have hrepR : (p : ℝ) * r - j = q * z := by exact_mod_cast hrep
  have he : ((r : ℝ) - 1 / 2) * θ - z =
      ((r : ℝ) / q) * ((q : ℝ) * θ - p) + ((j : ℝ) - q * θ / 2) / q := by
    field_simp
    nlinarith
  have hfrac : 0 < (r : ℝ) / q := div_pos hrR hqR
  have hfrac1 : (r : ℝ) / q ≤ 1 := (div_le_one hqR).mpr hrqR
  calc
    integerDistance (((r : ℝ) - 1 / 2) * θ) ≤
        |((r : ℝ) - 1 / 2) * θ - z| := integerDistance_le_sub_integer _ z
    _ = |((r : ℝ) / q) * ((q : ℝ) * θ - p) + ((j : ℝ) - q * θ / 2) / q| := by rw [he]
    _ ≤ |((r : ℝ) / q) * ((q : ℝ) * θ - p)| + |((j : ℝ) - q * θ / 2) / q| := abs_add_le _ _
    _ = ((r : ℝ) / q) * |(q : ℝ) * θ - p| + |(j : ℝ) - q * θ / 2| / q := by
      rw [abs_mul, abs_of_pos hfrac, abs_div, abs_of_pos hqR]
    _ < ((r : ℝ) / q) * (1 / (q : ℝ)) + 1 / (q : ℝ) :=
      add_lt_add_of_lt_of_le (mul_lt_mul_of_pos_left herr hfrac) (div_le_div_of_nonneg_right hj hqR.le)
    _ ≤ 1 / (q : ℝ) + 1 / (q : ℝ) := by
      have := mul_le_mul_of_nonneg_right hfrac1 (show 0 ≤ 1 / (q : ℝ) by positivity)
      linarith
    _ = 2 / (q : ℝ) := by ring

/-- Two actual odd multiples are within 2/q of integers for each unimodular approximant. -/
theorem two_grid_distances {θ : ℝ} {p q u v : ℤ} (hq : 2 ≤ q)
    (hbez : p * u + q * v = 1)
    (herr : |(q : ℝ) * θ - p| < 1 / (q : ℝ)) :
    ∃ r s : ℕ, 1 ≤ r ∧ (r : ℤ) ≤ q ∧ 1 ≤ s ∧ (s : ℤ) ≤ q ∧ r ≠ s ∧
      integerDistance (((r : ℝ) - 1 / 2) * θ) < 2 / (q : ℝ) ∧
      integerDistance (((s : ℝ) - 1 / 2) * θ) < 2 / (q : ℝ) := by
  let j : ℤ := ⌊(q : ℝ) * θ / 2⌋
  obtain ⟨r, hr, hrq, z, hz⟩ := grid_representative (by omega : 0 < q) hbez j
  obtain ⟨s, hs, hsq, z', hz'⟩ := grid_representative (by omega : 0 < q) hbez (j + 1)
  have hj1 := Int.floor_le ((q : ℝ) * θ / 2)
  have hj2 := Int.lt_floor_add_one ((q : ℝ) * θ / 2)
  refine ⟨r, s, hr, hrq, hs, hsq, grid_representatives_ne hq hz hz', ?_, ?_⟩
  · apply grid_distance_bound (by omega : 0 < q) hr hrq hz _ herr
    apply abs_le.mpr
    dsimp [j]
    constructor <;> linarith
  · apply grid_distance_bound (by omega : 0 < q) hs hsq hz' _ herr
    apply abs_le.mpr
    dsimp [j]
    push_cast
    constructor <;> linarith

/-- Lemma 3.2 for actual convergents; the direct adjacent-grid proof gives 2π/q. -/
theorem secondDistance_lt_convergent {θ : ℝ} (hθ : Irrational θ)
    (hlo : 0 ≤ θ) (hhi : θ < 1) (n : ℕ)
    (hq : 2 ≤ actualDenominator θ (n + 1)) {k : ℕ}
    (hk : actualDenominator θ (n + 1) ≤ k) :
    secondDistance (θ / 2) k < 2 * Real.pi / (actualDenominator θ (n + 1) : ℝ) := by
  let p : ℤ := actualNumerator θ (n + 1)
  let q : ℤ := actualDenominator θ (n + 1)
  let p' : ℤ := actualNumerator θ n
  let q' : ℤ := actualDenominator θ n
  let D : ℤ := p * q' - p' * q
  have hD : D ^ 2 = 1 := by
    change ((numerator (actualDigit θ) (n + 1) : ℤ) * denominator (actualDigit θ) n -
      (numerator (actualDigit θ) n : ℤ) * denominator (actualDigit θ) (n + 1)) ^ 2 = 1
    rw [continuant_determinant, ← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  have hbez : p * (q' * D) + q * (-p' * D) = 1 := by
    calc
      _ = D ^ 2 := by dsimp [D]; ring
      _ = 1 := hD
  have hqR : (0 : ℝ) < actualDenominator θ (n + 1) := by exact_mod_cast (show 0 < actualDenominator θ (n + 1) by omega)
  have hqn : (actualDenominator θ (n + 1) : ℝ) ≤ actualDenominator θ (n + 2) := by
    exact_mod_cast denominator_mono_step (one_le_actualDigit_succ hθ) (n + 1)
  have herr : |(q : ℝ) * θ - p| < 1 / (q : ℝ) := by
    simpa only [p, q, Int.cast_natCast] using
      (lt_of_lt_of_le (actual_error_bounds hθ hlo hhi n).2 (one_div_le_one_div_of_le hqR hqn))
  obtain ⟨r, s, hr, hrq, hs, hsq, hrs, hdr, hds⟩ :=
    two_grid_distances (by dsimp [q]; exact_mod_cast hq) hbez herr
  have hrk : r ≤ k := by dsimp [q] at hrq; omega
  have hsk : s ≤ k := by dsimp [q] at hsq; omega
  have hp : secondDistance (θ / 2) k ≤ max (oddDistance (θ / 2) r) (oddDistance (θ / 2) s) := by
    convert secondDistance_le_pair (γ := θ / 2) (i := r - 1) (j := s - 1)
      (by omega : r - 1 < k) (by omega : s - 1 < k) (by omega : r - 1 ≠ s - 1) using 1
    congr 2 <;> omega
  apply lt_of_le_of_lt hp
  apply max_lt
  · have he : (2 * (r : ℝ) - 1) * (θ / 2) = ((r : ℝ) - 1 / 2) * θ := by ring
    unfold oddDistance
    rw [he]
    have hd := mul_lt_mul_of_pos_left hdr Real.pi_pos
    dsimp [q] at hd
    push_cast at hd
    convert hd using 1
    ring
  · have he : (2 * (s : ℝ) - 1) * (θ / 2) = ((s : ℝ) - 1 / 2) * θ := by ring
    unfold oddDistance
    rw [he]
    have hd := mul_lt_mul_of_pos_left hds Real.pi_pos
    dsimp [q] at hd
    push_cast at hd
    convert hd using 1
    ring

end ArithmeticSections
