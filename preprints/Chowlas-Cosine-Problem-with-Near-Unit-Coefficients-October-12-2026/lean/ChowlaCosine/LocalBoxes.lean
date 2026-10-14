import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic
import Mathlib.Tactic.Ring

namespace ChowlaCosine

noncomputable def localReal (t a b c d e : ℝ) : ℝ :=
  t*a*a/4-t*a*b-t*a*c/2-(t+1)*b*b+t*b*c+2*b*d+(4+t/2)*c*c+t*c*d-t*c*e/2-(t+1)*d*d-t*d*e+t*e*e/4

noncomputable def localImaginary (t a b c d e : ℝ) : ℝ :=
  -t*a*a/4-t*a*b+t*a*c/2+t*b*b+(t+4)*b*c-(4+t)*c*d-t*c*e/2-t*d*d+t*d*e+t*e*e/4

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem local_box_00000 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (0+a) (0+b) (0+c) (0+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (0+b) (0+c) (0+d) (0+e) ∧
    localImaginary t (0+a) (0+b) (0+c) (0+d) (0+e) ≤ 8 := by
  have hr : localReal t (0+a) (0+b) (0+c) (0+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((((1/4 : ℚ) : ℝ) * t) * e^2) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (0+b) (0+c) (0+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + (t * b^2) + ((4 + t) * b * c) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-1 * t) * d^2) + (t * d * e) + ((((1/4 : ℚ) : ℝ) * t) * e^2) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_00001 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (0+a) (0+b) (0+c) (0+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (0+b) (0+c) (0+d) (1+e) ∧
    localImaginary t (0+a) (0+b) (0+c) (0+d) (1+e) ≤ 8 := by
  have hr : localReal t (0+a) (0+b) (0+c) (0+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((-1/2 : ℚ) : ℝ) * t) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-1 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((1/2 : ℚ) : ℝ) * t) * e) + ((((1/4 : ℚ) : ℝ) * t)) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (0+b) (0+c) (0+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + (t * b^2) + ((4 + t) * b * c) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((-1/2 : ℚ) : ℝ) * t) * c) + ((-1 * t) * d^2) + (t * d * e) + (t * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((1/2 : ℚ) : ℝ) * t) * e) + ((((1/4 : ℚ) : ℝ) * t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_00010 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (0+a) (0+b) (0+c) (1+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (0+b) (0+c) (1+d) (0+e) ∧
    localImaginary t (0+a) (0+b) (0+c) (1+d) (0+e) ≤ 8 := by
  have hr : localReal t (0+a) (0+b) (0+c) (1+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + (2 * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + (t * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-2 + (-2 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((-1 * t) * e) + ((-1 + (-1 * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (0+b) (0+c) (1+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + (t * b^2) + ((4 + t) * b * c) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-4 + (-1 * t)) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-2 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + (t * e) + ((-1 * t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_00011 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (0+a) (0+b) (0+c) (1+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (0+b) (0+c) (1+d) (1+e) ∧
    localImaginary t (0+a) (0+b) (0+c) (1+d) (1+e) ≤ 8 := by
  have hr : localReal t (0+a) (0+b) (0+c) (1+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + (2 * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((1/2 : ℚ) : ℝ) * t) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-2 + (-3 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/2 : ℚ) : ℝ) * t) * e) + ((-1 + (((-7/4 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (0+b) (0+c) (1+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + (t * b^2) + ((4 + t) * b * c) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-4 + (((-3/2 : ℚ) : ℝ) * t)) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-1 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((3/2 : ℚ) : ℝ) * t) * e) + ((((1/4 : ℚ) : ℝ) * t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_00100 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (0+a) (0+b) (1+c) (0+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (0+b) (1+c) (0+d) (0+e) ∧
    localImaginary t (0+a) (0+b) (1+c) (0+d) (0+e) ≤ 8 := by
  have hr : localReal t (0+a) (0+b) (1+c) (0+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + (t * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + t) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + (t * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/2 : ℚ) : ℝ) * t) * e) + ((4 + (((1/2 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (0+b) (1+c) (0+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((1/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((4 + t) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-1 * t) * d^2) + (t * d * e) + ((-4 + (-1 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/2 : ℚ) : ℝ) * t) * e) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_00101 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (0+a) (0+b) (1+c) (0+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (0+b) (1+c) (0+d) (1+e) ∧
    localImaginary t (0+a) (0+b) (1+c) (0+d) (1+e) ≤ 8 := by
  have hr : localReal t (0+a) (0+b) (1+c) (0+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + (t * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + (((1/2 : ℚ) : ℝ) * t)) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((4 + (((1/4 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (0+b) (1+c) (0+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((1/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((4 + t) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((-1/2 : ℚ) : ℝ) * t) * c) + ((-1 * t) * d^2) + (t * d * e) + (-4 * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/4 : ℚ) : ℝ) * t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_00110 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (0+a) (0+b) (1+c) (1+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (0+b) (1+c) (1+d) (0+e) ∧
    localImaginary t (0+a) (0+b) (1+c) (1+d) (0+e) ≤ 8 := by
  have hr : localReal t (0+a) (0+b) (1+c) (1+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((2 + t) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + (2 * t)) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-2 + (-1 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-3/2 : ℚ) : ℝ) * t) * e) + ((3 + (((1/2 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (0+b) (1+c) (1+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((1/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((4 + t) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-4 + (-1 * t)) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-4 + (-3 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((1/2 : ℚ) : ℝ) * t) * e) + ((-4 + (-2 * t))) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_00111 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (0+a) (0+b) (1+c) (1+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (0+b) (1+c) (1+d) (1+e) ∧
    localImaginary t (0+a) (0+b) (1+c) (1+d) (1+e) ≤ 8 := by
  have hr : localReal t (0+a) (0+b) (1+c) (1+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((2 + t) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + (((3/2 : ℚ) : ℝ) * t)) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-2 + (-2 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((-1 * t) * e) + ((3 + (((-3/4 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (0+b) (1+c) (1+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((1/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((4 + t) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-4 + (((-3/2 : ℚ) : ℝ) * t)) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-4 + (-2 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + (t * e) + ((-4 + (((-5/4 : ℚ) : ℝ) * t))) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_01000 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (0+a) (1+b) (0+c) (0+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (1+b) (0+c) (0+d) (0+e) ∧
    localImaginary t (0+a) (1+b) (0+c) (0+d) (0+e) ≤ 8 := by
  have hr : localReal t (0+a) (1+b) (0+c) (0+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-2 + (-2 * t)) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + (t * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + (2 * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((-1 + (-1 * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (1+b) (0+c) (0+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((2 * t) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((4 + t) * c) + ((-1 * t) * d^2) + (t * d * e) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + (t) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_01001 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (0+a) (1+b) (0+c) (0+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (1+b) (0+c) (0+d) (1+e) ∧
    localImaginary t (0+a) (1+b) (0+c) (0+d) (1+e) ≤ 8 := by
  have hr : localReal t (0+a) (1+b) (0+c) (0+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-2 + (-2 * t)) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((1/2 : ℚ) : ℝ) * t) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((2 + (-1 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((1/2 : ℚ) : ℝ) * t) * e) + ((-1 + (((-3/4 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (1+b) (0+c) (0+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((2 * t) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c) + ((-1 * t) * d^2) + (t * d * e) + (t * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((1/2 : ℚ) : ℝ) * t) * e) + ((((5/4 : ℚ) : ℝ) * t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_01010 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (0+a) (1+b) (0+c) (1+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (1+b) (0+c) (1+d) (0+e) ∧
    localImaginary t (0+a) (1+b) (0+c) (1+d) (0+e) ≤ 8 := by
  have hr : localReal t (0+a) (1+b) (0+c) (1+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-2 * t) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((2 * t) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-2 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((-1 * t) * e) + ((-2 * t)) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (1+b) (0+c) (1+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((2 * t) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-1 * t) * d^2) + (t * d * e) + ((-2 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + (t * e) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_01011 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (0+a) (1+b) (0+c) (1+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (1+b) (0+c) (1+d) (1+e) ∧
    localImaginary t (0+a) (1+b) (0+c) (1+d) (1+e) ≤ 8 := by
  have hr : localReal t (0+a) (1+b) (0+c) (1+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-2 * t) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((3/2 : ℚ) : ℝ) * t) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-3 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/2 : ℚ) : ℝ) * t) * e) + ((((-11/4 : ℚ) : ℝ) * t)) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (1+b) (0+c) (1+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((2 * t) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((-1/2 : ℚ) : ℝ) * t) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-1 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((3/2 : ℚ) : ℝ) * t) * e) + ((((5/4 : ℚ) : ℝ) * t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_01100 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (0+a) (1+b) (1+c) (0+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (1+b) (1+c) (0+d) (0+e) ∧
    localImaginary t (0+a) (1+b) (1+c) (0+d) (0+e) ≤ 8 ∧
    5.27 ≤ localImaginary t (0+a) (1+b) (1+c) (0+d) (0+e) := by
  have hr : localReal t (0+a) (1+b) (1+c) (0+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((-3/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-2 + (-1 * t)) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + (2 * t)) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((2 + t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/2 : ℚ) : ℝ) * t) * e) + ((3 + (((1/2 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (1+b) (1+c) (0+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((4 + (3 * t)) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((4 + t) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-4 + (-1 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/2 : ℚ) : ℝ) * t) * e) + ((4 + (2 * t))) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_01101 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (0+a) (1+b) (1+c) (0+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (1+b) (1+c) (0+d) (1+e) ∧
    localImaginary t (0+a) (1+b) (1+c) (0+d) (1+e) ≤ 8 ∧
    5.27 ≤ localImaginary t (0+a) (1+b) (1+c) (0+d) (1+e) := by
  have hr : localReal t (0+a) (1+b) (1+c) (0+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((-3/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-2 + (-1 * t)) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + (((3/2 : ℚ) : ℝ) * t)) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + (2 * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((3 + (((1/4 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (1+b) (1+c) (0+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((4 + (3 * t)) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c) + ((-1 * t) * d^2) + (t * d * e) + (-4 * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((4 + (((7/4 : ℚ) : ℝ) * t))) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_01110 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (0+a) (1+b) (1+c) (1+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (1+b) (1+c) (1+d) (0+e) ∧
    localImaginary t (0+a) (1+b) (1+c) (1+d) (0+e) ≤ 8 := by
  have hr : localReal t (0+a) (1+b) (1+c) (1+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((-3/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-1 * t) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + (3 * t)) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-1 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-3/2 : ℚ) : ℝ) * t) * e) + ((4 + (((1/2 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (1+b) (1+c) (1+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((4 + (3 * t)) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-1 * t) * d^2) + (t * d * e) + ((-4 + (-3 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((1/2 : ℚ) : ℝ) * t) * e) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_01111 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc 0 0)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (0+a) (1+b) (1+c) (1+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (0+a) (1+b) (1+c) (1+d) (1+e) ∧
    localImaginary t (0+a) (1+b) (1+c) (1+d) (1+e) ≤ 8 := by
  have hr : localReal t (0+a) (1+b) (1+c) (1+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((-3/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-1 * t) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + (((5/2 : ℚ) : ℝ) * t)) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-2 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((-1 * t) * e) + ((4 + (((-3/4 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (0+a) (1+b) (1+c) (1+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((4 + (3 * t)) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((-1/2 : ℚ) : ℝ) * t) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-4 + (-2 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + (t * e) + ((((3/4 : ℚ) : ℝ) * t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_10000 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (1+a) (0+b) (0+c) (0+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (0+b) (0+c) (0+d) (0+e) ∧
    localImaginary t (1+a) (0+b) (0+c) (0+d) (0+e) ≤ 8 := by
  have hr : localReal t (1+a) (0+b) (0+c) (0+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((1/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-1 * t) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((-1/2 : ℚ) : ℝ) * t) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((1/4 : ℚ) : ℝ) * t)) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (0+b) (0+c) (0+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((-1 * t) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((1/2 : ℚ) : ℝ) * t) * c) + ((-1 * t) * d^2) + (t * d * e) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/4 : ℚ) : ℝ) * t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_10001 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (1+a) (0+b) (0+c) (0+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (0+b) (0+c) (0+d) (1+e) ∧
    localImaginary t (1+a) (0+b) (0+c) (0+d) (1+e) ≤ 8 := by
  have hr : localReal t (1+a) (0+b) (0+c) (0+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((1/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-1 * t) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-1 * t) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-1 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((1/2 : ℚ) : ℝ) * t) * e) + ((((1/2 : ℚ) : ℝ) * t)) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (0+b) (0+c) (0+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((-1 * t) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-1 * t) * d^2) + (t * d * e) + (t * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((1/2 : ℚ) : ℝ) * t) * e) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_10010 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (1+a) (0+b) (0+c) (1+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (0+b) (0+c) (1+d) (0+e) ∧
    localImaginary t (1+a) (0+b) (0+c) (1+d) (0+e) ≤ 8 := by
  have hr : localReal t (1+a) (0+b) (0+c) (1+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((1/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((2 + (-1 * t)) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((1/2 : ℚ) : ℝ) * t) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-2 + (-2 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((-1 * t) * e) + ((-1 + (((-3/4 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (0+b) (0+c) (1+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((-1 * t) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-4 + (((-1/2 : ℚ) : ℝ) * t)) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-2 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + (t * e) + ((((-5/4 : ℚ) : ℝ) * t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_10011 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (1+a) (0+b) (0+c) (1+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (0+b) (0+c) (1+d) (1+e) ∧
    localImaginary t (1+a) (0+b) (0+c) (1+d) (1+e) ≤ 8 := by
  have hr : localReal t (1+a) (0+b) (0+c) (1+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((1/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((2 + (-1 * t)) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-2 + (-3 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/2 : ℚ) : ℝ) * t) * e) + ((-1 + (((-3/2 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (0+b) (0+c) (1+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((-1 * t) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-4 + (-1 * t)) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-1 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((3/2 : ℚ) : ℝ) * t) * e) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_10100 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (1+a) (0+b) (1+c) (0+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (0+b) (1+c) (0+d) (0+e) ∧
    localImaginary t (1+a) (0+b) (1+c) (0+d) (0+e) ≤ 8 := by
  have hr : localReal t (1+a) (0+b) (1+c) (0+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + (((1/2 : ℚ) : ℝ) * t)) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + (t * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/2 : ℚ) : ℝ) * t) * e) + ((4 + (((1/4 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (0+b) (1+c) (0+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + (t * b^2) + ((4 + t) * b * c) + (4 * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((1/2 : ℚ) : ℝ) * t) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-4 + (-1 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/2 : ℚ) : ℝ) * t) * e) + ((((1/4 : ℚ) : ℝ) * t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_10101 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (1+a) (0+b) (1+c) (0+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (0+b) (1+c) (0+d) (1+e) ∧
    localImaginary t (1+a) (0+b) (1+c) (0+d) (1+e) ≤ 8 := by
  have hr : localReal t (1+a) (0+b) (1+c) (0+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + (8 * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + (4) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (0+b) (1+c) (0+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + (t * b^2) + ((4 + t) * b * c) + (4 * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-1 * t) * d^2) + (t * d * e) + (-4 * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_10110 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (1+a) (0+b) (1+c) (1+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (0+b) (1+c) (1+d) (0+e) ∧
    localImaginary t (1+a) (0+b) (1+c) (1+d) (0+e) ≤ 8 := by
  have hr : localReal t (1+a) (0+b) (1+c) (1+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + (2 * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + (((3/2 : ℚ) : ℝ) * t)) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-2 + (-1 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-3/2 : ℚ) : ℝ) * t) * e) + ((3 + (((1/4 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (0+b) (1+c) (1+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + (t * b^2) + ((4 + t) * b * c) + (4 * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-4 + (((-1/2 : ℚ) : ℝ) * t)) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-4 + (-3 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((1/2 : ℚ) : ℝ) * t) * e) + ((-4 + (((-7/4 : ℚ) : ℝ) * t))) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_10111 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc 0 0)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (1+a) (0+b) (1+c) (1+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (0+b) (1+c) (1+d) (1+e) ∧
    localImaginary t (1+a) (0+b) (1+c) (1+d) (1+e) ≤ 8 := by
  have hr : localReal t (1+a) (0+b) (1+c) (1+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + (2 * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + t) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-2 + (-2 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((-1 * t) * e) + ((3 + (-1 * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (0+b) (1+c) (1+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + (t * b^2) + ((4 + t) * b * c) + (4 * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-4 + (-1 * t)) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-4 + (-2 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + (t * e) + ((-4 + (-1 * t))) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_11000 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (1+a) (1+b) (0+c) (0+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (1+b) (0+c) (0+d) (0+e) ∧
    localImaginary t (1+a) (1+b) (0+c) (0+d) (0+e) ≤ 8 := by
  have hr : localReal t (1+a) (1+b) (0+c) (0+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-2 + (-3 * t)) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((1/2 : ℚ) : ℝ) * t) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + (2 * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((-1 + (((-7/4 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (1+b) (0+c) (0+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((-3/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + (t * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((4 + (((3/2 : ℚ) : ℝ) * t)) * c) + ((-1 * t) * d^2) + (t * d * e) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/4 : ℚ) : ℝ) * t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_11001 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (1+a) (1+b) (0+c) (0+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (1+b) (0+c) (0+d) (1+e) ∧
    localImaginary t (1+a) (1+b) (0+c) (0+d) (1+e) ≤ 8 := by
  have hr : localReal t (1+a) (1+b) (0+c) (0+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-2 + (-3 * t)) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((2 + (-1 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((1/2 : ℚ) : ℝ) * t) * e) + ((-1 + (((-3/2 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (1+b) (0+c) (0+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((-3/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + (t * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((4 + t) * c) + ((-1 * t) * d^2) + (t * d * e) + (t * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((1/2 : ℚ) : ℝ) * t) * e) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_11010 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (1+a) (1+b) (0+c) (1+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (1+b) (0+c) (1+d) (0+e) ∧
    localImaginary t (1+a) (1+b) (0+c) (1+d) (0+e) ≤ 8 := by
  have hr : localReal t (1+a) (1+b) (0+c) (1+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-3 * t) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((3/2 : ℚ) : ℝ) * t) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-2 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((-1 * t) * e) + ((((-11/4 : ℚ) : ℝ) * t)) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (1+b) (0+c) (1+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((-3/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + (t * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((1/2 : ℚ) : ℝ) * t) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-2 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + (t * e) + ((((-5/4 : ℚ) : ℝ) * t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_11011 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc 0 0)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (1+a) (1+b) (0+c) (1+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (1+b) (0+c) (1+d) (1+e) ∧
    localImaginary t (1+a) (1+b) (0+c) (1+d) (1+e) ≤ 8 := by
  have hr : localReal t (1+a) (1+b) (0+c) (1+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((((-1/2 : ℚ) : ℝ) * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-3 * t) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + (t * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-3 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/2 : ℚ) : ℝ) * t) * e) + ((((-7/2 : ℚ) : ℝ) * t)) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (1+b) (0+c) (1+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((((-3/2 : ℚ) : ℝ) * t) * a) + (t * b^2) + ((4 + t) * b * c) + (t * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-1 * t) * d^2) + (t * d * e) + ((-1 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((3/2 : ℚ) : ℝ) * t) * e) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_11100 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (1+a) (1+b) (1+c) (0+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (1+b) (1+c) (0+d) (0+e) ∧
    localImaginary t (1+a) (1+b) (1+c) (0+d) (0+e) ≤ 8 ∧
    5.27 ≤ localImaginary t (1+a) (1+b) (1+c) (0+d) (0+e) := by
  have hr : localReal t (1+a) (1+b) (1+c) (0+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-2 + (-2 * t)) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + (((3/2 : ℚ) : ℝ) * t)) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((2 + t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/2 : ℚ) : ℝ) * t) * e) + ((3 + (((-3/4 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (1+b) (1+c) (0+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((4 + (2 * t)) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((4 + (((3/2 : ℚ) : ℝ) * t)) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-4 + (-1 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-1/2 : ℚ) : ℝ) * t) * e) + ((4 + (((5/4 : ℚ) : ℝ) * t))) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_11101 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc 0 0)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (1+a) (1+b) (1+c) (0+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (1+b) (1+c) (0+d) (1+e) ∧
    localImaginary t (1+a) (1+b) (1+c) (0+d) (1+e) ≤ 8 ∧
    5.27 ≤ localImaginary t (1+a) (1+b) (1+c) (0+d) (1+e) := by
  have hr : localReal t (1+a) (1+b) (1+c) (0+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-2 + (-2 * t)) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + t) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + (2 * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((3 + (-1 * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (1+b) (1+c) (0+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((4 + (2 * t)) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((4 + t) * c) + ((-1 * t) * d^2) + (t * d * e) + (-4 * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((4 + t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_11110 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc 0 0) :
    localReal t (1+a) (1+b) (1+c) (1+d) (0+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (1+b) (1+c) (1+d) (0+e) ∧
    localImaginary t (1+a) (1+b) (1+c) (1+d) (0+e) ≤ 8 := by
  have hr : localReal t (1+a) (1+b) (1+c) (1+d) (0+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-2 * t) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + (((5/2 : ℚ) : ℝ) * t)) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-1 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((-3/2 : ℚ) : ℝ) * t) * e) + ((4 + (((-3/4 : ℚ) : ℝ) * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (1+b) (1+c) (1+d) (0+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((4 + (2 * t)) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((((1/2 : ℚ) : ℝ) * t) * c) + ((-1 * t) * d^2) + (t * d * e) + ((-4 + (-3 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((((1/2 : ℚ) : ℝ) * t) * e) + ((((-3/4 : ℚ) : ℝ) * t)) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

theorem local_box_11111 (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : a ∈ Set.Icc (-0.01) 0.01)
    (hb : b ∈ Set.Icc (-0.01) 0.01)
    (hc : c ∈ Set.Icc (-0.01) 0.01)
    (hd : d ∈ Set.Icc (-0.01) 0.01)
    (he : e ∈ Set.Icc (-0.01) 0.01) :
    localReal t (1+a) (1+b) (1+c) (1+d) (1+e) ≤ 4.86 ∧
    -8 ≤ localImaginary t (1+a) (1+b) (1+c) (1+d) (1+e) ∧
    localImaginary t (1+a) (1+b) (1+c) (1+d) (1+e) ≤ 8 := by
  have hr : localReal t (1+a) (1+b) (1+c) (1+d) (1+e) = ((((1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((-1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + ((-1 + (-1 * t)) * b^2) + (t * b * c) + (2 * b * d) + ((-2 * t) * b) + ((4 + (((1/2 : ℚ) : ℝ) * t)) * c^2) + (t * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((8 + (2 * t)) * c) + ((-1 + (-1 * t)) * d^2) + ((-1 * t) * d * e) + ((-2 * t) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + ((-1 * t) * e) + ((4 + (-2 * t))) := by unfold localReal; norm_num; ring
  have hj : localImaginary t (1+a) (1+b) (1+c) (1+d) (1+e) = ((((-1/4 : ℚ) : ℝ) * t) * a^2) + ((-1 * t) * a * b) + ((((1/2 : ℚ) : ℝ) * t) * a * c) + ((-1 * t) * a) + (t * b^2) + ((4 + t) * b * c) + ((4 + (2 * t)) * b) + ((-4 + (-1 * t)) * c * d) + ((((-1/2 : ℚ) : ℝ) * t) * c * e) + ((-1 * t) * d^2) + (t * d * e) + ((-4 + (-2 * t)) * d) + ((((1/4 : ℚ) : ℝ) * t) * e^2) + (t * e) := by unfold localImaginary; norm_num; ring
  rw [hr, hj]
  simp only [pow_two]
  constructor
  · dyadic_interval +kernel [prec := 24]
  constructor
  · dyadic_interval +kernel [prec := 24]
  · dyadic_interval +kernel [prec := 24]

end ChowlaCosine
