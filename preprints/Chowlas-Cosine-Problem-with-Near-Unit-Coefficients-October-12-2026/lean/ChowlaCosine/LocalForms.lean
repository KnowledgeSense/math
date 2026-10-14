import ChowlaCosine.LocalBoxes
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith

namespace ChowlaCosine

theorem one_add_sub_one (x : ℝ) : 1 + (x - 1) = x := by ring

def AdmissibleValue (x : ℝ) : Prop := x = 0 ∨ x ∈ Set.Icc 0.99 1.01

def Admissible (z : Fin 5 → ℝ) : Prop := ∀ i, AdmissibleValue (z i)

noncomputable def R (z : Fin 5 → ℝ) : ℝ :=
  localReal (Real.sqrt 2) (z 0) (z 1) (z 2) (z 3) (z 4)

noncomputable def J (z : Fin 5 → ℝ) : ℝ :=
  localImaginary (Real.sqrt 2) (z 0) (z 1) (z 2) (z 3) (z 4)

theorem sqrt_two_bounds : Real.sqrt 2 ∈ Set.Icc 1.414213 1.414214 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2:ℝ)
  constructor <;> nlinarith

theorem scalar_local_bounds (t a b c d e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : AdmissibleValue a) (hb : AdmissibleValue b) (hc : AdmissibleValue c)
    (hd : AdmissibleValue d) (he : AdmissibleValue e) :
    localReal t a b c d e ≤ 4.86 ∧
      -8 ≤ localImaginary t a b c d e ∧ localImaginary t a b c d e ≤ 8 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;>
    rcases hc with hc | hc <;> rcases hd with hd | hd <;> rcases he with he | he
  · subst a b c d e
    have hx := local_box_00000 t 0 0 0 0 0 ht (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a b c d
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_00001 t 0 0 0 0 (e-1) ht (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num) he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a b c e
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have hx := local_box_00010 t 0 0 0 (d-1) 0 ht (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num) hd' (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a b c
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_00011 t 0 0 0 (d-1) (e-1) ht (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num) hd' he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a b d e
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have hx := local_box_00100 t 0 0 (c-1) 0 0 ht (by constructor <;> norm_num) (by constructor <;> norm_num) hc' (by constructor <;> norm_num) (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a b d
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_00101 t 0 0 (c-1) 0 (e-1) ht (by constructor <;> norm_num) (by constructor <;> norm_num) hc' (by constructor <;> norm_num) he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a b e
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have hx := local_box_00110 t 0 0 (c-1) (d-1) 0 ht (by constructor <;> norm_num) (by constructor <;> norm_num) hc' hd' (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a b
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_00111 t 0 0 (c-1) (d-1) (e-1) ht (by constructor <;> norm_num) (by constructor <;> norm_num) hc' hd' he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a c d e
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hx := local_box_01000 t 0 (b-1) 0 0 0 ht (by constructor <;> norm_num) hb' (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a c d
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_01001 t 0 (b-1) 0 0 (e-1) ht (by constructor <;> norm_num) hb' (by constructor <;> norm_num) (by constructor <;> norm_num) he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a c e
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have hx := local_box_01010 t 0 (b-1) 0 (d-1) 0 ht (by constructor <;> norm_num) hb' (by constructor <;> norm_num) hd' (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a c
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_01011 t 0 (b-1) 0 (d-1) (e-1) ht (by constructor <;> norm_num) hb' (by constructor <;> norm_num) hd' he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a d e
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have hx := local_box_01100 t 0 (b-1) (c-1) 0 0 ht (by constructor <;> norm_num) hb' hc' (by constructor <;> norm_num) (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2.1)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a d
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_01101 t 0 (b-1) (c-1) 0 (e-1) ht (by constructor <;> norm_num) hb' hc' (by constructor <;> norm_num) he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2.1)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a e
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have hx := local_box_01110 t 0 (b-1) (c-1) (d-1) 0 ht (by constructor <;> norm_num) hb' hc' hd' (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst a
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_01111 t 0 (b-1) (c-1) (d-1) (e-1) ht (by constructor <;> norm_num) hb' hc' hd' he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst b c d e
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hx := local_box_10000 t (a-1) 0 0 0 0 ht ha' (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst b c d
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_10001 t (a-1) 0 0 0 (e-1) ht ha' (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num) he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst b c e
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have hx := local_box_10010 t (a-1) 0 0 (d-1) 0 ht ha' (by constructor <;> norm_num) (by constructor <;> norm_num) hd' (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst b c
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_10011 t (a-1) 0 0 (d-1) (e-1) ht ha' (by constructor <;> norm_num) (by constructor <;> norm_num) hd' he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst b d e
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have hx := local_box_10100 t (a-1) 0 (c-1) 0 0 ht ha' (by constructor <;> norm_num) hc' (by constructor <;> norm_num) (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst b d
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_10101 t (a-1) 0 (c-1) 0 (e-1) ht ha' (by constructor <;> norm_num) hc' (by constructor <;> norm_num) he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst b e
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have hx := local_box_10110 t (a-1) 0 (c-1) (d-1) 0 ht ha' (by constructor <;> norm_num) hc' hd' (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst b
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_10111 t (a-1) 0 (c-1) (d-1) (e-1) ht ha' (by constructor <;> norm_num) hc' hd' he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst c d e
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hx := local_box_11000 t (a-1) (b-1) 0 0 0 ht ha' hb' (by constructor <;> norm_num) (by constructor <;> norm_num) (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst c d
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_11001 t (a-1) (b-1) 0 0 (e-1) ht ha' hb' (by constructor <;> norm_num) (by constructor <;> norm_num) he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst c e
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have hx := local_box_11010 t (a-1) (b-1) 0 (d-1) 0 ht ha' hb' (by constructor <;> norm_num) hd' (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst c
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_11011 t (a-1) (b-1) 0 (d-1) (e-1) ht ha' hb' (by constructor <;> norm_num) hd' he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst d e
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have hx := local_box_11100 t (a-1) (b-1) (c-1) 0 0 ht ha' hb' hc' (by constructor <;> norm_num) (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2.1)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst d
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_11101 t (a-1) (b-1) (c-1) 0 (e-1) ht ha' hb' hc' (by constructor <;> norm_num) he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2.1)
    simpa only [zero_add, one_add_sub_one] using hy
  · subst e
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have hx := local_box_11110 t (a-1) (b-1) (c-1) (d-1) 0 ht ha' hb' hc' hd' (by constructor <;> norm_num)
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy
  · have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [ha.1, ha.2]
    have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hb.1, hb.2]
    have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hc.1, hc.2]
    have hd' : d-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [hd.1, hd.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by
      constructor <;> linarith [he.1, he.2]
    have hx := local_box_11111 t (a-1) (b-1) (c-1) (d-1) (e-1) ht ha' hb' hc' hd' he'
    have hy := And.intro hx.1 (And.intro hx.2.1 hx.2.2)
    simpa only [zero_add, one_add_sub_one] using hy

theorem R_le (z : Fin 5 → ℝ) (hz : Admissible z) : R z ≤ 243/50 := by
  simpa only [R, show (4.86 : ℝ) = 243/50 by norm_num] using (scalar_local_bounds (Real.sqrt 2) (z 0) (z 1) (z 2) (z 3) (z 4)
    sqrt_two_bounds (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)).1

theorem abs_J_le (z : Fin 5 → ℝ) (hz : Admissible z) : |J z| ≤ 8 := by
  exact abs_le.mpr (scalar_local_bounds (Real.sqrt 2) (z 0) (z 1) (z 2) (z 3) (z 4)
    sqrt_two_bounds (hz 0) (hz 1) (hz 2) (hz 3) (hz 4)).2

theorem scalar_boundary_lower (t a b c e : ℝ)
    (ht : t ∈ Set.Icc 1.414213 1.414214)
    (ha : AdmissibleValue a) (hb : b ∈ Set.Icc 0.99 1.01)
    (hc : c ∈ Set.Icc 0.99 1.01) (he : AdmissibleValue e) :
    5.27 ≤ localImaginary t a b c 0 e := by
  have hb' : b-1 ∈ Set.Icc (-0.01) 0.01 := by constructor <;> linarith [hb.1,hb.2]
  have hc' : c-1 ∈ Set.Icc (-0.01) 0.01 := by constructor <;> linarith [hc.1,hc.2]
  rcases ha with ha | ha <;> rcases he with he | he
  · subst a e
    have hx := (local_box_01100 t 0 (b-1) (c-1) 0 0 ht (by constructor <;> norm_num) hb' hc' (by constructor <;> norm_num) (by constructor <;> norm_num)).2.2.2
    simpa only [zero_add, one_add_sub_one] using hx
  · subst a
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by constructor <;> linarith [he.1,he.2]
    have hx := (local_box_01101 t 0 (b-1) (c-1) 0 (e-1) ht (by constructor <;> norm_num) hb' hc' (by constructor <;> norm_num) he').2.2.2
    simpa only [zero_add, one_add_sub_one] using hx
  · subst e
    have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by constructor <;> linarith [ha.1,ha.2]
    have hx := (local_box_11100 t (a-1) (b-1) (c-1) 0 0 ht ha' hb' hc' (by constructor <;> norm_num) (by constructor <;> norm_num)).2.2.2
    simpa only [zero_add, one_add_sub_one] using hx
  · have ha' : a-1 ∈ Set.Icc (-0.01) 0.01 := by constructor <;> linarith [ha.1,ha.2]
    have he' : e-1 ∈ Set.Icc (-0.01) 0.01 := by constructor <;> linarith [he.1,he.2]
    have hx := (local_box_11101 t (a-1) (b-1) (c-1) 0 (e-1) ht ha' hb' hc' (by constructor <;> norm_num) he').2.2.2
    simpa only [zero_add, one_add_sub_one] using hx

theorem J_boundary_ge (z : Fin 5 → ℝ) (hz : Admissible z)
    (h1 : 99/100 ≤ z 1) (h2 : 99/100 ≤ z 2) (h3 : z 3 = 0) :
    527/100 ≤ J z := by
  have hb : z 1 ∈ Set.Icc 0.99 1.01 := by
    rcases hz 1 with h | h
    · rw [h] at h1
      norm_num at h1
    · exact h
  have hc : z 2 ∈ Set.Icc 0.99 1.01 := by
    rcases hz 2 with h | h
    · rw [h] at h2
      norm_num at h2
    · exact h
  unfold J
  rw [h3]
  simpa only [show (5.27 : ℝ) = 527/100 by norm_num] using
    scalar_boundary_lower _ _ _ _ _ sqrt_two_bounds (hz 0) hb hc (hz 4)

end ChowlaCosine
