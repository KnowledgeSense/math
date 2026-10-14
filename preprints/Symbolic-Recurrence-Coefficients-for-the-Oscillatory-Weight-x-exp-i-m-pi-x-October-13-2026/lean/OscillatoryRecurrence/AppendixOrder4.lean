import OscillatoryRecurrence.AppendixPolynomials

noncomputable section
open Polynomial
open scoped Matrix BigOperators
namespace OscillatoryRecurrence
set_option maxHeartbeats 2000000

theorem sample_H_4_0 :
    (polynomialHankel 4).eval (0)=55296 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 4) (Fin 4) ℚ := !![1, 0, 0, 0;
    2, 1, 0, 0;
    6, 6, 1, 0;
    24, 36, 12, 1]
  let U : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 12, 48;
    0, 4, 24, 144;
    0, 0, 24, 288;
    0, 0, 0, 288]
  let A : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 12, 48;
    4, 12, 48, 240;
    12, 48, 240, 1440;
    48, 240, 1440, 10080]
  have hm0 : (endpointMoment 0).eval (0)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (0)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (0)=12 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (0)=48 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (0)=240 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (0)=1440 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (0)=10080 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have he : (Matrix.of (fun i j : Fin 4 =>
      (endpointMoment (i.val+j.val)).eval (0)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_4_1 :
    (polynomialHankel 4).eval (-1)=414720 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 4) (Fin 4) ℚ := !![1, 0, 0, 0;
    2, 1, 0, 0;
    7, (14/3), 1, 0;
    28, (85/3), (19/2), 1]
  let U : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 14, 56;
    0, 6, 28, 170;
    0, 0, (160/3), (1520/3);
    0, 0, 0, 648]
  let A : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 14, 56;
    4, 14, 56, 282;
    14, 56, 282, 1692;
    56, 282, 1692, 11846]
  have hm0 : (endpointMoment 0).eval (-1)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-1)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-1)=14 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-1)=56 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-1)=282 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-1)=1692 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-1)=11846 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have he : (Matrix.of (fun i j : Fin 4 =>
      (endpointMoment (i.val+j.val)).eval (-1)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_4_2 :
    (polynomialHankel 4).eval (-2)=883712 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 4) (Fin 4) ℚ := !![1, 0, 0, 0;
    2, 1, 0, 0;
    8, 4, 1, 0;
    32, 25, (82/9), 1]
  let U : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 16, 64;
    0, 8, 32, 200;
    0, 0, 72, 656;
    0, 0, 0, (6904/9)]
  let A : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 16, 64;
    4, 16, 64, 328;
    16, 64, 328, 1968;
    64, 328, 1968, 13792]
  have hm0 : (endpointMoment 0).eval (-2)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-2)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-2)=16 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-2)=64 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-2)=328 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-2)=1968 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-2)=13792 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have he : (Matrix.of (fun i j : Fin 4 =>
      (endpointMoment (i.val+j.val)).eval (-2)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_4_3 :
    (polynomialHankel 4).eval (-3)=1492992 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 4) (Fin 4) ℚ := !![1, 0, 0, 0;
    2, 1, 0, 0;
    9, (18/5), 1, 0;
    36, (117/5), 9, 1]
  let U : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 18, 72;
    0, 10, 36, 234;
    0, 0, (432/5), (3888/5);
    0, 0, 0, 864]
  let A : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 18, 72;
    4, 18, 72, 378;
    18, 72, 378, 2268;
    72, 378, 2268, 15930]
  have hm0 : (endpointMoment 0).eval (-3)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-3)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-3)=18 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-3)=72 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-3)=378 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-3)=2268 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-3)=15930 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have he : (Matrix.of (fun i j : Fin 4 =>
      (endpointMoment (i.val+j.val)).eval (-3)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_4_4 :
    (polynomialHankel 4).eval (-4)=2279424 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 4) (Fin 4) ℚ := !![1, 0, 0, 0;
    2, 1, 0, 0;
    10, (10/3), 1, 0;
    40, (68/3), (332/37), 1]
  let U : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 20, 80;
    0, 12, 40, 272;
    0, 0, (296/3), (2656/3);
    0, 0, 0, (35616/37)]
  let A : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 20, 80;
    4, 20, 80, 432;
    20, 80, 432, 2592;
    80, 432, 2592, 18272]
  have hm0 : (endpointMoment 0).eval (-4)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-4)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-4)=20 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-4)=80 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-4)=432 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-4)=2592 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-4)=18272 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have he : (Matrix.of (fun i j : Fin 4 =>
      (endpointMoment (i.val+j.val)).eval (-4)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_4_0 :
    (polynomialBorder 4).eval (0)=1105920 := by
  rw [polynomialBorder_eval 4 (by norm_num)]
  let L : Matrix (Fin 4) (Fin 4) ℚ := !![1, 0, 0, 0;
    2, 1, 0, 0;
    6, 6, 1, 0;
    24, 36, 12, 1]
  let U : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 12, 240;
    0, 4, 24, 960;
    0, 0, 24, 2880;
    0, 0, 0, 5760]
  let A : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 12, 240;
    4, 12, 48, 1440;
    12, 48, 240, 10080;
    48, 240, 1440, 80640]
  have hm0 : (endpointMoment 0).eval (0)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (0)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (0)=12 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (0)=48 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (0)=240 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (0)=1440 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (0)=10080 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (0)=80640 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have he : (Matrix.of (fun i j : Fin 4 =>
      (endpointMoment (i.val+borderColumn 4 j)).eval (0)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_4_1 :
    (polynomialBorder 4).eval (-1)=7127040 := by
  rw [polynomialBorder_eval 4 (by norm_num)]
  let L : Matrix (Fin 4) (Fin 4) ℚ := !![1, 0, 0, 0;
    2, 1, 0, 0;
    7, (14/3), 1, 0;
    28, (85/3), (19/2), 1]
  let U : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 14, 282;
    0, 6, 28, 1128;
    0, 0, (160/3), 4608;
    0, 0, 0, 11136]
  let A : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 14, 282;
    4, 14, 56, 1692;
    14, 56, 282, 11846;
    56, 282, 1692, 94768]
  have hm0 : (endpointMoment 0).eval (-1)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-1)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-1)=14 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-1)=56 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-1)=282 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-1)=1692 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-1)=11846 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-1)=94768 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have he : (Matrix.of (fun i j : Fin 4 =>
      (endpointMoment (i.val+borderColumn 4 j)).eval (-1)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_4_2 :
    (polynomialBorder 4).eval (-2)=15093760 := by
  rw [polynomialBorder_eval 4 (by norm_num)]
  let L : Matrix (Fin 4) (Fin 4) ℚ := !![1, 0, 0, 0;
    2, 1, 0, 0;
    8, 4, 1, 0;
    32, 25, (82/9), 1]
  let U : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 16, 328;
    0, 8, 32, 1312;
    0, 0, 72, 5920;
    0, 0, 0, (117920/9)]
  let A : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 16, 328;
    4, 16, 64, 1968;
    16, 64, 328, 13792;
    64, 328, 1968, 110336]
  have hm0 : (endpointMoment 0).eval (-2)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-2)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-2)=16 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-2)=64 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-2)=328 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-2)=1968 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-2)=13792 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-2)=110336 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have he : (Matrix.of (fun i j : Fin 4 =>
      (endpointMoment (i.val+borderColumn 4 j)).eval (-2)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_4_3 :
    (polynomialBorder 4).eval (-3)=25380864 := by
  rw [polynomialBorder_eval 4 (by norm_num)]
  let L : Matrix (Fin 4) (Fin 4) ℚ := !![1, 0, 0, 0;
    2, 1, 0, 0;
    9, (18/5), 1, 0;
    36, (117/5), 9, 1]
  let U : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 18, 378;
    0, 10, 36, 1512;
    0, 0, (432/5), (35424/5);
    0, 0, 0, 14688]
  let A : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 18, 378;
    4, 18, 72, 2268;
    18, 72, 378, 15930;
    72, 378, 2268, 127440]
  have hm0 : (endpointMoment 0).eval (-3)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-3)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-3)=18 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-3)=72 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-3)=378 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-3)=2268 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-3)=15930 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-3)=127440 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have he : (Matrix.of (fun i j : Fin 4 =>
      (endpointMoment (i.val+borderColumn 4 j)).eval (-3)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_4_4 :
    (polynomialBorder 4).eval (-4)=38412288 := by
  rw [polynomialBorder_eval 4 (by norm_num)]
  let L : Matrix (Fin 4) (Fin 4) ℚ := !![1, 0, 0, 0;
    2, 1, 0, 0;
    10, (10/3), 1, 0;
    40, (68/3), (332/37), 1]
  let U : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 20, 432;
    0, 12, 40, 1728;
    0, 0, (296/3), 8192;
    0, 0, 0, (600192/37)]
  let A : Matrix (Fin 4) (Fin 4) ℚ := !![2, 4, 20, 432;
    4, 20, 80, 2592;
    20, 80, 432, 18272;
    80, 432, 2592, 146176]
  have hm0 : (endpointMoment 0).eval (-4)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-4)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-4)=20 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-4)=80 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-4)=432 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-4)=2592 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-4)=18272 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-4)=146176 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have he : (Matrix.of (fun i j : Fin 4 =>
      (endpointMoment (i.val+borderColumn 4 j)).eval (-4)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem table_H_4 : polynomialHankel 4=C (256)*appendixG4 := by
  apply eq_of_natDegree_lt_card_of_eval_eq (f:=fun i : Fin 5 => -(i.val:ℚ))
  · intro i j h
    apply Fin.ext
    exact_mod_cast neg_inj.mp h
  · intro i
    fin_cases i <;>
      norm_num [sample_H_4_0,sample_H_4_1,sample_H_4_2,sample_H_4_3,sample_H_4_4,appendixG4]
  · apply max_lt
    · rw [polynomialHankel_natDegree]
      norm_num [hankelDegree]
    · unfold appendixG4
      compute_degree!

theorem table_J_4 : polynomialBorder 4=C (5120)*appendixG4-X*(C (3072)*appendixG3) := by
  apply eq_of_natDegree_lt_card_of_eval_eq (f:=fun i : Fin 5 => -(i.val:ℚ))
  · intro i j h
    apply Fin.ext
    exact_mod_cast neg_inj.mp h
  · intro i
    fin_cases i <;>
      norm_num [sample_J_4_0,sample_J_4_1,sample_J_4_2,sample_J_4_3,sample_J_4_4,appendixG4,appendixG3]
  · apply max_lt
    · rw [polynomialBorder_natDegree 4 (by norm_num)]
      norm_num [hankelDegree]
    · unfold appendixG4 appendixG3
      compute_degree!

theorem recurrenceFamily_appendix_4 : recurrenceFamily 4=appendixG4 := by
  have h := recurrenceFamily_hankel_eq (n:=4) (by norm_num) appendixG4
    (256) (by norm_num) appendixG4_monic table_H_4
  simpa only [hankelDegree,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceMul] using h

theorem recurrenceFamily_appendix_3 : recurrenceFamily 3=appendixG3 := by
  have h := recurrenceFamily_numerator_eq (n:=4) (by norm_num) appendixG3
    (3072) (by norm_num) appendixG3_monic (by
      rw [polynomialNumerator,table_H_4,table_J_4]
      norm_num only [Nat.cast_ofNat,map_ofNat,map_neg]
      ring)
  simpa only [hankelDegree,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using h

end OscillatoryRecurrence
