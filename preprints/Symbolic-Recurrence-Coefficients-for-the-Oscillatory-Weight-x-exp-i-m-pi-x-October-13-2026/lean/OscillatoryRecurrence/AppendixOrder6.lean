import OscillatoryRecurrence.AppendixPolynomials

noncomputable section
open Polynomial
open scoped Matrix BigOperators
namespace OscillatoryRecurrence
set_option maxHeartbeats 2000000

theorem sample_H_6_0 :
    (polynomialHankel 6).eval (0)=55037657088000 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    6, 6, 1, 0, 0, 0;
    24, 36, 12, 1, 0, 0;
    120, 240, 120, 20, 1, 0;
    720, 1800, 1200, 300, 30, 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 12, 48, 240, 1440;
    0, 4, 24, 144, 960, 7200;
    0, 0, 24, 288, 2880, 28800;
    0, 0, 0, 288, 5760, 86400;
    0, 0, 0, 0, 5760, 172800;
    0, 0, 0, 0, 0, 172800]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 12, 48, 240, 1440;
    4, 12, 48, 240, 1440, 10080;
    12, 48, 240, 1440, 10080, 80640;
    48, 240, 1440, 10080, 80640, 725760;
    240, 1440, 10080, 80640, 725760, 7257600;
    1440, 10080, 80640, 725760, 7257600, 79833600]
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
  have hm8 : (endpointMoment 8).eval (0)=725760 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (0)=7257600 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (0)=79833600 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+j.val)).eval (0)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_6_1 :
    (polynomialHankel 6).eval (-1)=1525128739422208 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    7, (14/3), 1, 0, 0, 0;
    28, (85/3), (19/2), 1, 0, 0;
    141, 188, (432/5), (464/27), 1, 0;
    846, (4231/3), (4072/5), (19144/81), (664477/24432), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 14, 56, 282, 1692;
    0, 6, 28, 170, 1128, 8462;
    0, 0, (160/3), (1520/3), 4608, (130304/3);
    0, 0, 0, 648, 11136, 153152;
    0, 0, 0, 0, (521216/45), (42526528/135);
    0, 0, 0, 0, 0, (1454476108/4581)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 14, 56, 282, 1692;
    4, 14, 56, 282, 1692, 11846;
    14, 56, 282, 1692, 11846, 94768;
    56, 282, 1692, 11846, 94768, 852914;
    282, 1692, 11846, 94768, 852914, 8529140;
    1692, 11846, 94768, 852914, 8529140, 93820542]
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
  have hm8 : (endpointMoment 8).eval (-1)=852914 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-1)=8529140 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-1)=93820542 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+j.val)).eval (-1)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_6_2 :
    (polynomialHankel 6).eval (-2)=5103135387287552 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    8, 4, 1, 0, 0, 0;
    32, 25, (82/9), 1, 0, 0;
    164, 164, (740/9), (14740/863), 1, 0;
    984, 1232, (6896/9), 236, (2449194/91391), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 16, 64, 328, 1968;
    0, 8, 32, 200, 1312, 9856;
    0, 0, 72, 656, 5920, 55168;
    0, 0, 0, (6904/9), (117920/9), (1629344/9);
    0, 0, 0, 0, (11698048/863), 363264;
    0, 0, 0, 0, 0, (38933833216/91391)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 16, 64, 328, 1968;
    4, 16, 64, 328, 1968, 13792;
    16, 64, 328, 1968, 13792, 110336;
    64, 328, 1968, 13792, 110336, 993056;
    328, 1968, 13792, 110336, 993056, 9930560;
    1968, 13792, 110336, 993056, 9930560, 109236224]
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
  have hm8 : (endpointMoment 8).eval (-2)=993056 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-2)=9930560 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-2)=109236224 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+j.val)).eval (-2)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_6_3 :
    (polynomialHankel 6).eval (-3)=15097187084009472 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    9, (18/5), 1, 0, 0, 0;
    36, (117/5), 9, 1, 0, 0;
    189, (756/5), 82, 17, 1, 0;
    1134, (5697/5), 764, 237, (493/19), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 18, 72, 378, 2268;
    0, 10, 36, 234, 1512, 11394;
    0, 0, (432/5), (3888/5), (35424/5), (330048/5);
    0, 0, 0, 864, 14688, 204768;
    0, 0, 0, 0, 16416, 425952;
    0, 0, 0, 0, 0, (11703744/19)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 18, 72, 378, 2268;
    4, 18, 72, 378, 2268, 15930;
    18, 72, 378, 2268, 15930, 127440;
    72, 378, 2268, 15930, 127440, 1147122;
    378, 2268, 15930, 127440, 1147122, 11471220;
    2268, 15930, 127440, 1147122, 11471220, 126183906]
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
  have hm8 : (endpointMoment 8).eval (-3)=1147122 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-3)=11471220 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-3)=126183906 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+j.val)).eval (-3)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_6_4 :
    (polynomialHankel 6).eval (-4)=39908411516649472 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    10, (10/3), 1, 0, 0, 0;
    40, (68/3), (332/37), 1, 0, 0;
    216, 144, (3072/37), (6252/371), 1, 0;
    1296, (3272/3), (28736/37), (263812/1113), (1475842/59231), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 20, 80, 432, 2592;
    0, 12, 40, 272, 1728, 13088;
    0, 0, (296/3), (2656/3), 8192, (229888/3);
    0, 0, 0, (35616/37), (600192/37), (8441984/37);
    0, 0, 0, 0, (7581568/371), (188907776/371);
    0, 0, 0, 0, 0, (152238508288/177693)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 20, 80, 432, 2592;
    4, 20, 80, 432, 2592, 18272;
    20, 80, 432, 2592, 18272, 146176;
    80, 432, 2592, 18272, 146176, 1316096;
    432, 2592, 18272, 146176, 1316096, 13160960;
    2592, 18272, 146176, 1316096, 13160960, 144772608]
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
  have hm8 : (endpointMoment 8).eval (-4)=1316096 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-4)=13160960 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-4)=144772608 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+j.val)).eval (-4)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_6_5 :
    (polynomialHankel 6).eval (-5)=93994022862848000 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    11, (22/7), 1, 0, 0, 0;
    44, (157/7), (431/48), 1, 0, 0;
    245, 140, (1015/12), (53380/3209), 1, 0;
    1470, (7475/7), (4775/6), (757000/3209), (6157635/257162), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 22, 88, 490, 2940;
    0, 14, 44, 314, 1960, 14950;
    0, 0, (768/7), (6896/7), 9280, (611200/7);
    0, 0, 0, (3209/3), (53380/3), (757000/3);
    0, 0, 0, 0, (82291840/3209), (1970443200/3209);
    0, 0, 0, 0, 0, (143423496800/128581)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 22, 88, 490, 2940;
    4, 22, 88, 490, 2940, 20830;
    22, 88, 490, 2940, 20830, 166640;
    88, 490, 2940, 20830, 166640, 1501010;
    490, 2940, 20830, 166640, 1501010, 15010100;
    2940, 20830, 166640, 1501010, 15010100, 165117350]
  have hm0 : (endpointMoment 0).eval (-5)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-5)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-5)=22 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-5)=88 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-5)=490 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-5)=2940 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-5)=20830 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-5)=166640 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-5)=1501010 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-5)=15010100 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-5)=165117350 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+j.val)).eval (-5)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_6_6 :
    (polynomialHankel 6).eval (-6)=200346758427967488 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    12, 3, 1, 0, 0, 0;
    48, (45/2), 9, 1, 0, 0;
    276, 138, (432/5), (180/11), 1, 0;
    1656, 1062, (4092/5), (2572/11), (11774/509), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 24, 96, 552, 3312;
    0, 16, 48, 360, 2208, 16992;
    0, 0, 120, 1080, 10368, 98208;
    0, 0, 0, 1188, 19440, 277776;
    0, 0, 0, 0, (1759104/55), (40690944/55);
    0, 0, 0, 0, 0, (698913792/509)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 24, 96, 552, 3312;
    4, 24, 96, 552, 3312, 23616;
    24, 96, 552, 3312, 23616, 188928;
    96, 552, 3312, 23616, 188928, 1702944;
    552, 3312, 23616, 188928, 1702944, 17029440;
    3312, 23616, 188928, 1702944, 17029440, 187339392]
  have hm0 : (endpointMoment 0).eval (-6)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-6)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-6)=24 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-6)=96 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-6)=552 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-6)=3312 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-6)=23616 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-6)=188928 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-6)=1702944 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-6)=17029440 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-6)=187339392 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+j.val)).eval (-6)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_6_7 :
    (polynomialHankel 6).eval (-7)=393580717017137152 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    13, (26/9), 1, 0, 0, 0;
    52, (205/9), (659/73), 1, 0, 0;
    309, (412/3), (6450/73), (16105/1003), 1, 0;
    1854, (9613/9), (61532/73), (695269/3009), (27742021/1233529), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 26, 104, 618, 3708;
    0, 18, 52, 410, 2472, 19226;
    0, 0, (1168/9), (10544/9), (34400/3), (984512/9);
    0, 0, 0, (96288/73), (1546080/73), (22248608/73);
    0, 0, 0, 0, (39472928/1003), (887744672/1003);
    0, 0, 0, 0, 0, (6005565140032/3700587)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 26, 104, 618, 3708;
    4, 26, 104, 618, 3708, 26642;
    26, 104, 618, 3708, 26642, 213136;
    104, 618, 3708, 26642, 213136, 1923026;
    618, 3708, 26642, 213136, 1923026, 19230260;
    3708, 26642, 213136, 1923026, 19230260, 211566474]
  have hm0 : (endpointMoment 0).eval (-7)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-7)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-7)=26 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-7)=104 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-7)=618 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-7)=3708 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-7)=26642 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-7)=213136 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-7)=1923026 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-7)=19230260 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-7)=211566474 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+j.val)).eval (-7)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_6_8 :
    (polynomialHankel 6).eval (-8)=723728872717156352 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    14, (14/5), 1, 0, 0, 0;
    56, (116/5), (788/87), 1, 0, 0;
    344, (688/5), (7864/87), (62588/3979), 1, 0;
    2064, (5416/5), (75568/87), (906788/3979), (32577186/1481023), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 28, 112, 688, 4128;
    0, 20, 56, 464, 2752, 21664;
    0, 0, (696/5), (6304/5), (62912/5), (604544/5);
    0, 0, 0, (127328/87), (2002816/87), (29017216/87);
    0, 0, 0, 0, (189570944/3979), (4169879808/3979);
    0, 0, 0, 0, 0, (2760806551808/1481023)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 28, 112, 688, 4128;
    4, 28, 112, 688, 4128, 29920;
    28, 112, 688, 4128, 29920, 239360;
    112, 688, 4128, 29920, 239360, 2162432;
    688, 4128, 29920, 239360, 2162432, 21624320;
    4128, 29920, 239360, 2162432, 21624320, 237933056]
  have hm0 : (endpointMoment 0).eval (-8)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-8)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-8)=28 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-8)=112 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-8)=688 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-8)=4128 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-8)=29920 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-8)=239360 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-8)=2162432 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-8)=21624320 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-8)=237933056 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+j.val)).eval (-8)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_6_9 :
    (polynomialHankel 6).eval (-9)=1260874280082604032 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    15, (30/11), 1, 0, 0, 0;
    60, (261/11), (309/34), 1, 0, 0;
    381, (1524/11), (1572/17), (5896/383), 1, 0;
    2286, (12159/11), (15216/17), (85992/383), (815613/37724), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 30, 120, 762, 4572;
    0, 22, 60, 522, 3048, 24318;
    0, 0, (1632/11), (14832/11), (150912/11), (1460736/11);
    0, 0, 0, (27576/17), (424512/17), (6191424/17);
    0, 0, 0, 0, (21729024/383), (469793088/383);
    0, 0, 0, 0, 0, (19793636496/9431)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 30, 120, 762, 4572;
    4, 30, 120, 762, 4572, 33462;
    30, 120, 762, 4572, 33462, 267696;
    120, 762, 4572, 33462, 267696, 2422386;
    762, 4572, 33462, 267696, 2422386, 24223860;
    4572, 33462, 267696, 2422386, 24223860, 266580558]
  have hm0 : (endpointMoment 0).eval (-9)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-9)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-9)=30 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-9)=120 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-9)=762 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-9)=4572 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-9)=33462 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-9)=267696 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-9)=2422386 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-9)=24223860 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-9)=266580558 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+j.val)).eval (-9)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_6_0 :
    (polynomialBorder 6).eval (0)=2311581597696000 := by
  rw [polynomialBorder_eval 6 (by norm_num)]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    6, 6, 1, 0, 0, 0;
    24, 36, 12, 1, 0, 0;
    120, 240, 120, 20, 1, 0;
    720, 1800, 1200, 300, 30, 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 12, 48, 240, 10080;
    0, 4, 24, 144, 960, 60480;
    0, 0, 24, 288, 2880, 302400;
    0, 0, 0, 288, 5760, 1209600;
    0, 0, 0, 0, 5760, 3628800;
    0, 0, 0, 0, 0, 7257600]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 12, 48, 240, 10080;
    4, 12, 48, 240, 1440, 80640;
    12, 48, 240, 1440, 10080, 725760;
    48, 240, 1440, 10080, 80640, 7257600;
    240, 1440, 10080, 80640, 725760, 79833600;
    1440, 10080, 80640, 725760, 7257600, 958003200]
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
  have hm8 : (endpointMoment 8).eval (0)=725760 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (0)=7257600 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (0)=79833600 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (0)=958003200 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+borderColumn 6 j)).eval (0)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_6_1 :
    (polynomialBorder 6).eval (-1)=59611428855742464 := by
  rw [polynomialBorder_eval 6 (by norm_num)]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    7, (14/3), 1, 0, 0, 0;
    28, (85/3), (19/2), 1, 0, 0;
    141, 188, (432/5), (464/27), 1, 0;
    846, (4231/3), (4072/5), (19144/81), (664477/24432), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 14, 56, 282, 11846;
    0, 6, 28, 170, 1128, 71076;
    0, 0, (160/3), (1520/3), 4608, 438304;
    0, 0, 0, 648, 11136, 2019744;
    0, 0, 0, 0, (521216/45), (93132416/15);
    0, 0, 0, 0, 0, (6316654296/509)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 14, 56, 282, 11846;
    4, 14, 56, 282, 1692, 94768;
    14, 56, 282, 1692, 11846, 852914;
    56, 282, 1692, 11846, 94768, 8529140;
    282, 1692, 11846, 94768, 852914, 93820542;
    1692, 11846, 94768, 852914, 8529140, 1125846504]
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
  have hm8 : (endpointMoment 8).eval (-1)=852914 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-1)=8529140 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-1)=93820542 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-1)=1125846504 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+borderColumn 6 j)).eval (-1)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_6_2 :
    (polynomialBorder 6).eval (-2)=190463978684547072 := by
  rw [polynomialBorder_eval 6 (by norm_num)]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    8, 4, 1, 0, 0, 0;
    32, 25, (82/9), 1, 0, 0;
    164, 164, (740/9), (14740/863), 1, 0;
    984, 1232, (6896/9), 236, (2449194/91391), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 16, 64, 328, 13792;
    0, 8, 32, 200, 1312, 82752;
    0, 0, 72, 656, 5920, 551712;
    0, 0, 0, (6904/9), (117920/9), (7181120/3);
    0, 0, 0, 0, (11698048/863), (6175302144/863);
    0, 0, 0, 0, 0, (1453124837376/91391)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 16, 64, 328, 13792;
    4, 16, 64, 328, 1968, 110336;
    16, 64, 328, 1968, 13792, 993056;
    64, 328, 1968, 13792, 110336, 9930560;
    328, 1968, 13792, 110336, 993056, 109236224;
    1968, 13792, 110336, 993056, 9930560, 1310834688]
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
  have hm8 : (endpointMoment 8).eval (-2)=993056 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-2)=9930560 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-2)=109236224 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-2)=1310834688 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+borderColumn 6 j)).eval (-2)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_6_3 :
    (polynomialBorder 6).eval (-3)=534257196909723648 := by
  rw [polynomialBorder_eval 6 (by norm_num)]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    9, (18/5), 1, 0, 0, 0;
    36, (117/5), 9, 1, 0, 0;
    189, (756/5), 82, 17, 1, 0;
    1134, (5697/5), 764, 237, (493/19), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 18, 72, 378, 15930;
    0, 10, 36, 234, 1512, 95580;
    0, 0, (432/5), (3888/5), (35424/5), 659664;
    0, 0, 0, 864, 14688, 2724192;
    0, 0, 0, 0, 16416, 8317728;
    0, 0, 0, 0, 0, (414170496/19)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 18, 72, 378, 15930;
    4, 18, 72, 378, 2268, 127440;
    18, 72, 378, 2268, 15930, 1147122;
    72, 378, 2268, 15930, 127440, 11471220;
    378, 2268, 15930, 127440, 1147122, 126183906;
    2268, 15930, 127440, 1147122, 11471220, 1514206872]
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
  have hm8 : (endpointMoment 8).eval (-3)=1147122 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-3)=11471220 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-3)=126183906 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-3)=1514206872 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+borderColumn 6 j)).eval (-3)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_6_4 :
    (polynomialBorder 6).eval (-4)=1362937874290311168 := by
  rw [polynomialBorder_eval 6 (by norm_num)]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    10, (10/3), 1, 0, 0, 0;
    40, (68/3), (332/37), 1, 0, 0;
    216, 144, (3072/37), (6252/371), 1, 0;
    1296, (3272/3), (28736/37), (263812/1113), (1475842/59231), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 20, 80, 432, 18272;
    0, 12, 40, 272, 1728, 109632;
    0, 0, (296/3), (2656/3), 8192, 767936;
    0, 0, 0, (35616/37), (600192/37), (113013504/37);
    0, 0, 0, 0, (7581568/371), (3638431488/371);
    0, 0, 0, 0, 0, (1733065127424/59231)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 20, 80, 432, 18272;
    4, 20, 80, 432, 2592, 146176;
    20, 80, 432, 2592, 18272, 1316096;
    80, 432, 2592, 18272, 146176, 13160960;
    432, 2592, 18272, 146176, 1316096, 144772608;
    2592, 18272, 146176, 1316096, 13160960, 1737271296]
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
  have hm8 : (endpointMoment 8).eval (-4)=1316096 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-4)=13160960 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-4)=144772608 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-4)=1737271296 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+borderColumn 6 j)).eval (-4)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_6_5 :
    (polynomialBorder 6).eval (-5)=3146016453820416000 := by
  rw [polynomialBorder_eval 6 (by norm_num)]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    11, (22/7), 1, 0, 0, 0;
    44, (157/7), (431/48), 1, 0, 0;
    245, 140, (1015/12), (53380/3209), 1, 0;
    1470, (7475/7), (4775/6), (757000/3209), (6157635/257162), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 22, 88, 490, 20830;
    0, 14, 44, 314, 1960, 124980;
    0, 0, (768/7), (6896/7), 9280, (6153600/7);
    0, 0, 0, (3209/3), (53380/3), 3397000;
    0, 0, 0, 0, (82291840/3209), (37396147200/3209);
    0, 0, 0, 0, 0, (4800440145600/128581)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 22, 88, 490, 20830;
    4, 22, 88, 490, 2940, 166640;
    22, 88, 490, 2940, 20830, 1501010;
    88, 490, 2940, 20830, 166640, 15010100;
    490, 2940, 20830, 166640, 1501010, 165117350;
    2940, 20830, 166640, 1501010, 15010100, 1981408200]
  have hm0 : (endpointMoment 0).eval (-5)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-5)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-5)=22 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-5)=88 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-5)=490 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-5)=2940 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-5)=20830 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-5)=166640 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-5)=1501010 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-5)=15010100 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-5)=165117350 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-5)=1981408200 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+borderColumn 6 j)).eval (-5)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_6_6 :
    (polynomialBorder 6).eval (-6)=6632920923424948224 := by
  rw [polynomialBorder_eval 6 (by norm_num)]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    12, 3, 1, 0, 0, 0;
    48, (45/2), 9, 1, 0, 0;
    276, 138, (432/5), (180/11), 1, 0;
    1656, 1062, (4092/5), (2572/11), (11774/509), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 24, 96, 552, 23616;
    0, 16, 48, 360, 2208, 141696;
    0, 0, 120, 1080, 10368, 994464;
    0, 0, 0, 1188, 19440, 3757536;
    0, 0, 0, 0, (1759104/55), (762227712/55);
    0, 0, 0, 0, 0, (23139081216/509)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 24, 96, 552, 23616;
    4, 24, 96, 552, 3312, 188928;
    24, 96, 552, 3312, 23616, 1702944;
    96, 552, 3312, 23616, 188928, 17029440;
    552, 3312, 23616, 188928, 1702944, 187339392;
    3312, 23616, 188928, 1702944, 17029440, 2248072704]
  have hm0 : (endpointMoment 0).eval (-6)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-6)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-6)=24 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-6)=96 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-6)=552 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-6)=3312 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-6)=23616 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-6)=188928 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-6)=1702944 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-6)=17029440 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-6)=187339392 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-6)=2248072704 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+borderColumn 6 j)).eval (-6)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_6_7 :
    (polynomialBorder 6).eval (-7)=12955417356892372992 := by
  rw [polynomialBorder_eval 6 (by norm_num)]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    13, (26/9), 1, 0, 0, 0;
    52, (205/9), (659/73), 1, 0, 0;
    309, (412/3), (6450/73), (16105/1003), 1, 0;
    1854, (9613/9), (61532/73), (695269/3009), (27742021/1233529), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 26, 104, 618, 26642;
    0, 18, 52, 410, 2472, 159852;
    0, 0, (1168/9), (10544/9), (34400/3), (3344656/3);
    0, 0, 0, (96288/73), (1546080/73), (302168160/73);
    0, 0, 0, 0, (39472928/1003), (16459455264/1003);
    0, 0, 0, 0, 0, (65894660221824/1233529)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 26, 104, 618, 26642;
    4, 26, 104, 618, 3708, 213136;
    26, 104, 618, 3708, 26642, 1923026;
    104, 618, 3708, 26642, 213136, 19230260;
    618, 3708, 26642, 213136, 1923026, 211566474;
    3708, 26642, 213136, 1923026, 19230260, 2538797688]
  have hm0 : (endpointMoment 0).eval (-7)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-7)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-7)=26 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-7)=104 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-7)=618 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-7)=3708 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-7)=26642 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-7)=213136 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-7)=1923026 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-7)=19230260 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-7)=211566474 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-7)=2538797688 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+borderColumn 6 j)).eval (-7)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_6_8 :
    (polynomialBorder 6).eval (-8)=23753149532275212288 := by
  rw [polynomialBorder_eval 6 (by norm_num)]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    14, (14/5), 1, 0, 0, 0;
    56, (116/5), (788/87), 1, 0, 0;
    344, (688/5), (7864/87), (62588/3979), 1, 0;
    2064, (5416/5), (75568/87), (906788/3979), (32577186/1481023), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 28, 112, 688, 29920;
    0, 20, 56, 464, 2752, 179520;
    0, 0, (696/5), (6304/5), (62912/5), 1240896;
    0, 0, 0, (127328/87), (2002816/87), (131792128/29);
    0, 0, 0, 0, (189570944/3979), (76751231232/3979);
    0, 0, 0, 0, 0, (90611074570752/1481023)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 28, 112, 688, 29920;
    4, 28, 112, 688, 4128, 239360;
    28, 112, 688, 4128, 29920, 2162432;
    112, 688, 4128, 29920, 239360, 21624320;
    688, 4128, 29920, 239360, 2162432, 237933056;
    4128, 29920, 239360, 2162432, 21624320, 2855196672]
  have hm0 : (endpointMoment 0).eval (-8)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-8)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-8)=28 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-8)=112 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-8)=688 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-8)=4128 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-8)=29920 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-8)=239360 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-8)=2162432 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-8)=21624320 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-8)=237933056 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-8)=2855196672 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+borderColumn 6 j)).eval (-8)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_6_9 :
    (polynomialBorder 6).eval (-9)=41325712299899486208 := by
  rw [polynomialBorder_eval 6 (by norm_num)]
  let L : Matrix (Fin 6) (Fin 6) ℚ := !![1, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0;
    15, (30/11), 1, 0, 0, 0;
    60, (261/11), (309/34), 1, 0, 0;
    381, (1524/11), (1572/17), (5896/383), 1, 0;
    2286, (12159/11), (15216/17), (85992/383), (815613/37724), 1]
  let U : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 30, 120, 762, 33462;
    0, 22, 60, 522, 3048, 200772;
    0, 0, (1632/11), (14832/11), (150912/11), 1372896;
    0, 0, 0, (27576/17), (424512/17), (84577824/17);
    0, 0, 0, 0, (21729024/383), (8607544704/383);
    0, 0, 0, 0, 0, (648745192224/9431)]
  let A : Matrix (Fin 6) (Fin 6) ℚ := !![2, 4, 30, 120, 762, 33462;
    4, 30, 120, 762, 4572, 267696;
    30, 120, 762, 4572, 33462, 2422386;
    120, 762, 4572, 33462, 267696, 24223860;
    762, 4572, 33462, 267696, 2422386, 266580558;
    4572, 33462, 267696, 2422386, 24223860, 3198966696]
  have hm0 : (endpointMoment 0).eval (-9)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-9)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-9)=30 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-9)=120 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-9)=762 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-9)=4572 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-9)=33462 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-9)=267696 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-9)=2422386 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-9)=24223860 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-9)=266580558 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-9)=3198966696 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have he : (Matrix.of (fun i j : Fin 6 =>
      (endpointMoment (i.val+borderColumn 6 j)).eval (-9)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem table_H_6 : polynomialHankel 6=C (-4194304)*appendixG9 := by
  apply eq_of_natDegree_lt_card_of_eval_eq (f:=fun i : Fin 10 => -(i.val:ℚ))
  · intro i j h
    apply Fin.ext
    exact_mod_cast neg_inj.mp h
  · intro i
    fin_cases i <;>
      norm_num [sample_H_6_0,sample_H_6_1,sample_H_6_2,sample_H_6_3,sample_H_6_4,sample_H_6_5,sample_H_6_6,sample_H_6_7,sample_H_6_8,sample_H_6_9,appendixG9]
  · apply max_lt
    · rw [polynomialHankel_natDegree]
      norm_num [hankelDegree]
    · unfold appendixG9
      compute_degree!

theorem table_J_6 : polynomialBorder 6=C (-176160768)*appendixG9-X*(C (-100663296)*appendixG8) := by
  apply eq_of_natDegree_lt_card_of_eval_eq (f:=fun i : Fin 10 => -(i.val:ℚ))
  · intro i j h
    apply Fin.ext
    exact_mod_cast neg_inj.mp h
  · intro i
    fin_cases i <;>
      norm_num [sample_J_6_0,sample_J_6_1,sample_J_6_2,sample_J_6_3,sample_J_6_4,sample_J_6_5,sample_J_6_6,sample_J_6_7,sample_J_6_8,sample_J_6_9,appendixG9,appendixG8]
  · apply max_lt
    · rw [polynomialBorder_natDegree 6 (by norm_num)]
      norm_num [hankelDegree]
    · unfold appendixG9 appendixG8
      compute_degree!

theorem recurrenceFamily_appendix_9 : recurrenceFamily 9=appendixG9 := by
  have h := recurrenceFamily_hankel_eq (n:=6) (by norm_num) appendixG9
    (-4194304) (by norm_num) appendixG9_monic table_H_6
  simpa only [hankelDegree,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceMul] using h

theorem recurrenceFamily_appendix_8 : recurrenceFamily 8=appendixG8 := by
  have h := recurrenceFamily_numerator_eq (n:=6) (by norm_num) appendixG8
    (-100663296) (by norm_num) appendixG8_monic (by
      rw [polynomialNumerator,table_H_6,table_J_6]
      norm_num only [Nat.cast_ofNat,map_ofNat,map_neg]
      ring)
  simpa only [hankelDegree,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using h

end OscillatoryRecurrence
