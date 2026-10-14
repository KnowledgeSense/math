import OscillatoryRecurrence.AppendixPolynomials

noncomputable section
open Polynomial
open scoped Matrix BigOperators
namespace OscillatoryRecurrence
set_option maxHeartbeats 2000000

theorem sample_H_5_0 :
    (polynomialHankel 5).eval (0)=318504960 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    6, 6, 1, 0, 0;
    24, 36, 12, 1, 0;
    120, 240, 120, 20, 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 12, 48, 240;
    0, 4, 24, 144, 960;
    0, 0, 24, 288, 2880;
    0, 0, 0, 288, 5760;
    0, 0, 0, 0, 5760]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 12, 48, 240;
    4, 12, 48, 240, 1440;
    12, 48, 240, 1440, 10080;
    48, 240, 1440, 10080, 80640;
    240, 1440, 10080, 80640, 725760]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+j.val)).eval (0)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_5_1 :
    (polynomialHankel 5).eval (-1)=4803526656 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    7, (14/3), 1, 0, 0;
    28, (85/3), (19/2), 1, 0;
    141, 188, (432/5), (464/27), 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 14, 56, 282;
    0, 6, 28, 170, 1128;
    0, 0, (160/3), (1520/3), 4608;
    0, 0, 0, 648, 11136;
    0, 0, 0, 0, (521216/45)]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 14, 56, 282;
    4, 14, 56, 282, 1692;
    14, 56, 282, 1692, 11846;
    56, 282, 1692, 11846, 94768;
    282, 1692, 11846, 94768, 852914]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+j.val)).eval (-1)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_5_2 :
    (polynomialHankel 5).eval (-2)=11978801152 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    8, 4, 1, 0, 0;
    32, 25, (82/9), 1, 0;
    164, 164, (740/9), (14740/863), 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 16, 64, 328;
    0, 8, 32, 200, 1312;
    0, 0, 72, 656, 5920;
    0, 0, 0, (6904/9), (117920/9);
    0, 0, 0, 0, (11698048/863)]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 16, 64, 328;
    4, 16, 64, 328, 1968;
    16, 64, 328, 1968, 13792;
    64, 328, 1968, 13792, 110336;
    328, 1968, 13792, 110336, 993056]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+j.val)).eval (-2)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_5_3 :
    (polynomialHankel 5).eval (-3)=24508956672 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    9, (18/5), 1, 0, 0;
    36, (117/5), 9, 1, 0;
    189, (756/5), 82, 17, 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 18, 72, 378;
    0, 10, 36, 234, 1512;
    0, 0, (432/5), (3888/5), (35424/5);
    0, 0, 0, 864, 14688;
    0, 0, 0, 0, 16416]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 18, 72, 378;
    4, 18, 72, 378, 2268;
    18, 72, 378, 2268, 15930;
    72, 378, 2268, 15930, 127440;
    378, 2268, 15930, 127440, 1147122]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+j.val)).eval (-3)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_5_4 :
    (polynomialHankel 5).eval (-4)=46581153792 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    10, (10/3), 1, 0, 0;
    40, (68/3), (332/37), 1, 0;
    216, 144, (3072/37), (6252/371), 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 20, 80, 432;
    0, 12, 40, 272, 1728;
    0, 0, (296/3), (2656/3), 8192;
    0, 0, 0, (35616/37), (600192/37);
    0, 0, 0, 0, (7581568/371)]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 20, 80, 432;
    4, 20, 80, 432, 2592;
    20, 80, 432, 2592, 18272;
    80, 432, 2592, 18272, 146176;
    432, 2592, 18272, 146176, 1316096]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+j.val)).eval (-4)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_5_5 :
    (polynomialHankel 5).eval (-5)=84266844160 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    11, (22/7), 1, 0, 0;
    44, (157/7), (431/48), 1, 0;
    245, 140, (1015/12), (53380/3209), 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 22, 88, 490;
    0, 14, 44, 314, 1960;
    0, 0, (768/7), (6896/7), 9280;
    0, 0, 0, (3209/3), (53380/3);
    0, 0, 0, 0, (82291840/3209)]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 22, 88, 490;
    4, 22, 88, 490, 2940;
    22, 88, 490, 2940, 20830;
    88, 490, 2940, 20830, 166640;
    490, 2940, 20830, 166640, 1501010]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+j.val)).eval (-5)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_5_6 :
    (polynomialHankel 5).eval (-6)=145907122176 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    12, 3, 1, 0, 0;
    48, (45/2), 9, 1, 0;
    276, 138, (432/5), (180/11), 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 24, 96, 552;
    0, 16, 48, 360, 2208;
    0, 0, 120, 1080, 10368;
    0, 0, 0, 1188, 19440;
    0, 0, 0, 0, (1759104/55)]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 24, 96, 552;
    4, 24, 96, 552, 3312;
    24, 96, 552, 3312, 23616;
    96, 552, 3312, 23616, 188928;
    552, 3312, 23616, 188928, 1702944]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+j.val)).eval (-6)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_5_0 :
    (polynomialBorder 5).eval (0)=9555148800 := by
  rw [polynomialBorder_eval 5 (by norm_num)]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    6, 6, 1, 0, 0;
    24, 36, 12, 1, 0;
    120, 240, 120, 20, 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 12, 48, 1440;
    0, 4, 24, 144, 7200;
    0, 0, 24, 288, 28800;
    0, 0, 0, 288, 86400;
    0, 0, 0, 0, 172800]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 12, 48, 1440;
    4, 12, 48, 240, 10080;
    12, 48, 240, 1440, 80640;
    48, 240, 1440, 10080, 725760;
    240, 1440, 10080, 80640, 7257600]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+borderColumn 5 j)).eval (0)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_5_1 :
    (polynomialBorder 5).eval (-1)=130641494016 := by
  rw [polynomialBorder_eval 5 (by norm_num)]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    7, (14/3), 1, 0, 0;
    28, (85/3), (19/2), 1, 0;
    141, 188, (432/5), (464/27), 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 14, 56, 1692;
    0, 6, 28, 170, 8462;
    0, 0, (160/3), (1520/3), (130304/3);
    0, 0, 0, 648, 153152;
    0, 0, 0, 0, (42526528/135)]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 14, 56, 1692;
    4, 14, 56, 282, 11846;
    14, 56, 282, 1692, 94768;
    56, 282, 1692, 11846, 852914;
    282, 1692, 11846, 94768, 8529140]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+borderColumn 5 j)).eval (-1)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_5_2 :
    (polynomialBorder 5).eval (-2)=321020755968 := by
  rw [polynomialBorder_eval 5 (by norm_num)]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    8, 4, 1, 0, 0;
    32, 25, (82/9), 1, 0;
    164, 164, (740/9), (14740/863), 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 16, 64, 1968;
    0, 8, 32, 200, 9856;
    0, 0, 72, 656, 55168;
    0, 0, 0, (6904/9), (1629344/9);
    0, 0, 0, 0, 363264]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 16, 64, 1968;
    4, 16, 64, 328, 13792;
    16, 64, 328, 1968, 110336;
    64, 328, 1968, 13792, 993056;
    328, 1968, 13792, 110336, 9930560]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+borderColumn 5 j)).eval (-2)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_5_3 :
    (polynomialBorder 5).eval (-3)=635942928384 := by
  rw [polynomialBorder_eval 5 (by norm_num)]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    9, (18/5), 1, 0, 0;
    36, (117/5), 9, 1, 0;
    189, (756/5), 82, 17, 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 18, 72, 2268;
    0, 10, 36, 234, 11394;
    0, 0, (432/5), (3888/5), (330048/5);
    0, 0, 0, 864, 204768;
    0, 0, 0, 0, 425952]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 18, 72, 2268;
    4, 18, 72, 378, 15930;
    18, 72, 378, 2268, 127440;
    72, 378, 2268, 15930, 1147122;
    378, 2268, 15930, 127440, 11471220]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+borderColumn 5 j)).eval (-3)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_5_4 :
    (polynomialBorder 5).eval (-4)=1160649375744 := by
  rw [polynomialBorder_eval 5 (by norm_num)]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    10, (10/3), 1, 0, 0;
    40, (68/3), (332/37), 1, 0;
    216, 144, (3072/37), (6252/371), 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 20, 80, 2592;
    0, 12, 40, 272, 13088;
    0, 0, (296/3), (2656/3), (229888/3);
    0, 0, 0, (35616/37), (8441984/37);
    0, 0, 0, 0, (188907776/371)]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 20, 80, 2592;
    4, 20, 80, 432, 18272;
    20, 80, 432, 2592, 146176;
    80, 432, 2592, 18272, 1316096;
    432, 2592, 18272, 146176, 13160960]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+borderColumn 5 j)).eval (-4)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_5_5 :
    (polynomialBorder 5).eval (-5)=2017733836800 := by
  rw [polynomialBorder_eval 5 (by norm_num)]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    11, (22/7), 1, 0, 0;
    44, (157/7), (431/48), 1, 0;
    245, 140, (1015/12), (53380/3209), 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 22, 88, 2940;
    0, 14, 44, 314, 14950;
    0, 0, (768/7), (6896/7), (611200/7);
    0, 0, 0, (3209/3), (757000/3);
    0, 0, 0, 0, (1970443200/3209)]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 22, 88, 2940;
    4, 22, 88, 490, 20830;
    22, 88, 490, 2940, 166640;
    88, 490, 2940, 20830, 1501010;
    490, 2940, 20830, 166640, 15010100]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+borderColumn 5 j)).eval (-5)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_5_6 :
    (polynomialBorder 5).eval (-6)=3375069659136 := by
  rw [polynomialBorder_eval 5 (by norm_num)]
  let L : Matrix (Fin 5) (Fin 5) ℚ := !![1, 0, 0, 0, 0;
    2, 1, 0, 0, 0;
    12, 3, 1, 0, 0;
    48, (45/2), 9, 1, 0;
    276, 138, (432/5), (180/11), 1]
  let U : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 24, 96, 3312;
    0, 16, 48, 360, 16992;
    0, 0, 120, 1080, 98208;
    0, 0, 0, 1188, 277776;
    0, 0, 0, 0, (40690944/55)]
  let A : Matrix (Fin 5) (Fin 5) ℚ := !![2, 4, 24, 96, 3312;
    4, 24, 96, 552, 23616;
    24, 96, 552, 3312, 188928;
    96, 552, 3312, 23616, 1702944;
    552, 3312, 23616, 188928, 17029440]
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
  have he : (Matrix.of (fun i j : Fin 5 =>
      (endpointMoment (i.val+borderColumn 5 j)).eval (-6)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem table_H_5 : polynomialHankel 5=C (32768)*appendixG6 := by
  apply eq_of_natDegree_lt_card_of_eval_eq (f:=fun i : Fin 7 => -(i.val:ℚ))
  · intro i j h
    apply Fin.ext
    exact_mod_cast neg_inj.mp h
  · intro i
    fin_cases i <;>
      norm_num [sample_H_5_0,sample_H_5_1,sample_H_5_2,sample_H_5_3,sample_H_5_4,sample_H_5_5,sample_H_5_6,appendixG6]
  · apply max_lt
    · rw [polynomialHankel_natDegree]
      norm_num [hankelDegree]
    · unfold appendixG6
      compute_degree!

theorem table_J_5 : polynomialBorder 5=C (983040)*appendixG6-X*(C (196608)*appendixG5) := by
  apply eq_of_natDegree_lt_card_of_eval_eq (f:=fun i : Fin 7 => -(i.val:ℚ))
  · intro i j h
    apply Fin.ext
    exact_mod_cast neg_inj.mp h
  · intro i
    fin_cases i <;>
      norm_num [sample_J_5_0,sample_J_5_1,sample_J_5_2,sample_J_5_3,sample_J_5_4,sample_J_5_5,sample_J_5_6,appendixG6,appendixG5]
  · apply max_lt
    · rw [polynomialBorder_natDegree 5 (by norm_num)]
      norm_num [hankelDegree]
    · unfold appendixG6 appendixG5
      compute_degree!

theorem recurrenceFamily_appendix_6 : recurrenceFamily 6=appendixG6 := by
  have h := recurrenceFamily_hankel_eq (n:=5) (by norm_num) appendixG6
    (32768) (by norm_num) appendixG6_monic table_H_5
  simpa only [hankelDegree,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceMul] using h

theorem recurrenceFamily_appendix_5 : recurrenceFamily 5=appendixG5 := by
  have h := recurrenceFamily_numerator_eq (n:=5) (by norm_num) appendixG5
    (196608) (by norm_num) appendixG5_monic (by
      rw [polynomialNumerator,table_H_5,table_J_5]
      norm_num only [Nat.cast_ofNat,map_ofNat,map_neg]
      ring)
  simpa only [hankelDegree,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using h

end OscillatoryRecurrence
