import OscillatoryRecurrence.AppendixPolynomials

noncomputable section
open Polynomial
open scoped Matrix BigOperators
namespace OscillatoryRecurrence
set_option maxHeartbeats 2000000

theorem sample_H_7_0 :
    (polynomialHankel 7).eval (0)=399441300081868800000 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    6, 6, 1, 0, 0, 0, 0;
    24, 36, 12, 1, 0, 0, 0;
    120, 240, 120, 20, 1, 0, 0;
    720, 1800, 1200, 300, 30, 1, 0;
    5040, 15120, 12600, 4200, 630, 42, 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 12, 48, 240, 1440, 10080;
    0, 4, 24, 144, 960, 7200, 60480;
    0, 0, 24, 288, 2880, 28800, 302400;
    0, 0, 0, 288, 5760, 86400, 1209600;
    0, 0, 0, 0, 5760, 172800, 3628800;
    0, 0, 0, 0, 0, 172800, 7257600;
    0, 0, 0, 0, 0, 0, 7257600]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 12, 48, 240, 1440, 10080;
    4, 12, 48, 240, 1440, 10080, 80640;
    12, 48, 240, 1440, 10080, 80640, 725760;
    48, 240, 1440, 10080, 80640, 725760, 7257600;
    240, 1440, 10080, 80640, 725760, 7257600, 79833600;
    1440, 10080, 80640, 725760, 7257600, 79833600, 958003200;
    10080, 80640, 725760, 7257600, 79833600, 958003200, 12454041600]
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
  have hm12 : (endpointMoment 12).eval (0)=12454041600 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+j.val)).eval (0)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_7_1 :
    (polynomialHankel 7).eval (-1)=20124401546916507156480 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    7, (14/3), 1, 0, 0, 0, 0;
    28, (85/3), (19/2), 1, 0, 0, 0;
    141, 188, (432/5), (464/27), 1, 0, 0;
    846, (4231/3), (4072/5), (19144/81), (664477/24432), 1, 0;
    5923, 11846, (41091/5), (28052/9), (2182791/4072), (14212472166/363619027), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 14, 56, 282, 1692, 11846;
    0, 6, 28, 170, 1128, 8462, 71076;
    0, 0, (160/3), (1520/3), 4608, (130304/3), 438304;
    0, 0, 0, 648, 11136, 153152, 2019744;
    0, 0, 0, 0, (521216/45), (42526528/135), (93132416/15);
    0, 0, 0, 0, 0, (1454476108/4581), (6316654296/509);
    0, 0, 0, 0, 0, 0, (4798031222085120/363619027)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 14, 56, 282, 1692, 11846;
    4, 14, 56, 282, 1692, 11846, 94768;
    14, 56, 282, 1692, 11846, 94768, 852914;
    56, 282, 1692, 11846, 94768, 852914, 8529140;
    282, 1692, 11846, 94768, 852914, 8529140, 93820542;
    1692, 11846, 94768, 852914, 8529140, 93820542, 1125846504;
    11846, 94768, 852914, 8529140, 93820542, 1125846504, 14636004554]
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
  have hm12 : (endpointMoment 12).eval (-1)=14636004554 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+j.val)).eval (-1)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_7_2 :
    (polynomialHankel 7).eval (-2)=112140880097790583111680 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    8, 4, 1, 0, 0, 0, 0;
    32, 25, (82/9), 1, 0, 0, 0;
    164, 164, (740/9), (14740/863), 1, 0, 0;
    984, 1232, (6896/9), 236, (2449194/91391), 1, 0;
    6896, 10344, (22988/3), (2692920/863), (48244548/91391), (2838134448/76042643), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 16, 64, 328, 1968, 13792;
    0, 8, 32, 200, 1312, 9856, 82752;
    0, 0, 72, 656, 5920, 55168, 551712;
    0, 0, 0, (6904/9), (117920/9), (1629344/9), (7181120/3);
    0, 0, 0, 0, (11698048/863), 363264, (6175302144/863);
    0, 0, 0, 0, 0, (38933833216/91391), (1453124837376/91391);
    0, 0, 0, 0, 0, 0, (1671029330757120/76042643)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 16, 64, 328, 1968, 13792;
    4, 16, 64, 328, 1968, 13792, 110336;
    16, 64, 328, 1968, 13792, 110336, 993056;
    64, 328, 1968, 13792, 110336, 993056, 9930560;
    328, 1968, 13792, 110336, 993056, 9930560, 109236224;
    1968, 13792, 110336, 993056, 9930560, 109236224, 1310834688;
    13792, 110336, 993056, 9930560, 109236224, 1310834688, 17040851072]
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
  have hm12 : (endpointMoment 12).eval (-2)=17040851072 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+j.val)).eval (-2)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_7_3 :
    (polynomialHankel 7).eval (-3)=490368242540916743602176 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    9, (18/5), 1, 0, 0, 0, 0;
    36, (117/5), 9, 1, 0, 0, 0;
    189, (756/5), 82, 17, 1, 0, 0;
    1134, (5697/5), 764, 237, (493/19), 1, 0;
    7965, 9558, 7635, 3153, (9627/19), (239682/6773), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 18, 72, 378, 2268, 15930;
    0, 10, 36, 234, 1512, 11394, 95580;
    0, 0, (432/5), (3888/5), (35424/5), (330048/5), 659664;
    0, 0, 0, 864, 14688, 204768, 2724192;
    0, 0, 0, 0, 16416, 425952, 8317728;
    0, 0, 0, 0, 0, (11703744/19), (414170496/19);
    0, 0, 0, 0, 0, 0, (219992246784/6773)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 18, 72, 378, 2268, 15930;
    4, 18, 72, 378, 2268, 15930, 127440;
    18, 72, 378, 2268, 15930, 127440, 1147122;
    72, 378, 2268, 15930, 127440, 1147122, 11471220;
    378, 2268, 15930, 127440, 1147122, 11471220, 126183906;
    2268, 15930, 127440, 1147122, 11471220, 126183906, 1514206872;
    15930, 127440, 1147122, 11471220, 126183906, 1514206872, 19684690794]
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
  have hm12 : (endpointMoment 12).eval (-3)=19684690794 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+j.val)).eval (-3)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_7_4 :
    (polynomialHankel 7).eval (-4)=1648855298672759314317312 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    10, (10/3), 1, 0, 0, 0, 0;
    40, (68/3), (332/37), 1, 0, 0, 0;
    216, 144, (3072/37), (6252/371), 1, 0, 0;
    1296, (3272/3), (28736/37), (263812/1113), (1475842/59231), 1, 0;
    9136, 9136, (287976/37), (1177224/371), (28425246/59231), (20309356962/594681673), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 20, 80, 432, 2592, 18272;
    0, 12, 40, 272, 1728, 13088, 109632;
    0, 0, (296/3), (2656/3), 8192, (229888/3), 767936;
    0, 0, 0, (35616/37), (600192/37), (8441984/37), (113013504/37);
    0, 0, 0, 0, (7581568/371), (188907776/371), (3638431488/371);
    0, 0, 0, 0, 0, (152238508288/177693), (1733065127424/59231);
    0, 0, 0, 0, 0, 0, (24569858590852608/594681673)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 20, 80, 432, 2592, 18272;
    4, 20, 80, 432, 2592, 18272, 146176;
    20, 80, 432, 2592, 18272, 146176, 1316096;
    80, 432, 2592, 18272, 146176, 1316096, 13160960;
    432, 2592, 18272, 146176, 1316096, 13160960, 144772608;
    2592, 18272, 146176, 1316096, 13160960, 144772608, 1737271296;
    18272, 146176, 1316096, 13160960, 144772608, 1737271296, 22584535040]
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
  have hm12 : (endpointMoment 12).eval (-4)=22584535040 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+j.val)).eval (-4)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_7_5 :
    (polynomialHankel 7).eval (-5)=4571209413318986956800000 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    11, (22/7), 1, 0, 0, 0, 0;
    44, (157/7), (431/48), 1, 0, 0, 0;
    245, 140, (1015/12), (53380/3209), 1, 0, 0;
    1470, (7475/7), (4775/6), (757000/3209), (6157635/257162), 1, 0;
    10415, (62490/7), (16025/2), (10191000/3209), (58431480/128581), (6000550182/179279371), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 22, 88, 490, 2940, 20830;
    0, 14, 44, 314, 1960, 14950, 124980;
    0, 0, (768/7), (6896/7), 9280, (611200/7), (6153600/7);
    0, 0, 0, (3209/3), (53380/3), (757000/3), 3397000;
    0, 0, 0, 0, (82291840/3209), (1970443200/3209), (37396147200/3209);
    0, 0, 0, 0, 0, (143423496800/128581), (4800440145600/128581);
    0, 0, 0, 0, 0, 0, (8718890024793600/179279371)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 22, 88, 490, 2940, 20830;
    4, 22, 88, 490, 2940, 20830, 166640;
    22, 88, 490, 2940, 20830, 166640, 1501010;
    88, 490, 2940, 20830, 166640, 1501010, 15010100;
    490, 2940, 20830, 166640, 1501010, 15010100, 165117350;
    2940, 20830, 166640, 1501010, 15010100, 165117350, 1981408200;
    20830, 166640, 1501010, 15010100, 165117350, 1981408200, 25758337850]
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
  have hm12 : (endpointMoment 12).eval (-5)=25758337850 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+j.val)).eval (-5)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_7_6 :
    (polynomialHankel 7).eval (-6)=11053801455658802369003520 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    12, 3, 1, 0, 0, 0, 0;
    48, (45/2), 9, 1, 0, 0, 0;
    276, 138, (432/5), (180/11), 1, 0, 0;
    1656, 1062, (4092/5), (2572/11), (11774/509), 1, 0;
    11808, 8856, (41436/5), (34792/11), (220552/509), (836917/25279), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 24, 96, 552, 3312, 23616;
    0, 16, 48, 360, 2208, 16992, 141696;
    0, 0, 120, 1080, 10368, 98208, 994464;
    0, 0, 0, 1188, 19440, 277776, 3757536;
    0, 0, 0, 0, (1759104/55), (40690944/55), (762227712/55);
    0, 0, 0, 0, 0, (698913792/509), (23139081216/509);
    0, 0, 0, 0, 0, 0, (1394727068160/25279)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 24, 96, 552, 3312, 23616;
    4, 24, 96, 552, 3312, 23616, 188928;
    24, 96, 552, 3312, 23616, 188928, 1702944;
    96, 552, 3312, 23616, 188928, 1702944, 17029440;
    552, 3312, 23616, 188928, 1702944, 17029440, 187339392;
    3312, 23616, 188928, 1702944, 17029440, 187339392, 2248072704;
    23616, 188928, 1702944, 17029440, 187339392, 2248072704, 29225038464]
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
  have hm12 : (endpointMoment 12).eval (-6)=29225038464 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+j.val)).eval (-6)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_7_7 :
    (polynomialHankel 7).eval (-7)=24201457244477629315153920 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    13, (26/9), 1, 0, 0, 0, 0;
    52, (205/9), (659/73), 1, 0, 0, 0;
    309, (412/3), (6450/73), (16105/1003), 1, 0, 0;
    1854, (9613/9), (61532/73), (695269/3009), (27742021/1233529), 1, 0;
    13321, (26642/3), (627123/73), (3147585/1003), (514357977/1233529), (3088812197898/93836955313), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 26, 104, 618, 3708, 26642;
    0, 18, 52, 410, 2472, 19226, 159852;
    0, 0, (1168/9), (10544/9), (34400/3), (984512/9), (3344656/3);
    0, 0, 0, (96288/73), (1546080/73), (22248608/73), (302168160/73);
    0, 0, 0, 0, (39472928/1003), (887744672/1003), (16459455264/1003);
    0, 0, 0, 0, 0, (6005565140032/3700587), (65894660221824/1233529);
    0, 0, 0, 0, 0, 0, (5770077048415572480/93836955313)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 26, 104, 618, 3708, 26642;
    4, 26, 104, 618, 3708, 26642, 213136;
    26, 104, 618, 3708, 26642, 213136, 1923026;
    104, 618, 3708, 26642, 213136, 1923026, 19230260;
    618, 3708, 26642, 213136, 1923026, 19230260, 211566474;
    3708, 26642, 213136, 1923026, 19230260, 211566474, 2538797688;
    26642, 213136, 1923026, 19230260, 211566474, 2538797688, 33004605242]
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
  have hm12 : (endpointMoment 12).eval (-7)=33004605242 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+j.val)).eval (-7)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_7_8 :
    (polynomialHankel 7).eval (-8)=49183136496943904373866496 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    14, (14/5), 1, 0, 0, 0, 0;
    56, (116/5), (788/87), 1, 0, 0, 0;
    344, (688/5), (7864/87), (62588/3979), 1, 0, 0;
    2064, (5416/5), (75568/87), (906788/3979), (32577186/1481023), 1, 0;
    14960, 8976, (258520/29), (12355512/3979), (599618994/1481023), (353949510042/10784400593), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 28, 112, 688, 4128, 29920;
    0, 20, 56, 464, 2752, 21664, 179520;
    0, 0, (696/5), (6304/5), (62912/5), (604544/5), 1240896;
    0, 0, 0, (127328/87), (2002816/87), (29017216/87), (131792128/29);
    0, 0, 0, 0, (189570944/3979), (4169879808/3979), (76751231232/3979);
    0, 0, 0, 0, 0, (2760806551808/1481023), (90611074570752/1481023);
    0, 0, 0, 0, 0, 0, (732885844959972864/10784400593)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 28, 112, 688, 4128, 29920;
    4, 28, 112, 688, 4128, 29920, 239360;
    28, 112, 688, 4128, 29920, 239360, 2162432;
    112, 688, 4128, 29920, 239360, 2162432, 21624320;
    688, 4128, 29920, 239360, 2162432, 21624320, 237933056;
    4128, 29920, 239360, 2162432, 21624320, 237933056, 2855196672;
    29920, 239360, 2162432, 21624320, 237933056, 2855196672, 37118081024]
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
  have hm12 : (endpointMoment 12).eval (-8)=37118081024 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+j.val)).eval (-8)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_7_9 :
    (polynomialHankel 7).eval (-9)=94374262462435176650637312 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    15, (30/11), 1, 0, 0, 0, 0;
    60, (261/11), (309/34), 1, 0, 0, 0;
    381, (1524/11), (1572/17), (5896/383), 1, 0, 0;
    2286, (12159/11), (15216/17), (85992/383), (815613/37724), 1, 0;
    16731, 9126, (157311/17), (1174692/383), (7471827/18862), (1501724982/45818603), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 30, 120, 762, 4572, 33462;
    0, 22, 60, 522, 3048, 24318, 200772;
    0, 0, (1632/11), (14832/11), (150912/11), (1460736/11), 1372896;
    0, 0, 0, (27576/17), (424512/17), (6191424/17), (84577824/17);
    0, 0, 0, 0, (21729024/383), (469793088/383), (8607544704/383);
    0, 0, 0, 0, 0, (19793636496/9431), (648745192224/9431);
    0, 0, 0, 0, 0, 0, (3429443310478848/45818603)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 30, 120, 762, 4572, 33462;
    4, 30, 120, 762, 4572, 33462, 267696;
    30, 120, 762, 4572, 33462, 267696, 2422386;
    120, 762, 4572, 33462, 267696, 2422386, 24223860;
    762, 4572, 33462, 267696, 2422386, 24223860, 266580558;
    4572, 33462, 267696, 2422386, 24223860, 266580558, 3198966696;
    33462, 267696, 2422386, 24223860, 266580558, 3198966696, 41587629930]
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
  have hm12 : (endpointMoment 12).eval (-9)=41587629930 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+j.val)).eval (-9)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_7_10 :
    (polynomialHankel 7).eval (-10)=173064143884031675596800000 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    16, (8/3), 1, 0, 0, 0, 0;
    64, (73/3), (538/59), 1, 0, 0, 0;
    420, 140, (5580/59), (66460/4413), 1, 0, 0;
    2520, (3400/3), (54400/59), (2927300/13239), (9786310/458697), 1, 0;
    18640, 9320, (566700/59), (4451800/1471), (59631420/152899), (8203394772/250429541), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 32, 128, 840, 5040, 37280;
    0, 24, 64, 584, 3360, 27200, 223680;
    0, 0, (472/3), (4304/3), 14880, (435200/3), 1511200;
    0, 0, 0, (105912/59), (1595040/59), (23418400/59), (320529600/59);
    0, 0, 0, 0, (97855360/1471), (6263238400/4413), (38164108800/1471);
    0, 0, 0, 0, 0, (3205498124800/1376091), (11667050342400/152899);
    0, 0, 0, 0, 0, 0, (20630853639129600/250429541)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 32, 128, 840, 5040, 37280;
    4, 32, 128, 840, 5040, 37280, 298240;
    32, 128, 840, 5040, 37280, 298240, 2704160;
    128, 840, 5040, 37280, 298240, 2704160, 27041600;
    840, 5040, 37280, 298240, 2704160, 27041600, 297657600;
    5040, 37280, 298240, 2704160, 27041600, 297657600, 3571891200;
    37280, 298240, 2704160, 27041600, 297657600, 3571891200, 46436585600]
  have hm0 : (endpointMoment 0).eval (-10)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-10)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-10)=32 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-10)=128 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-10)=840 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-10)=5040 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-10)=37280 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-10)=298240 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-10)=2704160 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-10)=27041600 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-10)=297657600 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-10)=3571891200 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-10)=46436585600 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+j.val)).eval (-10)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_7_11 :
    (polynomialHankel 7).eval (-11)=305973815474529430048604160 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    17, (34/13), 1, 0, 0, 0, 0;
    68, 25, (247/27), 1, 0, 0, 0;
    461, (1844/13), (13054/135), (24649/1673), 1, 0, 0;
    2766, (15161/13), (128164/135), (364345/1673), (424627671/20107261), 1, 0;
    20693, (124158/13), (448519/45), (4993833/1673), (7758890133/20107261), (26326773728946/803829329117), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 34, 136, 922, 5532, 41386;
    0, 26, 68, 650, 3688, 30322, 248316;
    0, 0, (2160/13), 1520, (208864/13), (2050624/13), (21528912/13);
    0, 0, 0, (53536/27), (788768/27), (11659040/27), (53267552/9);
    0, 0, 0, 0, (643432352/8365), (13588085472/8365), (248284484256/8365);
    0, 0, 0, 0, 0, (51445077063488/20107261), (1684913518652544/20107261);
    0, 0, 0, 0, 0, 0, (72949842327720983040/803829329117)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 34, 136, 922, 5532, 41386;
    4, 34, 136, 922, 5532, 41386, 331088;
    34, 136, 922, 5532, 41386, 331088, 3009074;
    136, 922, 5532, 41386, 331088, 3009074, 30090740;
    922, 5532, 41386, 331088, 3009074, 30090740, 331320242;
    5532, 41386, 331088, 3009074, 30090740, 331320242, 3975842904;
    41386, 331088, 3009074, 30090740, 331320242, 3975842904, 51689500874]
  have hm0 : (endpointMoment 0).eval (-11)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-11)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-11)=34 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-11)=136 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-11)=922 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-11)=5532 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-11)=41386 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-11)=331088 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-11)=3009074 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-11)=30090740 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-11)=331320242 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-11)=3975842904 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-11)=51689500874 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+j.val)).eval (-11)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_7_12 :
    (polynomialHankel 7).eval (-12)=524914358107582958728642560 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    18, (18/7), 1, 0, 0, 0, 0;
    72, (180/7), (156/17), 1, 0, 0, 0;
    504, 144, (1680/17), (620/43), 1, 0, 0;
    3024, (8424/7), (16608/17), (9228/43), (22902/1093), 1, 0;
    22896, (68688/7), (175752/17), (126600/43), (418914/1093), (1604446/48991), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 36, 144, 1008, 6048, 45792;
    0, 28, 72, 720, 4032, 33696, 274752;
    0, 0, (1224/7), (11232/7), 17280, (1195776/7), (12654144/7);
    0, 0, 0, (37152/17), (535680/17), (7972992/17), (109382400/17);
    0, 0, 0, 0, (3777408/43), (79149312/43), (1447766784/43);
    0, 0, 0, 0, 0, (3047632128/1093), (99809376768/1093);
    0, 0, 0, 0, 0, 0, (4906053204480/48991)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 36, 144, 1008, 6048, 45792;
    4, 36, 144, 1008, 6048, 45792, 366336;
    36, 144, 1008, 6048, 45792, 366336, 3338496;
    144, 1008, 6048, 45792, 366336, 3338496, 33384960;
    1008, 6048, 45792, 366336, 3338496, 33384960, 367732224;
    6048, 45792, 366336, 3338496, 33384960, 367732224, 4412786688;
    45792, 366336, 3338496, 33384960, 367732224, 4412786688, 57372198912]
  have hm0 : (endpointMoment 0).eval (-12)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-12)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-12)=36 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-12)=144 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-12)=1008 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-12)=6048 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-12)=45792 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-12)=366336 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-12)=3338496 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-12)=33384960 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-12)=367732224 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-12)=4412786688 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-12)=57372198912 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+j.val)).eval (-12)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_7_0 :
    (polynomialBorder 7).eval (0)=22368712804584652800000 := by
  rw [polynomialBorder_eval 7 (by norm_num)]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    6, 6, 1, 0, 0, 0, 0;
    24, 36, 12, 1, 0, 0, 0;
    120, 240, 120, 20, 1, 0, 0;
    720, 1800, 1200, 300, 30, 1, 0;
    5040, 15120, 12600, 4200, 630, 42, 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 12, 48, 240, 1440, 80640;
    0, 4, 24, 144, 960, 7200, 564480;
    0, 0, 24, 288, 2880, 28800, 3386880;
    0, 0, 0, 288, 5760, 86400, 16934400;
    0, 0, 0, 0, 5760, 172800, 67737600;
    0, 0, 0, 0, 0, 172800, 203212800;
    0, 0, 0, 0, 0, 0, 406425600]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 12, 48, 240, 1440, 80640;
    4, 12, 48, 240, 1440, 10080, 725760;
    12, 48, 240, 1440, 10080, 80640, 7257600;
    48, 240, 1440, 10080, 80640, 725760, 79833600;
    240, 1440, 10080, 80640, 725760, 7257600, 958003200;
    1440, 10080, 80640, 725760, 7257600, 79833600, 12454041600;
    10080, 80640, 725760, 7257600, 79833600, 958003200, 174356582400]
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
  have hm12 : (endpointMoment 12).eval (0)=12454041600 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (0)=174356582400 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+borderColumn 7 j)).eval (0)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_7_1 :
    (polynomialBorder 7).eval (-1)=1053534291389574197280768 := by
  rw [polynomialBorder_eval 7 (by norm_num)]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    7, (14/3), 1, 0, 0, 0, 0;
    28, (85/3), (19/2), 1, 0, 0, 0;
    141, 188, (432/5), (464/27), 1, 0, 0;
    846, (4231/3), (4072/5), (19144/81), (664477/24432), 1, 0;
    5923, 11846, (41091/5), (28052/9), (2182791/4072), (14212472166/363619027), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 14, 56, 282, 1692, 94768;
    0, 6, 28, 170, 1128, 8462, 663378;
    0, 0, (160/3), (1520/3), 4608, (130304/3), 4770000;
    0, 0, 0, 648, 11136, 153152, 27056328;
    0, 0, 0, 0, (521216/45), (42526528/135), (996058304/9);
    0, 0, 0, 0, 0, (1454476108/4581), (505338442564/1527);
    0, 0, 0, 0, 0, 0, (251182148787873792/363619027)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 14, 56, 282, 1692, 94768;
    4, 14, 56, 282, 1692, 11846, 852914;
    14, 56, 282, 1692, 11846, 94768, 8529140;
    56, 282, 1692, 11846, 94768, 852914, 93820542;
    282, 1692, 11846, 94768, 852914, 8529140, 1125846504;
    1692, 11846, 94768, 852914, 8529140, 93820542, 14636004554;
    11846, 94768, 852914, 8529140, 93820542, 1125846504, 204904063756]
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
  have hm12 : (endpointMoment 12).eval (-1)=14636004554 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-1)=204904063756 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+borderColumn 7 j)).eval (-1)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_7_2 :
    (polynomialBorder 7).eval (-2)=5500863238860464751378432 := by
  rw [polynomialBorder_eval 7 (by norm_num)]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    8, 4, 1, 0, 0, 0, 0;
    32, 25, (82/9), 1, 0, 0, 0;
    164, 164, (740/9), (14740/863), 1, 0, 0;
    984, 1232, (6896/9), 236, (2449194/91391), 1, 0;
    6896, 10344, (22988/3), (2692920/863), (48244548/91391), (2838134448/76042643), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 16, 64, 328, 1968, 110336;
    0, 8, 32, 200, 1312, 9856, 772384;
    0, 0, 72, 656, 5920, 55168, 5958336;
    0, 0, 0, (6904/9), (117920/9), (1629344/9), (96326432/3);
    0, 0, 0, 0, (11698048/863), 363264, (110243057664/863);
    0, 0, 0, 0, 0, (38933833216/91391), (37853637527040/91391);
    0, 0, 0, 0, 0, 0, (81969249827570688/76042643)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 16, 64, 328, 1968, 110336;
    4, 16, 64, 328, 1968, 13792, 993056;
    16, 64, 328, 1968, 13792, 110336, 9930560;
    64, 328, 1968, 13792, 110336, 993056, 109236224;
    328, 1968, 13792, 110336, 993056, 9930560, 1310834688;
    1968, 13792, 110336, 993056, 9930560, 109236224, 17040851072;
    13792, 110336, 993056, 9930560, 109236224, 1310834688, 238571915008]
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
  have hm12 : (endpointMoment 12).eval (-2)=17040851072 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-2)=238571915008 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+borderColumn 7 j)).eval (-2)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_7_3 :
    (polynomialBorder 7).eval (-3)=23327548765433510164955136 := by
  rw [polynomialBorder_eval 7 (by norm_num)]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    9, (18/5), 1, 0, 0, 0, 0;
    36, (117/5), 9, 1, 0, 0, 0;
    189, (756/5), 82, 17, 1, 0, 0;
    1134, (5697/5), 764, 237, (493/19), 1, 0;
    7965, 9558, 7635, 3153, (9627/19), (239682/6773), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 18, 72, 378, 2268, 127440;
    0, 10, 36, 234, 1512, 11394, 892242;
    0, 0, (432/5), (3888/5), (35424/5), (330048/5), (35560944/5);
    0, 0, 0, 864, 14688, 204768, 36707904;
    0, 0, 0, 0, 16416, 425952, 147979872;
    0, 0, 0, 0, 0, (11703744/19), (10457211456/19);
    0, 0, 0, 0, 0, 0, (10465359335424/6773)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 18, 72, 378, 2268, 127440;
    4, 18, 72, 378, 2268, 15930, 1147122;
    18, 72, 378, 2268, 15930, 127440, 11471220;
    72, 378, 2268, 15930, 127440, 1147122, 126183906;
    378, 2268, 15930, 127440, 1147122, 11471220, 1514206872;
    2268, 15930, 127440, 1147122, 11471220, 126183906, 19684690794;
    15930, 127440, 1147122, 11471220, 126183906, 1514206872, 275585671116]
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
  have hm12 : (endpointMoment 12).eval (-3)=19684690794 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-3)=275585671116 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+borderColumn 7 j)).eval (-3)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_7_4 :
    (polynomialBorder 7).eval (-4)=77670408430739826898108416 := by
  rw [polynomialBorder_eval 7 (by norm_num)]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    10, (10/3), 1, 0, 0, 0, 0;
    40, (68/3), (332/37), 1, 0, 0, 0;
    216, 144, (3072/37), (6252/371), 1, 0, 0;
    1296, (3272/3), (28736/37), (263812/1113), (1475842/59231), 1, 0;
    9136, 9136, (287976/37), (1177224/371), (28425246/59231), (20309356962/594681673), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 20, 80, 432, 2592, 146176;
    0, 12, 40, 272, 1728, 13088, 1023744;
    0, 0, (296/3), (2656/3), 8192, (229888/3), 8286720;
    0, 0, 0, (35616/37), (600192/37), (8441984/37), (1530475008/37);
    0, 0, 0, 0, (7581568/371), (188907776/371), (64256219136/371);
    0, 0, 0, 0, 0, (152238508288/177693), (42805253785600/59231);
    0, 0, 0, 0, 0, 0, (1157379276018438144/594681673)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 20, 80, 432, 2592, 146176;
    4, 20, 80, 432, 2592, 18272, 1316096;
    20, 80, 432, 2592, 18272, 146176, 13160960;
    80, 432, 2592, 18272, 146176, 1316096, 144772608;
    432, 2592, 18272, 146176, 1316096, 13160960, 1737271296;
    2592, 18272, 146176, 1316096, 13160960, 144772608, 22584535040;
    18272, 146176, 1316096, 13160960, 144772608, 1737271296, 316183490560]
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
  have hm12 : (endpointMoment 12).eval (-4)=22584535040 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-4)=316183490560 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+borderColumn 7 j)).eval (-4)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_7_5 :
    (polynomialBorder 7).eval (-5)=214744837610802040012800000 := by
  rw [polynomialBorder_eval 7 (by norm_num)]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    11, (22/7), 1, 0, 0, 0, 0;
    44, (157/7), (431/48), 1, 0, 0, 0;
    245, 140, (1015/12), (53380/3209), 1, 0, 0;
    1470, (7475/7), (4775/6), (757000/3209), (6157635/257162), 1, 0;
    10415, (62490/7), (16025/2), (10191000/3209), (58431480/128581), (6000550182/179279371), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 22, 88, 490, 2940, 166640;
    0, 14, 44, 314, 1960, 14950, 1167730;
    0, 0, (768/7), (6896/7), 9280, (611200/7), (66549360/7);
    0, 0, 0, (3209/3), (53380/3), (757000/3), 46229275;
    0, 0, 0, 0, (82291840/3209), (1970443200/3209), (654513470400/3209);
    0, 0, 0, 0, 0, (143423496800/128581), (117157774360800/128581);
    0, 0, 0, 0, 0, 0, (409593272420505600/179279371)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 22, 88, 490, 2940, 166640;
    4, 22, 88, 490, 2940, 20830, 1501010;
    22, 88, 490, 2940, 20830, 166640, 15010100;
    88, 490, 2940, 20830, 166640, 1501010, 165117350;
    490, 2940, 20830, 166640, 1501010, 15010100, 1981408200;
    2940, 20830, 166640, 1501010, 15010100, 165117350, 25758337850;
    20830, 166640, 1501010, 15010100, 165117350, 1981408200, 360616729900]
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
  have hm12 : (endpointMoment 12).eval (-5)=25758337850 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-5)=360616729900 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+borderColumn 7 j)).eval (-5)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_7_6 :
    (polynomialBorder 7).eval (-6)=518916446351353605078908928 := by
  rw [polynomialBorder_eval 7 (by norm_num)]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    12, 3, 1, 0, 0, 0, 0;
    48, (45/2), 9, 1, 0, 0, 0;
    276, 138, (432/5), (180/11), 1, 0, 0;
    1656, 1062, (4092/5), (2572/11), (11774/509), 1, 0;
    11808, 8856, (41436/5), (34792/11), (220552/509), (836917/25279), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 24, 96, 552, 3312, 188928;
    0, 16, 48, 360, 2208, 16992, 1325088;
    0, 0, 120, 1080, 10368, 98208, 10787040;
    0, 0, 0, 1188, 19440, 277776, 51373008;
    0, 0, 0, 0, (1759104/55), (40690944/55), (2644586496/11);
    0, 0, 0, 0, 0, (698913792/509), (561751331328/509);
    0, 0, 0, 0, 0, 0, (65474924327424/25279)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 24, 96, 552, 3312, 188928;
    4, 24, 96, 552, 3312, 23616, 1702944;
    24, 96, 552, 3312, 23616, 188928, 17029440;
    96, 552, 3312, 23616, 188928, 1702944, 187339392;
    552, 3312, 23616, 188928, 1702944, 17029440, 2248072704;
    3312, 23616, 188928, 1702944, 17029440, 187339392, 29225038464;
    23616, 188928, 1702944, 17029440, 187339392, 2248072704, 409150538496]
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
  have hm12 : (endpointMoment 12).eval (-6)=29225038464 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-6)=409150538496 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+borderColumn 7 j)).eval (-6)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_7_7 :
    (polynomialBorder 7).eval (-7)=1135317886538250323169902592 := by
  rw [polynomialBorder_eval 7 (by norm_num)]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    13, (26/9), 1, 0, 0, 0, 0;
    52, (205/9), (659/73), 1, 0, 0, 0;
    309, (412/3), (6450/73), (16105/1003), 1, 0, 0;
    1854, (9613/9), (61532/73), (695269/3009), (27742021/1233529), 1, 0;
    13321, (26642/3), (627123/73), (3147585/1003), (514357977/1233529), (3088812197898/93836955313), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 26, 104, 618, 3708, 213136;
    0, 18, 52, 410, 2472, 19226, 1496754;
    0, 0, (1168/9), (10544/9), (34400/3), (984512/9), 12135536;
    0, 0, 0, (96288/73), (1546080/73), (22248608/73), (4149200832/73);
    0, 0, 0, 0, (39472928/1003), (887744672/1003), (283338529824/1003);
    0, 0, 0, 0, 0, (6005565140032/3700587), (1597658334475840/1233529);
    0, 0, 0, 0, 0, 0, (270680877337038594048/93836955313)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 26, 104, 618, 3708, 213136;
    4, 26, 104, 618, 3708, 26642, 1923026;
    26, 104, 618, 3708, 26642, 213136, 19230260;
    104, 618, 3708, 26642, 213136, 1923026, 211566474;
    618, 3708, 26642, 213136, 1923026, 19230260, 2538797688;
    3708, 26642, 213136, 1923026, 19230260, 211566474, 33004605242;
    26642, 213136, 1923026, 19230260, 211566474, 2538797688, 462064473388]
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
  have hm12 : (endpointMoment 12).eval (-7)=33004605242 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-7)=462064473388 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+borderColumn 7 j)).eval (-7)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_7_8 :
    (polynomialBorder 7).eval (-8)=2303445200638034734340898816 := by
  rw [polynomialBorder_eval 7 (by norm_num)]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    14, (14/5), 1, 0, 0, 0, 0;
    56, (116/5), (788/87), 1, 0, 0, 0;
    344, (688/5), (7864/87), (62588/3979), 1, 0, 0;
    2064, (5416/5), (75568/87), (906788/3979), (32577186/1481023), 1, 0;
    14960, 8976, (258520/29), (12355512/3979), (599618994/1481023), (353949510042/10784400593), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 28, 112, 688, 4128, 239360;
    0, 20, 56, 464, 2752, 21664, 1683712;
    0, 0, (696/5), (6304/5), (62912/5), (604544/5), (67794432/5);
    0, 0, 0, (127328/87), (2002816/87), (29017216/87), (1817069056/29);
    0, 0, 0, 0, (189570944/3979), (4169879808/3979), (1313079502848/3979);
    0, 0, 0, 0, 0, (2760806551808/1481023), (2199193227466752/1481023);
    0, 0, 0, 0, 0, 0, (34324008235902111744/10784400593)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 28, 112, 688, 4128, 239360;
    4, 28, 112, 688, 4128, 29920, 2162432;
    28, 112, 688, 4128, 29920, 239360, 21624320;
    112, 688, 4128, 29920, 239360, 2162432, 237933056;
    688, 4128, 29920, 239360, 2162432, 21624320, 2855196672;
    4128, 29920, 239360, 2162432, 21624320, 237933056, 37118081024;
    29920, 239360, 2162432, 21624320, 237933056, 2855196672, 519653134336]
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
  have hm12 : (endpointMoment 12).eval (-8)=37118081024 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-8)=519653134336 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+borderColumn 7 j)).eval (-8)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_7_9 :
    (polynomialBorder 7).eval (-9)=4406591830031391449432457216 := by
  rw [polynomialBorder_eval 7 (by norm_num)]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    15, (30/11), 1, 0, 0, 0, 0;
    60, (261/11), (309/34), 1, 0, 0, 0;
    381, (1524/11), (1572/17), (5896/383), 1, 0, 0;
    2286, (12159/11), (15216/17), (85992/383), (815613/37724), 1, 0;
    16731, 9126, (157311/17), (1174692/383), (7471827/18862), (1501724982/45818603), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 30, 120, 762, 4572, 267696;
    0, 22, 60, 522, 3048, 24318, 1886994;
    0, 0, (1632/11), (14832/11), (150912/11), (1460736/11), (165682800/11);
    0, 0, 0, (27576/17), (424512/17), (6191424/17), (1170584568/17);
    0, 0, 0, 0, (21729024/383), (469793088/383), (146583667008/383);
    0, 0, 0, 0, 0, (19793636496/9431), (15783464958480/9431);
    0, 0, 0, 0, 0, 0, (160130065965041664/45818603)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 30, 120, 762, 4572, 267696;
    4, 30, 120, 762, 4572, 33462, 2422386;
    30, 120, 762, 4572, 33462, 267696, 24223860;
    120, 762, 4572, 33462, 267696, 2422386, 266580558;
    762, 4572, 33462, 267696, 2422386, 24223860, 3198966696;
    4572, 33462, 267696, 2422386, 24223860, 266580558, 41587629930;
    33462, 267696, 2422386, 24223860, 266580558, 3198966696, 582226819020]
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
  have hm12 : (endpointMoment 12).eval (-9)=41587629930 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-9)=582226819020 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+borderColumn 7 j)).eval (-9)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_7_10 :
    (polynomialBorder 7).eval (-10)=8043850755570091740364800000 := by
  rw [polynomialBorder_eval 7 (by norm_num)]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    16, (8/3), 1, 0, 0, 0, 0;
    64, (73/3), (538/59), 1, 0, 0, 0;
    420, 140, (5580/59), (66460/4413), 1, 0, 0;
    2520, (3400/3), (54400/59), (2927300/13239), (9786310/458697), 1, 0;
    18640, 9320, (566700/59), (4451800/1471), (59631420/152899), (8203394772/250429541), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 32, 128, 840, 5040, 298240;
    0, 24, 64, 584, 3360, 27200, 2107680;
    0, 0, (472/3), (4304/3), 14880, (435200/3), 16649280;
    0, 0, 0, (105912/59), (1595040/59), (23418400/59), (4452405600/59);
    0, 0, 0, 0, (97855360/1471), (6263238400/4413), (647871385600/1471);
    0, 0, 0, 0, 0, (3205498124800/1376091), (854301538777600/458697);
    0, 0, 0, 0, 0, 0, (958901733824025600/250429541)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 32, 128, 840, 5040, 298240;
    4, 32, 128, 840, 5040, 37280, 2704160;
    32, 128, 840, 5040, 37280, 298240, 27041600;
    128, 840, 5040, 37280, 298240, 2704160, 297657600;
    840, 5040, 37280, 298240, 2704160, 27041600, 3571891200;
    5040, 37280, 298240, 2704160, 27041600, 297657600, 46436585600;
    37280, 298240, 2704160, 27041600, 297657600, 3571891200, 650112198400]
  have hm0 : (endpointMoment 0).eval (-10)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-10)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-10)=32 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-10)=128 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-10)=840 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-10)=5040 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-10)=37280 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-10)=298240 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-10)=2704160 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-10)=27041600 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-10)=297657600 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-10)=3571891200 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-10)=46436585600 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-10)=650112198400 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+borderColumn 7 j)).eval (-10)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_7_11 :
    (polynomialBorder 7).eval (-11)=14133825941060231083472191488 := by
  rw [polynomialBorder_eval 7 (by norm_num)]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    17, (34/13), 1, 0, 0, 0, 0;
    68, 25, (247/27), 1, 0, 0, 0;
    461, (1844/13), (13054/135), (24649/1673), 1, 0, 0;
    2766, (15161/13), (128164/135), (364345/1673), (424627671/20107261), 1, 0;
    20693, (124158/13), (448519/45), (4993833/1673), (7758890133/20107261), (26326773728946/803829329117), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 34, 136, 922, 5532, 331088;
    0, 26, 68, 650, 3688, 30322, 2346898;
    0, 0, (2160/13), 1520, (208864/13), (2050624/13), (238214640/13);
    0, 0, 0, (53536/27), (788768/27), (11659040/27), (742511552/9);
    0, 0, 0, 0, (643432352/8365), (13588085472/8365), (841359772128/1673);
    0, 0, 0, 0, 0, (51445077063488/20107261), (41277722573883072/20107261);
    0, 0, 0, 0, 0, 0, (3369766698136384745472/803829329117)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 34, 136, 922, 5532, 331088;
    4, 34, 136, 922, 5532, 41386, 3009074;
    34, 136, 922, 5532, 41386, 331088, 30090740;
    136, 922, 5532, 41386, 331088, 3009074, 331320242;
    922, 5532, 41386, 331088, 3009074, 30090740, 3975842904;
    5532, 41386, 331088, 3009074, 30090740, 331320242, 51689500874;
    41386, 331088, 3009074, 30090740, 331320242, 3975842904, 723653012236]
  have hm0 : (endpointMoment 0).eval (-11)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-11)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-11)=34 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-11)=136 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-11)=922 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-11)=5532 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-11)=41386 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-11)=331088 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-11)=3009074 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-11)=30090740 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-11)=331320242 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-11)=3975842904 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-11)=51689500874 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-11)=723653012236 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+borderColumn 7 j)).eval (-11)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_7_12 :
    (polynomialBorder 7).eval (-12)=24062242845117270548495204352 := by
  rw [polynomialBorder_eval 7 (by norm_num)]
  let L : Matrix (Fin 7) (Fin 7) ℚ := !![1, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0;
    18, (18/7), 1, 0, 0, 0, 0;
    72, (180/7), (156/17), 1, 0, 0, 0;
    504, 144, (1680/17), (620/43), 1, 0, 0;
    3024, (8424/7), (16608/17), (9228/43), (22902/1093), 1, 0;
    22896, (68688/7), (175752/17), (126600/43), (418914/1093), (1604446/48991), 1]
  let U : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 36, 144, 1008, 6048, 366336;
    0, 28, 72, 720, 4032, 33696, 2605824;
    0, 0, (1224/7), (11232/7), 17280, (1195776/7), (140631552/7);
    0, 0, 0, (37152/17), (535680/17), (7972992/17), (1529860608/17);
    0, 0, 0, 0, (3777408/43), (79149312/43), (24508790784/43);
    0, 0, 0, 0, 0, (3047632128/1093), (2454919280640/1093);
    0, 0, 0, 0, 0, 0, (224895055343616/48991)]
  let A : Matrix (Fin 7) (Fin 7) ℚ := !![2, 4, 36, 144, 1008, 6048, 366336;
    4, 36, 144, 1008, 6048, 45792, 3338496;
    36, 144, 1008, 6048, 45792, 366336, 33384960;
    144, 1008, 6048, 45792, 366336, 3338496, 367732224;
    1008, 6048, 45792, 366336, 3338496, 33384960, 4412786688;
    6048, 45792, 366336, 3338496, 33384960, 367732224, 57372198912;
    45792, 366336, 3338496, 33384960, 367732224, 4412786688, 803210784768]
  have hm0 : (endpointMoment 0).eval (-12)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-12)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-12)=36 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-12)=144 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-12)=1008 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-12)=6048 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-12)=45792 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-12)=366336 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-12)=3338496 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-12)=33384960 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-12)=367732224 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-12)=4412786688 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-12)=57372198912 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-12)=803210784768 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have he : (Matrix.of (fun i j : Fin 7 =>
      (endpointMoment (i.val+borderColumn 7 j)).eval (-12)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem table_H_7 : polynomialHankel 7=C (19327352832)*appendixG12 := by
  apply eq_of_natDegree_lt_card_of_eval_eq (f:=fun i : Fin 13 => -(i.val:ℚ))
  · intro i j h
    apply Fin.ext
    exact_mod_cast neg_inj.mp h
  · intro i
    fin_cases i <;>
      norm_num [sample_H_7_0,sample_H_7_1,sample_H_7_2,sample_H_7_3,sample_H_7_4,sample_H_7_5,sample_H_7_6,sample_H_7_7,sample_H_7_8,sample_H_7_9,sample_H_7_10,sample_H_7_11,sample_H_7_12,appendixG12]
  · apply max_lt
    · rw [polynomialHankel_natDegree]
      norm_num [hankelDegree]
    · unfold appendixG12
      compute_degree!

theorem table_J_7 : polynomialBorder 7=C (1082331758592)*appendixG12-X*(C (231928233984)*appendixG11) := by
  apply eq_of_natDegree_lt_card_of_eval_eq (f:=fun i : Fin 13 => -(i.val:ℚ))
  · intro i j h
    apply Fin.ext
    exact_mod_cast neg_inj.mp h
  · intro i
    fin_cases i <;>
      norm_num [sample_J_7_0,sample_J_7_1,sample_J_7_2,sample_J_7_3,sample_J_7_4,sample_J_7_5,sample_J_7_6,sample_J_7_7,sample_J_7_8,sample_J_7_9,sample_J_7_10,sample_J_7_11,sample_J_7_12,appendixG12,appendixG11]
  · apply max_lt
    · rw [polynomialBorder_natDegree 7 (by norm_num)]
      norm_num [hankelDegree]
    · unfold appendixG12 appendixG11
      compute_degree!

theorem recurrenceFamily_appendix_12 : recurrenceFamily 12=appendixG12 := by
  have h := recurrenceFamily_hankel_eq (n:=7) (by norm_num) appendixG12
    (19327352832) (by norm_num) appendixG12_monic table_H_7
  simpa only [hankelDegree,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceMul] using h

theorem recurrenceFamily_appendix_11 : recurrenceFamily 11=appendixG11 := by
  have h := recurrenceFamily_numerator_eq (n:=7) (by norm_num) appendixG11
    (231928233984) (by norm_num) appendixG11_monic (by
      rw [polynomialNumerator,table_H_7,table_J_7]
      norm_num only [Nat.cast_ofNat,map_ofNat,map_neg]
      ring)
  simpa only [hankelDegree,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using h

end OscillatoryRecurrence
