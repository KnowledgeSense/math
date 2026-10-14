import OscillatoryRecurrence.AppendixPolynomials

noncomputable section
open Polynomial
open scoped Matrix BigOperators
namespace OscillatoryRecurrence
set_option maxHeartbeats 2000000

theorem sample_H_8_0 :
    (polynomialHankel 8).eval (0)=162343170050553576161280000000 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    6, 6, 1, 0, 0, 0, 0, 0;
    24, 36, 12, 1, 0, 0, 0, 0;
    120, 240, 120, 20, 1, 0, 0, 0;
    720, 1800, 1200, 300, 30, 1, 0, 0;
    5040, 15120, 12600, 4200, 630, 42, 1, 0;
    40320, 141120, 141120, 58800, 11760, 1176, 56, 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 12, 48, 240, 1440, 10080, 80640;
    0, 4, 24, 144, 960, 7200, 60480, 564480;
    0, 0, 24, 288, 2880, 28800, 302400, 3386880;
    0, 0, 0, 288, 5760, 86400, 1209600, 16934400;
    0, 0, 0, 0, 5760, 172800, 3628800, 67737600;
    0, 0, 0, 0, 0, 172800, 7257600, 203212800;
    0, 0, 0, 0, 0, 0, 7257600, 406425600;
    0, 0, 0, 0, 0, 0, 0, 406425600]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 12, 48, 240, 1440, 10080, 80640;
    4, 12, 48, 240, 1440, 10080, 80640, 725760;
    12, 48, 240, 1440, 10080, 80640, 725760, 7257600;
    48, 240, 1440, 10080, 80640, 725760, 7257600, 79833600;
    240, 1440, 10080, 80640, 725760, 7257600, 79833600, 958003200;
    1440, 10080, 80640, 725760, 7257600, 79833600, 958003200, 12454041600;
    10080, 80640, 725760, 7257600, 79833600, 958003200, 12454041600, 174356582400;
    80640, 725760, 7257600, 79833600, 958003200, 12454041600, 174356582400, 2615348736000]
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
  have hm14 : (endpointMoment 14).eval (0)=2615348736000 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (0)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_1 :
    (polynomialHankel 8).eval (-1)=16333275924189313905124360323072 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    7, (14/3), 1, 0, 0, 0, 0, 0;
    28, (85/3), (19/2), 1, 0, 0, 0, 0;
    141, 188, (432/5), (464/27), 1, 0, 0, 0;
    846, (4231/3), (4072/5), (19144/81), (664477/24432), 1, 0, 0;
    5923, 11846, (41091/5), (28052/9), (2182791/4072), (14212472166/363619027), 1, 0;
    47384, 110563, (178875/2), (1127347/27), (77817055/8144), (379003831923/363619027), (54510014927924/1041239414515), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 14, 56, 282, 1692, 11846, 94768;
    0, 6, 28, 170, 1128, 8462, 71076, 663378;
    0, 0, (160/3), (1520/3), 4608, (130304/3), 438304, 4770000;
    0, 0, 0, 648, 11136, 153152, 2019744, 27056328;
    0, 0, 0, 0, (521216/45), (42526528/135), (93132416/15), (996058304/9);
    0, 0, 0, 0, 0, (1454476108/4581), (6316654296/509), (505338442564/1527);
    0, 0, 0, 0, 0, 0, (4798031222085120/363619027), (251182148787873792/363619027);
    0, 0, 0, 0, 0, 0, 0, (845086032534500061696/1041239414515)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 14, 56, 282, 1692, 11846, 94768;
    4, 14, 56, 282, 1692, 11846, 94768, 852914;
    14, 56, 282, 1692, 11846, 94768, 852914, 8529140;
    56, 282, 1692, 11846, 94768, 852914, 8529140, 93820542;
    282, 1692, 11846, 94768, 852914, 8529140, 93820542, 1125846504;
    1692, 11846, 94768, 852914, 8529140, 93820542, 1125846504, 14636004554;
    11846, 94768, 852914, 8529140, 93820542, 1125846504, 14636004554, 204904063756;
    94768, 852914, 8529140, 93820542, 1125846504, 14636004554, 204904063756, 3073560956342]
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
  have hm14 : (endpointMoment 14).eval (-1)=3073560956342 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-1)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_2 :
    (polynomialHankel 8).eval (-2)=159482440527462581436984462409728 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    8, 4, 1, 0, 0, 0, 0, 0;
    32, 25, (82/9), 1, 0, 0, 0, 0;
    164, 164, (740/9), (14740/863), 1, 0, 0, 0;
    984, 1232, (6896/9), 236, (2449194/91391), 1, 0, 0;
    6896, 10344, (22988/3), (2692920/863), (48244548/91391), (2838134448/76042643), 1, 0;
    55168, 96548, (248264/3), (36122412/863), (861273888/91391), (73932885795/76042643), (17788465674386/362636573515), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 16, 64, 328, 1968, 13792, 110336;
    0, 8, 32, 200, 1312, 9856, 82752, 772384;
    0, 0, 72, 656, 5920, 55168, 551712, 5958336;
    0, 0, 0, (6904/9), (117920/9), (1629344/9), (7181120/3), (96326432/3);
    0, 0, 0, 0, (11698048/863), 363264, (6175302144/863), (110243057664/863);
    0, 0, 0, 0, 0, (38933833216/91391), (1453124837376/91391), (37853637527040/91391);
    0, 0, 0, 0, 0, 0, (1671029330757120/76042643), (81969249827570688/76042643);
    0, 0, 0, 0, 0, 0, 0, (515727767770820780544/362636573515)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 16, 64, 328, 1968, 13792, 110336;
    4, 16, 64, 328, 1968, 13792, 110336, 993056;
    16, 64, 328, 1968, 13792, 110336, 993056, 9930560;
    64, 328, 1968, 13792, 110336, 993056, 9930560, 109236224;
    328, 1968, 13792, 110336, 993056, 9930560, 109236224, 1310834688;
    1968, 13792, 110336, 993056, 9930560, 109236224, 1310834688, 17040851072;
    13792, 110336, 993056, 9930560, 109236224, 1310834688, 17040851072, 238571915008;
    110336, 993056, 9930560, 109236224, 1310834688, 17040851072, 238571915008, 3578578725376]
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
  have hm14 : (endpointMoment 14).eval (-2)=3578578725376 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-2)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_3 :
    (polynomialHankel 8).eval (-3)=891581782958888732944291590045696 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    9, (18/5), 1, 0, 0, 0, 0, 0;
    36, (117/5), 9, 1, 0, 0, 0, 0;
    189, (756/5), 82, 17, 1, 0, 0, 0;
    1134, (5697/5), 764, 237, (493/19), 1, 0, 0;
    7965, 9558, 7635, 3153, (9627/19), (239682/6773), 1, 0;
    63720, (446121/5), 82317, 42486, (171273/19), (6051627/6773), (84115864/1768199), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 18, 72, 378, 2268, 15930, 127440;
    0, 10, 36, 234, 1512, 11394, 95580, 892242;
    0, 0, (432/5), (3888/5), (35424/5), (330048/5), 659664, (35560944/5);
    0, 0, 0, 864, 14688, 204768, 2724192, 36707904;
    0, 0, 0, 0, 16416, 425952, 8317728, 147979872;
    0, 0, 0, 0, 0, (11703744/19), (414170496/19), (10457211456/19);
    0, 0, 0, 0, 0, 0, (219992246784/6773), (10465359335424/6773);
    0, 0, 0, 0, 0, 0, 0, (3214918667810304/1768199)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 18, 72, 378, 2268, 15930, 127440;
    4, 18, 72, 378, 2268, 15930, 127440, 1147122;
    18, 72, 378, 2268, 15930, 127440, 1147122, 11471220;
    72, 378, 2268, 15930, 127440, 1147122, 11471220, 126183906;
    378, 2268, 15930, 127440, 1147122, 11471220, 126183906, 1514206872;
    2268, 15930, 127440, 1147122, 11471220, 126183906, 1514206872, 19684690794;
    15930, 127440, 1147122, 11471220, 126183906, 1514206872, 19684690794, 275585671116;
    127440, 1147122, 11471220, 126183906, 1514206872, 19684690794, 275585671116, 4133785071114]
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
  have hm14 : (endpointMoment 14).eval (-3)=4133785071114 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-3)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_4 :
    (polynomialHankel 8).eval (-4)=3452503890673667788719513705381888 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    10, (10/3), 1, 0, 0, 0, 0, 0;
    40, (68/3), (332/37), 1, 0, 0, 0, 0;
    216, 144, (3072/37), (6252/371), 1, 0, 0, 0;
    1296, (3272/3), (28736/37), (263812/1113), (1475842/59231), 1, 0, 0;
    9136, 9136, (287976/37), (1177224/371), (28425246/59231), (20309356962/594681673), 1, 0;
    73088, 85312, (3107520/37), (15942448/371), (502001712/59231), (501624067800/594681673), (251167377608168/5332000562251), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 20, 80, 432, 2592, 18272, 146176;
    0, 12, 40, 272, 1728, 13088, 109632, 1023744;
    0, 0, (296/3), (2656/3), 8192, (229888/3), 767936, 8286720;
    0, 0, 0, (35616/37), (600192/37), (8441984/37), (113013504/37), (1530475008/37);
    0, 0, 0, 0, (7581568/371), (188907776/371), (3638431488/371), (64256219136/371);
    0, 0, 0, 0, 0, (152238508288/177693), (1733065127424/59231), (42805253785600/59231);
    0, 0, 0, 0, 0, 0, (24569858590852608/594681673), (1157379276018438144/594681673);
    0, 0, 0, 0, 0, 0, 0, (11164565320597766836224/5332000562251)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 20, 80, 432, 2592, 18272, 146176;
    4, 20, 80, 432, 2592, 18272, 146176, 1316096;
    20, 80, 432, 2592, 18272, 146176, 1316096, 13160960;
    80, 432, 2592, 18272, 146176, 1316096, 13160960, 144772608;
    432, 2592, 18272, 146176, 1316096, 13160960, 144772608, 1737271296;
    2592, 18272, 146176, 1316096, 13160960, 144772608, 1737271296, 22584535040;
    18272, 146176, 1316096, 13160960, 144772608, 1737271296, 22584535040, 316183490560;
    146176, 1316096, 13160960, 144772608, 1737271296, 22584535040, 316183490560, 4742752391168]
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
  have hm14 : (endpointMoment 14).eval (-4)=4742752391168 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-4)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_5 :
    (polynomialHankel 8).eval (-5)=10754193667199597767903150080000000 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    11, (22/7), 1, 0, 0, 0, 0, 0;
    44, (157/7), (431/48), 1, 0, 0, 0, 0;
    245, 140, (1015/12), (53380/3209), 1, 0, 0, 0;
    1470, (7475/7), (4775/6), (757000/3209), (6157635/257162), 1, 0, 0;
    10415, (62490/7), (16025/2), (10191000/3209), (58431480/128581), (6000550182/179279371), 1, 0;
    83320, (583865/7), (1386445/16), (138687825/3209), (2045354595/257162), (146447217951/179279371), (3555497156428/75684809243), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 22, 88, 490, 2940, 20830, 166640;
    0, 14, 44, 314, 1960, 14950, 124980, 1167730;
    0, 0, (768/7), (6896/7), 9280, (611200/7), (6153600/7), (66549360/7);
    0, 0, 0, (3209/3), (53380/3), (757000/3), 3397000, 46229275;
    0, 0, 0, 0, (82291840/3209), (1970443200/3209), (37396147200/3209), (654513470400/3209);
    0, 0, 0, 0, 0, (143423496800/128581), (4800440145600/128581), (117157774360800/128581);
    0, 0, 0, 0, 0, 0, (8718890024793600/179279371), (409593272420505600/179279371);
    0, 0, 0, 0, 0, 0, 0, (178055525938663180800/75684809243)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 22, 88, 490, 2940, 20830, 166640;
    4, 22, 88, 490, 2940, 20830, 166640, 1501010;
    22, 88, 490, 2940, 20830, 166640, 1501010, 15010100;
    88, 490, 2940, 20830, 166640, 1501010, 15010100, 165117350;
    490, 2940, 20830, 166640, 1501010, 15010100, 165117350, 1981408200;
    2940, 20830, 166640, 1501010, 15010100, 165117350, 1981408200, 25758337850;
    20830, 166640, 1501010, 15010100, 165117350, 1981408200, 25758337850, 360616729900;
    166640, 1501010, 15010100, 165117350, 1981408200, 25758337850, 360616729900, 5409251104750]
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
  have hm14 : (endpointMoment 14).eval (-5)=5409251104750 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-5)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_6 :
    (polynomialHankel 8).eval (-6)=29259358901059189290771477568684032 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    12, 3, 1, 0, 0, 0, 0, 0;
    48, (45/2), 9, 1, 0, 0, 0, 0;
    276, 138, (432/5), (180/11), 1, 0, 0, 0;
    1656, 1062, (4092/5), (2572/11), (11774/509), 1, 0, 0;
    11808, 8856, (41436/5), (34792/11), (220552/509), (836917/25279), 1, 0;
    94464, 82818, 89892, (475676/11), (3826080/509), (40635947/50558), (4736322651/100891715), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 24, 96, 552, 3312, 23616, 188928;
    0, 16, 48, 360, 2208, 16992, 141696, 1325088;
    0, 0, 120, 1080, 10368, 98208, 994464, 10787040;
    0, 0, 0, 1188, 19440, 277776, 3757536, 51373008;
    0, 0, 0, 0, (1759104/55), (40690944/55), (762227712/55), (2644586496/11);
    0, 0, 0, 0, 0, (698913792/509), (23139081216/509), (561751331328/509);
    0, 0, 0, 0, 0, 0, (1394727068160/25279), (65474924327424/25279);
    0, 0, 0, 0, 0, 0, 0, (267059880817484544/100891715)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 24, 96, 552, 3312, 23616, 188928;
    4, 24, 96, 552, 3312, 23616, 188928, 1702944;
    24, 96, 552, 3312, 23616, 188928, 1702944, 17029440;
    96, 552, 3312, 23616, 188928, 1702944, 17029440, 187339392;
    552, 3312, 23616, 188928, 1702944, 17029440, 187339392, 2248072704;
    3312, 23616, 188928, 1702944, 17029440, 187339392, 2248072704, 29225038464;
    23616, 188928, 1702944, 17029440, 187339392, 2248072704, 29225038464, 409150538496;
    188928, 1702944, 17029440, 187339392, 2248072704, 29225038464, 409150538496, 6137258637312]
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
  have hm14 : (endpointMoment 14).eval (-6)=6137258637312 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-6)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_7 :
    (polynomialHankel 8).eval (-7)=72924549373232439596316223265046528 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    13, (26/9), 1, 0, 0, 0, 0, 0;
    52, (205/9), (659/73), 1, 0, 0, 0, 0;
    309, (412/3), (6450/73), (16105/1003), 1, 0, 0, 0;
    1854, (9613/9), (61532/73), (695269/3009), (27742021/1233529), 1, 0, 0;
    13321, (26642/3), (627123/73), (3147585/1003), (514357977/1233529), (3088812197898/93836955313), 1, 0;
    106568, 83153, (6826239/73), (43220842/1003), (8854329057/1233529), (74890234428555/93836955313), (8391644262681008/178883837066455), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 26, 104, 618, 3708, 26642, 213136;
    0, 18, 52, 410, 2472, 19226, 159852, 1496754;
    0, 0, (1168/9), (10544/9), (34400/3), (984512/9), (3344656/3), 12135536;
    0, 0, 0, (96288/73), (1546080/73), (22248608/73), (302168160/73), (4149200832/73);
    0, 0, 0, 0, (39472928/1003), (887744672/1003), (16459455264/1003), (283338529824/1003);
    0, 0, 0, 0, 0, (6005565140032/3700587), (65894660221824/1233529), (1597658334475840/1233529);
    0, 0, 0, 0, 0, 0, (5770077048415572480/93836955313), (270680877337038594048/93836955313);
    0, 0, 0, 0, 0, 0, 0, (539018087896447744015872/178883837066455)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 26, 104, 618, 3708, 26642, 213136;
    4, 26, 104, 618, 3708, 26642, 213136, 1923026;
    26, 104, 618, 3708, 26642, 213136, 1923026, 19230260;
    104, 618, 3708, 26642, 213136, 1923026, 19230260, 211566474;
    618, 3708, 26642, 213136, 1923026, 19230260, 211566474, 2538797688;
    3708, 26642, 213136, 1923026, 19230260, 211566474, 2538797688, 33004605242;
    26642, 213136, 1923026, 19230260, 211566474, 2538797688, 33004605242, 462064473388;
    213136, 1923026, 19230260, 211566474, 2538797688, 33004605242, 462064473388, 6930968747906]
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
  have hm14 : (endpointMoment 14).eval (-7)=6930968747906 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-7)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_8 :
    (polynomialHankel 8).eval (-8)=171250074916046028275230283447402496 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    14, (14/5), 1, 0, 0, 0, 0, 0;
    56, (116/5), (788/87), 1, 0, 0, 0, 0;
    344, (688/5), (7864/87), (62588/3979), 1, 0, 0, 0;
    2064, (5416/5), (75568/87), (906788/3979), (32577186/1481023), 1, 0, 0;
    14960, 8976, (258520/29), (12355512/3979), (599618994/1481023), (353949510042/10784400593), 1, 0;
    119680, (420928/5), (2824768/29), (170350224/3979), (10258433616/1481023), (8590598544792/10784400593), (7448786509527368/159046407326383), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 28, 112, 688, 4128, 29920, 239360;
    0, 20, 56, 464, 2752, 21664, 179520, 1683712;
    0, 0, (696/5), (6304/5), (62912/5), (604544/5), 1240896, (67794432/5);
    0, 0, 0, (127328/87), (2002816/87), (29017216/87), (131792128/29), (1817069056/29);
    0, 0, 0, 0, (189570944/3979), (4169879808/3979), (76751231232/3979), (1313079502848/3979);
    0, 0, 0, 0, 0, (2760806551808/1481023), (90611074570752/1481023), (2199193227466752/1481023);
    0, 0, 0, 0, 0, 0, (732885844959972864/10784400593), (34324008235902111744/10784400593);
    0, 0, 0, 0, 0, 0, 0, (553781460673283204395008/159046407326383)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 28, 112, 688, 4128, 29920, 239360;
    4, 28, 112, 688, 4128, 29920, 239360, 2162432;
    28, 112, 688, 4128, 29920, 239360, 2162432, 21624320;
    112, 688, 4128, 29920, 239360, 2162432, 21624320, 237933056;
    688, 4128, 29920, 239360, 2162432, 21624320, 237933056, 2855196672;
    4128, 29920, 239360, 2162432, 21624320, 237933056, 2855196672, 37118081024;
    29920, 239360, 2162432, 21624320, 237933056, 2855196672, 37118081024, 519653134336;
    239360, 2162432, 21624320, 237933056, 2855196672, 37118081024, 519653134336, 7794801209344]
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
  have hm14 : (endpointMoment 14).eval (-8)=7794801209344 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-8)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_9 :
    (polynomialHankel 8).eval (-9)=385057798916463611197672435249840128 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    15, (30/11), 1, 0, 0, 0, 0, 0;
    60, (261/11), (309/34), 1, 0, 0, 0, 0;
    381, (1524/11), (1572/17), (5896/383), 1, 0, 0, 0;
    2286, (12159/11), (15216/17), (85992/383), (815613/37724), 1, 0, 0;
    16731, 9126, (157311/17), (1174692/383), (7471827/18862), (1501724982/45818603), 1, 0;
    133848, (943497/11), (3451725/34), (16258119/383), (254485533/37724), (36535798515/45818603), (3861160927012/82692981059), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 30, 120, 762, 4572, 33462, 267696;
    0, 22, 60, 522, 3048, 24318, 200772, 1886994;
    0, 0, (1632/11), (14832/11), (150912/11), (1460736/11), 1372896, (165682800/11);
    0, 0, 0, (27576/17), (424512/17), (6191424/17), (84577824/17), (1170584568/17);
    0, 0, 0, 0, (21729024/383), (469793088/383), (8607544704/383), (146583667008/383);
    0, 0, 0, 0, 0, (19793636496/9431), (648745192224/9431), (15783464958480/9431);
    0, 0, 0, 0, 0, 0, (3429443310478848/45818603), (160130065965041664/45818603);
    0, 0, 0, 0, 0, 0, 0, (337396833009355792896/82692981059)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 30, 120, 762, 4572, 33462, 267696;
    4, 30, 120, 762, 4572, 33462, 267696, 2422386;
    30, 120, 762, 4572, 33462, 267696, 2422386, 24223860;
    120, 762, 4572, 33462, 267696, 2422386, 24223860, 266580558;
    762, 4572, 33462, 267696, 2422386, 24223860, 266580558, 3198966696;
    4572, 33462, 267696, 2422386, 24223860, 266580558, 3198966696, 41587629930;
    33462, 267696, 2422386, 24223860, 266580558, 3198966696, 41587629930, 582226819020;
    267696, 2422386, 24223860, 266580558, 3198966696, 41587629930, 582226819020, 8733411851238]
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
  have hm14 : (endpointMoment 14).eval (-9)=8733411851238 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-9)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_10 :
    (polynomialHankel 8).eval (-10)=836084434782867929348261806080000000 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    16, (8/3), 1, 0, 0, 0, 0, 0;
    64, (73/3), (538/59), 1, 0, 0, 0, 0;
    420, 140, (5580/59), (66460/4413), 1, 0, 0, 0;
    2520, (3400/3), (54400/59), (2927300/13239), (9786310/458697), 1, 0, 0;
    18640, 9320, (566700/59), (4451800/1471), (59631420/152899), (8203394772/250429541), 1, 0;
    149120, 87820, (6243480/59), (185516900/4413), (1012299040/152899), (200226923151/250429541), (8323799772778/179087271173), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 32, 128, 840, 5040, 37280, 298240;
    0, 24, 64, 584, 3360, 27200, 223680, 2107680;
    0, 0, (472/3), (4304/3), 14880, (435200/3), 1511200, 16649280;
    0, 0, 0, (105912/59), (1595040/59), (23418400/59), (320529600/59), (4452405600/59);
    0, 0, 0, 0, (97855360/1471), (6263238400/4413), (38164108800/1471), (647871385600/1471);
    0, 0, 0, 0, 0, (3205498124800/1376091), (11667050342400/152899), (854301538777600/458697);
    0, 0, 0, 0, 0, 0, (20630853639129600/250429541), (958901733824025600/250429541);
    0, 0, 0, 0, 0, 0, 0, (865182564886564108800/179087271173)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 32, 128, 840, 5040, 37280, 298240;
    4, 32, 128, 840, 5040, 37280, 298240, 2704160;
    32, 128, 840, 5040, 37280, 298240, 2704160, 27041600;
    128, 840, 5040, 37280, 298240, 2704160, 27041600, 297657600;
    840, 5040, 37280, 298240, 2704160, 27041600, 297657600, 3571891200;
    5040, 37280, 298240, 2704160, 27041600, 297657600, 3571891200, 46436585600;
    37280, 298240, 2704160, 27041600, 297657600, 3571891200, 46436585600, 650112198400;
    298240, 2704160, 27041600, 297657600, 3571891200, 46436585600, 650112198400, 9751702976000]
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
  have hm14 : (endpointMoment 14).eval (-10)=9751702976000 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-10)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_11 :
    (polynomialHankel 8).eval (-11)=1760186096273245496673856984493064192 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    17, (34/13), 1, 0, 0, 0, 0, 0;
    68, 25, (247/27), 1, 0, 0, 0, 0;
    461, (1844/13), (13054/135), (24649/1673), 1, 0, 0, 0;
    2766, (15161/13), (128164/135), (364345/1673), (424627671/20107261), 1, 0, 0;
    20693, (124158/13), (448519/45), (4993833/1673), (7758890133/20107261), (26326773728946/803829329117), 1, 0;
    165544, (1173449/13), (992561/9), (69610458/1673), (131462464395/20107261), (644964415216923/803829329117), (56252782754680568/1217779152105385), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 34, 136, 922, 5532, 41386, 331088;
    0, 26, 68, 650, 3688, 30322, 248316, 2346898;
    0, 0, (2160/13), 1520, (208864/13), (2050624/13), (21528912/13), (238214640/13);
    0, 0, 0, (53536/27), (788768/27), (11659040/27), (53267552/9), (742511552/9);
    0, 0, 0, 0, (643432352/8365), (13588085472/8365), (248284484256/8365), (841359772128/1673);
    0, 0, 0, 0, 0, (51445077063488/20107261), (1684913518652544/20107261), (41277722573883072/20107261);
    0, 0, 0, 0, 0, 0, (72949842327720983040/803829329117), (3369766698136384745472/803829329117);
    0, 0, 0, 0, 0, 0, 0, (7005560029844305679718912/1217779152105385)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 34, 136, 922, 5532, 41386, 331088;
    4, 34, 136, 922, 5532, 41386, 331088, 3009074;
    34, 136, 922, 5532, 41386, 331088, 3009074, 30090740;
    136, 922, 5532, 41386, 331088, 3009074, 30090740, 331320242;
    922, 5532, 41386, 331088, 3009074, 30090740, 331320242, 3975842904;
    5532, 41386, 331088, 3009074, 30090740, 331320242, 3975842904, 51689500874;
    41386, 331088, 3009074, 30090740, 331320242, 3975842904, 51689500874, 723653012236;
    331088, 3009074, 30090740, 331320242, 3975842904, 51689500874, 723653012236, 10854834157882]
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
  have hm14 : (endpointMoment 14).eval (-11)=10854834157882 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-11)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_12 :
    (polynomialHankel 8).eval (-12)=3599351098684344445960304471234838528 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    18, (18/7), 1, 0, 0, 0, 0, 0;
    72, (180/7), (156/17), 1, 0, 0, 0, 0;
    504, 144, (1680/17), (620/43), 1, 0, 0, 0;
    3024, (8424/7), (16608/17), (9228/43), (22902/1093), 1, 0, 0;
    22896, (68688/7), (175752/17), (126600/43), (418914/1093), (1604446/48991), 1, 0;
    183168, (651456/7), (1953216/17), (1770672/43), (7091664/1093), (39463080/48991), (1807605576/39432655), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 36, 144, 1008, 6048, 45792, 366336;
    0, 28, 72, 720, 4032, 33696, 274752, 2605824;
    0, 0, (1224/7), (11232/7), 17280, (1195776/7), (12654144/7), (140631552/7);
    0, 0, 0, (37152/17), (535680/17), (7972992/17), (109382400/17), (1529860608/17);
    0, 0, 0, 0, (3777408/43), (79149312/43), (1447766784/43), (24508790784/43);
    0, 0, 0, 0, 0, (3047632128/1093), (99809376768/1093), (2454919280640/1093);
    0, 0, 0, 0, 0, 0, (4906053204480/48991), (224895055343616/48991);
    0, 0, 0, 0, 0, 0, 0, (270390717849636864/39432655)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 36, 144, 1008, 6048, 45792, 366336;
    4, 36, 144, 1008, 6048, 45792, 366336, 3338496;
    36, 144, 1008, 6048, 45792, 366336, 3338496, 33384960;
    144, 1008, 6048, 45792, 366336, 3338496, 33384960, 367732224;
    1008, 6048, 45792, 366336, 3338496, 33384960, 367732224, 4412786688;
    6048, 45792, 366336, 3338496, 33384960, 367732224, 4412786688, 57372198912;
    45792, 366336, 3338496, 33384960, 367732224, 4412786688, 57372198912, 803210784768;
    366336, 3338496, 33384960, 367732224, 4412786688, 57372198912, 803210784768, 12048233435136]
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
  have hm14 : (endpointMoment 14).eval (-12)=12048233435136 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-12)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_13 :
    (polynomialHankel 8).eval (-13)=7155380959424589555151076548983914496 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    19, (38/15), 1, 0, 0, 0, 0, 0;
    76, (397/15), (1583/172), 1, 0, 0, 0, 0;
    549, (732/5), (4341/43), (121572/8611), 1, 0, 0, 0;
    3294, (18667/15), (43202/43), (5467256/25833), (278112373/13352594), 1, 0, 0;
    25255, 10102, (460875/43), (25015008/8611), (2549256006/6676297), (61911333889182/1890649592983), 1, 0;
    202040, (480947/5), (20578599/172), (351021611/8611), (86309729973/13352594), (1529063081414787/1890649592983), (2063885532753252428/45428950424538463), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 38, 152, 1098, 6588, 50510, 404080;
    0, 30, 76, 794, 4392, 37334, 303060, 2885682;
    0, 0, (2752/15), (25328/15), (92608/5), (2764928/15), 1966400, (109752528/5);
    0, 0, 0, (103332/43), (1458864/43), (21869024/43), (300180096/43), (4212259332/43);
    0, 0, 0, 0, (854566016/8611), (17799191872/8611), (326304768768/8611), (5523822718272/8611);
    0, 0, 0, 0, 0, (60500786975456/20028891), (660387561484608/6676297), (16310006201757728/6676297);
    0, 0, 0, 0, 0, 0, (209336603556273237504/1890649592983), (9510384534926987188224/1890649592983);
    0, 0, 0, 0, 0, 0, 0, (370220434304771197501936128/45428950424538463)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 38, 152, 1098, 6588, 50510, 404080;
    4, 38, 152, 1098, 6588, 50510, 404080, 3693842;
    38, 152, 1098, 6588, 50510, 404080, 3693842, 36938420;
    152, 1098, 6588, 50510, 404080, 3693842, 36938420, 407065206;
    1098, 6588, 50510, 404080, 3693842, 36938420, 407065206, 4884782472;
    6588, 50510, 404080, 3693842, 36938420, 407065206, 4884782472, 63511825754;
    50510, 404080, 3693842, 36938420, 407065206, 4884782472, 63511825754, 889165560556;
    404080, 3693842, 36938420, 407065206, 4884782472, 63511825754, 889165560556, 13337608905374]
  have hm0 : (endpointMoment 0).eval (-13)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-13)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-13)=38 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-13)=152 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-13)=1098 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-13)=6588 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-13)=50510 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-13)=404080 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-13)=3693842 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-13)=36938420 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-13)=407065206 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-13)=4884782472 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-13)=63511825754 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-13)=889165560556 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have hm14 : (endpointMoment 14).eval (-13)=13337608905374 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-13)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_14 :
    (polynomialHankel 8).eval (-14)=13838731395364602412131784463449325568 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    20, (5/2), 1, 0, 0, 0, 0, 0;
    80, (109/4), (443/48), 1, 0, 0, 0, 0;
    596, 149, (1237/12), (437572/31631), 1, 0, 0, 0;
    3576, 1289, (12391/12), (6608044/31631), (568999482/27442871), 1, 0, 0;
    27776, 10416, (22211/2), (90718824/31631), (10464295296/27442871), (2857688458191/87292646314), 1, 0;
    222208, 99617, (498085/4), (1277136588/31631), (177264562272/27442871), (141747212200755/174585292628), (14930361723359887/331952483990084), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 40, 160, 1192, 7152, 55552, 444416;
    0, 32, 80, 872, 4768, 41248, 333312, 3187744;
    0, 0, 192, 1772, 19792, 198256, 2132256, 23908080;
    0, 0, 0, (31631/12), (109393/3), (1652011/3), 7559902, 106428049;
    0, 0, 0, 0, (3512687488/31631), (72831933696/31631), (1339429797888/31631), (22689863970816/31631);
    0, 0, 0, 0, 0, (89387669825536/27442871), (2926272981187584/27442871), (72574572646786560/27442871);
    0, 0, 0, 0, 0, 0, (5353729661792074752/43646323157), (240796873874348257536/43646323157);
    0, 0, 0, 0, 0, 0, 0, (799127167196367500266944/82988120997521)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 40, 160, 1192, 7152, 55552, 444416;
    4, 40, 160, 1192, 7152, 55552, 444416, 4076576;
    40, 160, 1192, 7152, 55552, 444416, 4076576, 40765760;
    160, 1192, 7152, 55552, 444416, 4076576, 40765760, 449499008;
    1192, 7152, 55552, 444416, 4076576, 40765760, 449499008, 5393988096;
    7152, 55552, 444416, 4076576, 40765760, 449499008, 5393988096, 70136904320;
    55552, 444416, 4076576, 40765760, 449499008, 5393988096, 70136904320, 981916660480;
    444416, 4076576, 40765760, 449499008, 5393988096, 70136904320, 981916660480, 14728960734208]
  have hm0 : (endpointMoment 0).eval (-14)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-14)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-14)=40 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-14)=160 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-14)=1192 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-14)=7152 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-14)=55552 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-14)=444416 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-14)=4076576 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-14)=40765760 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-14)=449499008 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-14)=5393988096 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-14)=70136904320 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-14)=981916660480 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have hm14 : (endpointMoment 14).eval (-14)=14728960734208 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-14)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_15 :
    (polynomialHankel 8).eval (-15)=26060476291202696530504219361280000000 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    21, (42/17), 1, 0, 0, 0, 0, 0;
    84, (477/17), (657/71), 1, 0, 0, 0, 0;
    645, (2580/17), (7470/71), (3215/237), 1, 0, 0, 0;
    3870, (22725/17), (75300/71), (48925/237), (139705/6761), 1, 0, 0;
    30465, (182790/17), (816525/71), (671575/237), (2579305/6761), (17919698/547669), 1, 0;
    243720, (1756665/17), (9196245/71), (9484850/237), (43747685/6761), (446288879/547669), (9597775904/215716479), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 42, 168, 1290, 7740, 60930, 487440;
    0, 34, 84, 954, 5160, 45450, 365580, 3513330;
    0, 0, (3408/17), (31536/17), (358560/17), (3614400/17), (39193200/17), (441419760/17);
    0, 0, 0, (204768/71), (2777760/71), (42271200/71), (580240800/71), (8194910400/71);
    0, 0, 0, 0, (9735840/79), (201175200/79), (3714199200/79), (62996666400/79);
    0, 0, 0, 0, 0, (23659300800/6761), (774130953600/6761), (19279679572800/6761);
    0, 0, 0, 0, 0, 0, (74551615142400/547669), (3316991352422400/547669);
    0, 0, 0, 0, 0, 0, 0, (811904400809740800/71905493)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 42, 168, 1290, 7740, 60930, 487440;
    4, 42, 168, 1290, 7740, 60930, 487440, 4488210;
    42, 168, 1290, 7740, 60930, 487440, 4488210, 44882100;
    168, 1290, 7740, 60930, 487440, 4488210, 44882100, 495221850;
    1290, 7740, 60930, 487440, 4488210, 44882100, 495221850, 5942662200;
    7740, 60930, 487440, 4488210, 44882100, 495221850, 5942662200, 77277389850;
    60930, 487440, 4488210, 44882100, 495221850, 5942662200, 77277389850, 1081883457900;
    487440, 4488210, 44882100, 495221850, 5942662200, 77277389850, 1081883457900, 16228593587250]
  have hm0 : (endpointMoment 0).eval (-15)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-15)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-15)=42 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-15)=168 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-15)=1290 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-15)=7740 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-15)=60930 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-15)=487440 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-15)=4488210 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-15)=44882100 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-15)=495221850 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-15)=5942662200 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-15)=77277389850 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-15)=1081883457900 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have hm14 : (endpointMoment 14).eval (-15)=16228593587250 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-15)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_H_8_16 :
    (polynomialHankel 8).eval (-16)=47834729787842974606181076919545495552 := by
  rw [polynomialHankel_eval]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    22, (22/9), 1, 0, 0, 0, 0, 0;
    88, (260/9), (436/47), 1, 0, 0, 0, 0;
    696, (464/3), (25224/235), (892/67), 1, 0, 0, 0;
    4176, (12488/9), (255824/235), (944084/4623), (7323866/355331), 1, 0, 0;
    33328, (33328/3), (2797032/235), (4317960/1541), (135823218/355331), (11736813097746/358991782357), 1, 0;
    266624, 107328, (6328512/47), (61180016/1541), (2307619920/355331), (293519695943928/358991782357), (518423649211368104/11785182873295075), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 44, 176, 1392, 8352, 66656, 533248;
    0, 36, 88, 1040, 5568, 49952, 399936, 3863808;
    0, 0, (1880/9), (17440/9), (67264/3), (2046592/9), (7458752/3), 28126720;
    0, 0, 0, (147936/47), (1969536/47), (30210688/47), (414524160/47), (5873281536/47);
    0, 0, 0, 0, (45482368/335), (937454848/335), (17385371904/335), (59075069952/67);
    0, 0, 0, 0, 0, (91901896283392/24517839), (1001541384340992/8172613), (25047014053881856/8172613);
    0, 0, 0, 0, 0, 0, (54306122680143705600/358991782357), (2388896175565984223232/358991782357);
    0, 0, 0, 0, 0, 0, 0, (154685985076561255219408896/11785182873295075)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 44, 176, 1392, 8352, 66656, 533248;
    4, 44, 176, 1392, 8352, 66656, 533248, 4930304;
    44, 176, 1392, 8352, 66656, 533248, 4930304, 49303040;
    176, 1392, 8352, 66656, 533248, 4930304, 49303040, 544430592;
    1392, 8352, 66656, 533248, 4930304, 49303040, 544430592, 6533167104;
    8352, 66656, 533248, 4930304, 49303040, 544430592, 6533167104, 84964726784;
    66656, 533248, 4930304, 49303040, 544430592, 6533167104, 84964726784, 1189506174976;
    533248, 4930304, 49303040, 544430592, 6533167104, 84964726784, 1189506174976, 17843129495552]
  have hm0 : (endpointMoment 0).eval (-16)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-16)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-16)=44 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-16)=176 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-16)=1392 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-16)=8352 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-16)=66656 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-16)=533248 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-16)=4930304 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-16)=49303040 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-16)=544430592 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-16)=6533167104 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-16)=84964726784 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-16)=1189506174976 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have hm14 : (endpointMoment 14).eval (-16)=17843129495552 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+j.val)).eval (-16)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_0 :
    (polynomialBorder 8).eval (0)=11688708243639857483612160000000 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    6, 6, 1, 0, 0, 0, 0, 0;
    24, 36, 12, 1, 0, 0, 0, 0;
    120, 240, 120, 20, 1, 0, 0, 0;
    720, 1800, 1200, 300, 30, 1, 0, 0;
    5040, 15120, 12600, 4200, 630, 42, 1, 0;
    40320, 141120, 141120, 58800, 11760, 1176, 56, 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 12, 48, 240, 1440, 10080, 725760;
    0, 4, 24, 144, 960, 7200, 60480, 5806080;
    0, 0, 24, 288, 2880, 28800, 302400, 40642560;
    0, 0, 0, 288, 5760, 86400, 1209600, 243855360;
    0, 0, 0, 0, 5760, 172800, 3628800, 1219276800;
    0, 0, 0, 0, 0, 172800, 7257600, 4877107200;
    0, 0, 0, 0, 0, 0, 7257600, 14631321600;
    0, 0, 0, 0, 0, 0, 0, 29262643200]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 12, 48, 240, 1440, 10080, 725760;
    4, 12, 48, 240, 1440, 10080, 80640, 7257600;
    12, 48, 240, 1440, 10080, 80640, 725760, 79833600;
    48, 240, 1440, 10080, 80640, 725760, 7257600, 958003200;
    240, 1440, 10080, 80640, 725760, 7257600, 79833600, 12454041600;
    1440, 10080, 80640, 725760, 7257600, 79833600, 958003200, 174356582400;
    10080, 80640, 725760, 7257600, 79833600, 958003200, 12454041600, 2615348736000;
    80640, 725760, 7257600, 79833600, 958003200, 12454041600, 174356582400, 41845579776000]
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
  have hm14 : (endpointMoment 14).eval (0)=2615348736000 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (0)=41845579776000 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (0)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_1 :
    (polynomialBorder 8).eval (-1)=1090238656055367752222081688797184 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    7, (14/3), 1, 0, 0, 0, 0, 0;
    28, (85/3), (19/2), 1, 0, 0, 0, 0;
    141, 188, (432/5), (464/27), 1, 0, 0, 0;
    846, (4231/3), (4072/5), (19144/81), (664477/24432), 1, 0, 0;
    5923, 11846, (41091/5), (28052/9), (2182791/4072), (14212472166/363619027), 1, 0;
    47384, 110563, (178875/2), (1127347/27), (77817055/8144), (379003831923/363619027), (54510014927924/1041239414515), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 14, 56, 282, 1692, 11846, 852914;
    0, 6, 28, 170, 1128, 8462, 71076, 6823312;
    0, 0, (160/3), (1520/3), 4608, (130304/3), 438304, (168024064/3);
    0, 0, 0, 648, 11136, 153152, 2019744, 376561536;
    0, 0, 0, 0, (521216/45), (42526528/135), (93132416/15), (86516471296/45);
    0, 0, 0, 0, 0, (1454476108/4581), (6316654296/509), (11695453618720/1527);
    0, 0, 0, 0, 0, 0, (4798031222085120/363619027), (8628068188392413184/363619027);
    0, 0, 0, 0, 0, 0, 0, (56409104005711347290112/1041239414515)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 14, 56, 282, 1692, 11846, 852914;
    4, 14, 56, 282, 1692, 11846, 94768, 8529140;
    14, 56, 282, 1692, 11846, 94768, 852914, 93820542;
    56, 282, 1692, 11846, 94768, 852914, 8529140, 1125846504;
    282, 1692, 11846, 94768, 852914, 8529140, 93820542, 14636004554;
    1692, 11846, 94768, 852914, 8529140, 93820542, 1125846504, 204904063756;
    11846, 94768, 852914, 8529140, 93820542, 1125846504, 14636004554, 3073560956342;
    94768, 852914, 8529140, 93820542, 1125846504, 14636004554, 204904063756, 49176975301472]
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
  have hm14 : (endpointMoment 14).eval (-1)=3073560956342 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-1)=49176975301472 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-1)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_2 :
    (polynomialBorder 8).eval (-2)=10151318590550377217192515596189696 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    8, 4, 1, 0, 0, 0, 0, 0;
    32, 25, (82/9), 1, 0, 0, 0, 0;
    164, 164, (740/9), (14740/863), 1, 0, 0, 0;
    984, 1232, (6896/9), 236, (2449194/91391), 1, 0, 0;
    6896, 10344, (22988/3), (2692920/863), (48244548/91391), (2838134448/76042643), 1, 0;
    55168, 96548, (248264/3), (36122412/863), (861273888/91391), (73932885795/76042643), (17788465674386/362636573515), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 16, 64, 328, 1968, 13792, 993056;
    0, 8, 32, 200, 1312, 9856, 82752, 7944448;
    0, 0, 72, 656, 5920, 55168, 551712, 69513984;
    0, 0, 0, (6904/9), (117920/9), (1629344/9), (7181120/3), 447096064;
    0, 0, 0, 0, (11698048/863), 363264, (6175302144/863), (1918557846528/863);
    0, 0, 0, 0, 0, (38933833216/91391), (1453124837376/91391), (863794849050624/91391);
    0, 0, 0, 0, 0, 0, (1671029330757120/76042643), (2694329533603270656/76042643);
    0, 0, 0, 0, 0, 0, 0, (32826917241296346820608/362636573515)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 16, 64, 328, 1968, 13792, 993056;
    4, 16, 64, 328, 1968, 13792, 110336, 9930560;
    16, 64, 328, 1968, 13792, 110336, 993056, 109236224;
    64, 328, 1968, 13792, 110336, 993056, 9930560, 1310834688;
    328, 1968, 13792, 110336, 993056, 9930560, 109236224, 17040851072;
    1968, 13792, 110336, 993056, 9930560, 109236224, 1310834688, 238571915008;
    13792, 110336, 993056, 9930560, 109236224, 1310834688, 17040851072, 3578578725376;
    110336, 993056, 9930560, 109236224, 1310834688, 17040851072, 238571915008, 57257259606016]
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
  have hm14 : (endpointMoment 14).eval (-2)=3578578725376 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-2)=57257259606016 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-2)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_3 :
    (polynomialBorder 8).eval (-3)=56341522500594587379170338010038272 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    9, (18/5), 1, 0, 0, 0, 0, 0;
    36, (117/5), 9, 1, 0, 0, 0, 0;
    189, (756/5), 82, 17, 1, 0, 0, 0;
    1134, (5697/5), 764, 237, (493/19), 1, 0, 0;
    7965, 9558, 7635, 3153, (9627/19), (239682/6773), 1, 0;
    63720, (446121/5), 82317, 42486, (171273/19), (6051627/6773), (84115864/1768199), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 18, 72, 378, 2268, 15930, 1147122;
    0, 10, 36, 234, 1512, 11394, 95580, 9176976;
    0, 0, (432/5), (3888/5), (35424/5), (330048/5), 659664, (414113472/5);
    0, 0, 0, 864, 14688, 204768, 2724192, 512764992;
    0, 0, 0, 0, 16416, 425952, 8317728, 2571860160;
    0, 0, 0, 0, 0, (11703744/19), (414170496/19), (233581128192/19);
    0, 0, 0, 0, 0, 0, (219992246784/6773), (336382132303872/6773);
    0, 0, 0, 0, 0, 0, 0, (203159615777353728/1768199)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 18, 72, 378, 2268, 15930, 1147122;
    4, 18, 72, 378, 2268, 15930, 127440, 11471220;
    18, 72, 378, 2268, 15930, 127440, 1147122, 126183906;
    72, 378, 2268, 15930, 127440, 1147122, 11471220, 1514206872;
    378, 2268, 15930, 127440, 1147122, 11471220, 126183906, 19684690794;
    2268, 15930, 127440, 1147122, 11471220, 126183906, 1514206872, 275585671116;
    15930, 127440, 1147122, 11471220, 126183906, 1514206872, 19684690794, 4133785071114;
    127440, 1147122, 11471220, 126183906, 1514206872, 19684690794, 275585671116, 66140561137824]
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
  have hm14 : (endpointMoment 14).eval (-3)=4133785071114 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-3)=66140561137824 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-3)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_4 :
    (polynomialBorder 8).eval (-4)=218151534766551684505046746908327936 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    10, (10/3), 1, 0, 0, 0, 0, 0;
    40, (68/3), (332/37), 1, 0, 0, 0, 0;
    216, 144, (3072/37), (6252/371), 1, 0, 0, 0;
    1296, (3272/3), (28736/37), (263812/1113), (1475842/59231), 1, 0, 0;
    9136, 9136, (287976/37), (1177224/371), (28425246/59231), (20309356962/594681673), 1, 0;
    73088, 85312, (3107520/37), (15942448/371), (502001712/59231), (501624067800/594681673), (251167377608168/5332000562251), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 20, 80, 432, 2592, 18272, 1316096;
    0, 12, 40, 272, 1728, 13088, 109632, 10528768;
    0, 0, (296/3), (2656/3), 8192, (229888/3), 767936, (289547264/3);
    0, 0, 0, (35616/37), (600192/37), (8441984/37), (113013504/37), (21457858560/37);
    0, 0, 0, 0, (7581568/371), (188907776/371), (3638431488/371), (1112131375104/371);
    0, 0, 0, 0, 0, (152238508288/177693), (1733065127424/59231), (940669854760960/59231);
    0, 0, 0, 0, 0, 0, (24569858590852608/594681673), (36962986907526340608/594681673);
    0, 0, 0, 0, 0, 0, 0, (705449475746885370544128/5332000562251)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 20, 80, 432, 2592, 18272, 1316096;
    4, 20, 80, 432, 2592, 18272, 146176, 13160960;
    20, 80, 432, 2592, 18272, 146176, 1316096, 144772608;
    80, 432, 2592, 18272, 146176, 1316096, 13160960, 1737271296;
    432, 2592, 18272, 146176, 1316096, 13160960, 144772608, 22584535040;
    2592, 18272, 146176, 1316096, 13160960, 144772608, 1737271296, 316183490560;
    18272, 146176, 1316096, 13160960, 144772608, 1737271296, 22584535040, 4742752391168;
    146176, 1316096, 13160960, 144772608, 1737271296, 22584535040, 316183490560, 75884038258688]
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
  have hm14 : (endpointMoment 14).eval (-4)=4742752391168 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-4)=75884038258688 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-4)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_5 :
    (polynomialBorder 8).eval (-5)=678755360182690831976166850560000000 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    11, (22/7), 1, 0, 0, 0, 0, 0;
    44, (157/7), (431/48), 1, 0, 0, 0, 0;
    245, 140, (1015/12), (53380/3209), 1, 0, 0, 0;
    1470, (7475/7), (4775/6), (757000/3209), (6157635/257162), 1, 0, 0;
    10415, (62490/7), (16025/2), (10191000/3209), (58431480/128581), (6000550182/179279371), 1, 0;
    83320, (583865/7), (1386445/16), (138687825/3209), (2045354595/257162), (146447217951/179279371), (3555497156428/75684809243), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 22, 88, 490, 2940, 20830, 1501010;
    0, 14, 44, 314, 1960, 14950, 124980, 12008080;
    0, 0, (768/7), (6896/7), 9280, (611200/7), (6153600/7), 110866560;
    0, 0, 0, (3209/3), (53380/3), (757000/3), 3397000, 650550360;
    0, 0, 0, 0, (82291840/3209), (1970443200/3209), (37396147200/3209), (11264996947200/3209);
    0, 0, 0, 0, 0, (143423496800/128581), (4800440145600/128581), (2550515548819200/128581);
    0, 0, 0, 0, 0, 0, (8718890024793600/179279371), (13076433884495001600/179279371);
    0, 0, 0, 0, 0, 0, 0, (11238047814744890265600/75684809243)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 22, 88, 490, 2940, 20830, 1501010;
    4, 22, 88, 490, 2940, 20830, 166640, 15010100;
    22, 88, 490, 2940, 20830, 166640, 1501010, 165117350;
    88, 490, 2940, 20830, 166640, 1501010, 15010100, 1981408200;
    490, 2940, 20830, 166640, 1501010, 15010100, 165117350, 25758337850;
    2940, 20830, 166640, 1501010, 15010100, 165117350, 1981408200, 360616729900;
    20830, 166640, 1501010, 15010100, 165117350, 1981408200, 25758337850, 5409251104750;
    166640, 1501010, 15010100, 165117350, 1981408200, 25758337850, 360616729900, 86548017676000]
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
  have hm14 : (endpointMoment 14).eval (-5)=5409251104750 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-5)=86548017676000 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-5)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_6 :
    (polynomialBorder 8).eval (-6)=1837920041189681059943226435912597504 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    12, 3, 1, 0, 0, 0, 0, 0;
    48, (45/2), 9, 1, 0, 0, 0, 0;
    276, 138, (432/5), (180/11), 1, 0, 0, 0;
    1656, 1062, (4092/5), (2572/11), (11774/509), 1, 0, 0;
    11808, 8856, (41436/5), (34792/11), (220552/509), (836917/25279), 1, 0;
    94464, 82818, 89892, (475676/11), (3826080/509), (40635947/50558), (4736322651/100891715), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 24, 96, 552, 3312, 23616, 1702944;
    0, 16, 48, 360, 2208, 16992, 141696, 13623552;
    0, 0, 120, 1080, 10368, 98208, 994464, 126033408;
    0, 0, 0, 1188, 19440, 277776, 3757536, 725500800;
    0, 0, 0, 0, (1759104/55), (40690944/55), (762227712/55), (226262191104/55);
    0, 0, 0, 0, 0, (698913792/509), (23139081216/509), (12175782727680/509);
    0, 0, 0, 0, 0, 0, (1394727068160/25279), (2093927437099008/25279);
    0, 0, 0, 0, 0, 0, 0, (16775306281041389568/100891715)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 24, 96, 552, 3312, 23616, 1702944;
    4, 24, 96, 552, 3312, 23616, 188928, 17029440;
    24, 96, 552, 3312, 23616, 188928, 1702944, 187339392;
    96, 552, 3312, 23616, 188928, 1702944, 17029440, 2248072704;
    552, 3312, 23616, 188928, 1702944, 17029440, 187339392, 29225038464;
    3312, 23616, 188928, 1702944, 17029440, 187339392, 2248072704, 409150538496;
    23616, 188928, 1702944, 17029440, 187339392, 2248072704, 29225038464, 6137258637312;
    188928, 1702944, 17029440, 187339392, 2248072704, 29225038464, 409150538496, 98196138196992]
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
  have hm14 : (endpointMoment 14).eval (-6)=6137258637312 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-6)=98196138196992 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-6)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_7 :
    (polynomialBorder 8).eval (-7)=4538591247834932642618907534500560896 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    13, (26/9), 1, 0, 0, 0, 0, 0;
    52, (205/9), (659/73), 1, 0, 0, 0, 0;
    309, (412/3), (6450/73), (16105/1003), 1, 0, 0, 0;
    1854, (9613/9), (61532/73), (695269/3009), (27742021/1233529), 1, 0, 0;
    13321, (26642/3), (627123/73), (3147585/1003), (514357977/1233529), (3088812197898/93836955313), 1, 0;
    106568, 83153, (6826239/73), (43220842/1003), (8854329057/1233529), (74890234428555/93836955313), (8391644262681008/178883837066455), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 26, 104, 618, 3708, 26642, 1923026;
    0, 18, 52, 410, 2472, 19226, 159852, 15384208;
    0, 0, (1168/9), (10544/9), (34400/3), (984512/9), (3344656/3), (1279114816/9);
    0, 0, 0, (96288/73), (1546080/73), (22248608/73), (302168160/73), (58792276032/73);
    0, 0, 0, 0, (39472928/1003), (887744672/1003), (16459455264/1003), (4822783535808/1003);
    0, 0, 0, 0, 0, (6005565140032/3700587), (65894660221824/1233529), (34586153601481216/1233529);
    0, 0, 0, 0, 0, 0, (5770077048415572480/93836955313), (8675786663581444356096/93836955313);
    0, 0, 0, 0, 0, 0, 0, (33546765762388149207035904/178883837066455)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 26, 104, 618, 3708, 26642, 1923026;
    4, 26, 104, 618, 3708, 26642, 213136, 19230260;
    26, 104, 618, 3708, 26642, 213136, 1923026, 211566474;
    104, 618, 3708, 26642, 213136, 1923026, 19230260, 2538797688;
    618, 3708, 26642, 213136, 1923026, 19230260, 211566474, 33004605242;
    3708, 26642, 213136, 1923026, 19230260, 211566474, 2538797688, 462064473388;
    26642, 213136, 1923026, 19230260, 211566474, 2538797688, 33004605242, 6930968747906;
    213136, 1923026, 19230260, 211566474, 2538797688, 33004605242, 462064473388, 110895499966496]
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
  have hm14 : (endpointMoment 14).eval (-7)=6930968747906 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-7)=110895499966496 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-7)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_8 :
    (polynomialBorder 8).eval (-8)=10516786677635178802137688647476969472 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    14, (14/5), 1, 0, 0, 0, 0, 0;
    56, (116/5), (788/87), 1, 0, 0, 0, 0;
    344, (688/5), (7864/87), (62588/3979), 1, 0, 0, 0;
    2064, (5416/5), (75568/87), (906788/3979), (32577186/1481023), 1, 0, 0;
    14960, 8976, (258520/29), (12355512/3979), (599618994/1481023), (353949510042/10784400593), 1, 0;
    119680, (420928/5), (2824768/29), (170350224/3979), (10258433616/1481023), (8590598544792/10784400593), (7448786509527368/159046407326383), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 28, 112, 688, 4128, 29920, 2162432;
    0, 20, 56, 464, 2752, 21664, 179520, 17299456;
    0, 0, (696/5), (6304/5), (62912/5), (604544/5), 1240896, (796102656/5);
    0, 0, 0, (127328/87), (2002816/87), (29017216/87), (131792128/29), (25827913728/29);
    0, 0, 0, 0, (189570944/3979), (4169879808/3979), (76751231232/3979), (22253291581440/3979);
    0, 0, 0, 0, 0, (2760806551808/1481023), (90611074570752/1481023), (47640973406060544/1481023);
    0, 0, 0, 0, 0, 0, (732885844959972864/10784400593), (1102350317859940073472/10784400593);
    0, 0, 0, 0, 0, 0, 0, (34008752935058886140461056/159046407326383)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 28, 112, 688, 4128, 29920, 2162432;
    4, 28, 112, 688, 4128, 29920, 239360, 21624320;
    28, 112, 688, 4128, 29920, 239360, 2162432, 237933056;
    112, 688, 4128, 29920, 239360, 2162432, 21624320, 2855196672;
    688, 4128, 29920, 239360, 2162432, 21624320, 237933056, 37118081024;
    4128, 29920, 239360, 2162432, 21624320, 237933056, 2855196672, 519653134336;
    29920, 239360, 2162432, 21624320, 237933056, 2855196672, 37118081024, 7794801209344;
    239360, 2162432, 21624320, 237933056, 2855196672, 37118081024, 519653134336, 124716819349504]
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
  have hm14 : (endpointMoment 14).eval (-8)=7794801209344 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-8)=124716819349504 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-8)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_9 :
    (polynomialBorder 8).eval (-9)=23266278722036868415143951869165961216 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    15, (30/11), 1, 0, 0, 0, 0, 0;
    60, (261/11), (309/34), 1, 0, 0, 0, 0;
    381, (1524/11), (1572/17), (5896/383), 1, 0, 0, 0;
    2286, (12159/11), (15216/17), (85992/383), (815613/37724), 1, 0, 0;
    16731, 9126, (157311/17), (1174692/383), (7471827/18862), (1501724982/45818603), 1, 0;
    133848, (943497/11), (3451725/34), (16258119/383), (254485533/37724), (36535798515/45818603), (3861160927012/82692981059), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 30, 120, 762, 4572, 33462, 2422386;
    0, 22, 60, 522, 3048, 24318, 200772, 19379088;
    0, 0, (1632/11), (14832/11), (150912/11), (1460736/11), 1372896, (1951319808/11);
    0, 0, 0, (27576/17), (424512/17), (6191424/17), (84577824/17), (16687607040/17);
    0, 0, 0, 0, (21729024/383), (469793088/383), (8607544704/383), (2476032924672/383);
    0, 0, 0, 0, 0, (19793636496/9431), (648745192224/9431), (342550807816320/9431);
    0, 0, 0, 0, 0, 0, (3429443310478848/45818603), (5150162545459550208/45818603);
    0, 0, 0, 0, 0, 0, 0, (20386468677735347392512/82692981059)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 30, 120, 762, 4572, 33462, 2422386;
    4, 30, 120, 762, 4572, 33462, 267696, 24223860;
    30, 120, 762, 4572, 33462, 267696, 2422386, 266580558;
    120, 762, 4572, 33462, 267696, 2422386, 24223860, 3198966696;
    762, 4572, 33462, 267696, 2422386, 24223860, 266580558, 41587629930;
    4572, 33462, 267696, 2422386, 24223860, 266580558, 3198966696, 582226819020;
    33462, 267696, 2422386, 24223860, 266580558, 3198966696, 41587629930, 8733411851238;
    267696, 2422386, 24223860, 266580558, 3198966696, 41587629930, 582226819020, 139734589619808]
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
  have hm14 : (endpointMoment 14).eval (-9)=8733411851238 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-9)=139734589619808 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-9)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_10 :
    (polynomialBorder 8).eval (-10)=49639157717727525719416095375360000000 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    16, (8/3), 1, 0, 0, 0, 0, 0;
    64, (73/3), (538/59), 1, 0, 0, 0, 0;
    420, 140, (5580/59), (66460/4413), 1, 0, 0, 0;
    2520, (3400/3), (54400/59), (2927300/13239), (9786310/458697), 1, 0, 0;
    18640, 9320, (566700/59), (4451800/1471), (59631420/152899), (8203394772/250429541), 1, 0;
    149120, 87820, (6243480/59), (185516900/4413), (1012299040/152899), (200226923151/250429541), (8323799772778/179087271173), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 32, 128, 840, 5040, 37280, 2704160;
    0, 24, 64, 584, 3360, 27200, 223680, 21633280;
    0, 0, (472/3), (4304/3), 14880, (435200/3), 1511200, (590106880/3);
    0, 0, 0, (105912/59), (1595040/59), (23418400/59), (320529600/59), (63646659840/59);
    0, 0, 0, 0, (97855360/1471), (6263238400/4413), (38164108800/1471), (10918756940800/1471);
    0, 0, 0, 0, 0, (3205498124800/1376091), (11667050342400/152899), (18588649820262400/458697);
    0, 0, 0, 0, 0, 0, (20630853639129600/250429541), (30862688454928281600/250429541);
    0, 0, 0, 0, 0, 0, 0, (51366742408241999769600/179087271173)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 32, 128, 840, 5040, 37280, 2704160;
    4, 32, 128, 840, 5040, 37280, 298240, 27041600;
    32, 128, 840, 5040, 37280, 298240, 2704160, 297657600;
    128, 840, 5040, 37280, 298240, 2704160, 27041600, 3571891200;
    840, 5040, 37280, 298240, 2704160, 27041600, 297657600, 46436585600;
    5040, 37280, 298240, 2704160, 27041600, 297657600, 3571891200, 650112198400;
    37280, 298240, 2704160, 27041600, 297657600, 3571891200, 46436585600, 9751702976000;
    298240, 2704160, 27041600, 297657600, 3571891200, 46436585600, 650112198400, 156027247616000]
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
  have hm14 : (endpointMoment 14).eval (-10)=9751702976000 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-10)=156027247616000 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-10)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_11 :
    (polynomialBorder 8).eval (-11)=102698578498541413061245193051097268224 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    17, (34/13), 1, 0, 0, 0, 0, 0;
    68, 25, (247/27), 1, 0, 0, 0, 0;
    461, (1844/13), (13054/135), (24649/1673), 1, 0, 0, 0;
    2766, (15161/13), (128164/135), (364345/1673), (424627671/20107261), 1, 0, 0;
    20693, (124158/13), (448519/45), (4993833/1673), (7758890133/20107261), (26326773728946/803829329117), 1, 0;
    165544, (1173449/13), (992561/9), (69610458/1673), (131462464395/20107261), (644964415216923/803829329117), (56252782754680568/1217779152105385), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 34, 136, 922, 5532, 41386, 3009074;
    0, 26, 68, 650, 3688, 30322, 248316, 24072592;
    0, 0, (2160/13), 1520, (208864/13), (2050624/13), (21528912/13), (2823689664/13);
    0, 0, 0, (53536/27), (788768/27), (11659040/27), (53267552/9), (3547110592/3);
    0, 0, 0, 0, (643432352/8365), (13588085472/8365), (248284484256/8365), (70803553363392/8365);
    0, 0, 0, 0, 0, (51445077063488/20107261), (1684913518652544/20107261), (900850727873748480/20107261);
    0, 0, 0, 0, 0, 0, (72949842327720983040/803829329117), (108450418407375223240704/803829329117);
    0, 0, 0, 0, 0, 0, 0, (24043616022275367699566592/71634067770905)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 34, 136, 922, 5532, 41386, 3009074;
    4, 34, 136, 922, 5532, 41386, 331088, 30090740;
    34, 136, 922, 5532, 41386, 331088, 3009074, 331320242;
    136, 922, 5532, 41386, 331088, 3009074, 30090740, 3975842904;
    922, 5532, 41386, 331088, 3009074, 30090740, 331320242, 51689500874;
    5532, 41386, 331088, 3009074, 30090740, 331320242, 3975842904, 723653012236;
    41386, 331088, 3009074, 30090740, 331320242, 3975842904, 51689500874, 10854834157882;
    331088, 3009074, 30090740, 331320242, 3975842904, 51689500874, 723653012236, 173677346526112]
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
  have hm14 : (endpointMoment 14).eval (-11)=10854834157882 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-11)=173677346526112 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-11)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_12 :
    (polynomialBorder 8).eval (-12)=206624954564235744156634019028843626496 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    18, (18/7), 1, 0, 0, 0, 0, 0;
    72, (180/7), (156/17), 1, 0, 0, 0, 0;
    504, 144, (1680/17), (620/43), 1, 0, 0, 0;
    3024, (8424/7), (16608/17), (9228/43), (22902/1093), 1, 0, 0;
    22896, (68688/7), (175752/17), (126600/43), (418914/1093), (1604446/48991), 1, 0;
    183168, (651456/7), (1953216/17), (1770672/43), (7091664/1093), (39463080/48991), (1807605576/39432655), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 36, 144, 1008, 6048, 45792, 3338496;
    0, 28, 72, 720, 4032, 33696, 274752, 26707968;
    0, 0, (1224/7), (11232/7), 17280, (1195776/7), (12654144/7), 238961664;
    0, 0, 0, (37152/17), (535680/17), (7972992/17), (109382400/17), (21977837568/17);
    0, 0, 0, 0, (3777408/43), (79149312/43), (1447766784/43), (412285759488/43);
    0, 0, 0, 0, 0, (3047632128/1093), (99809376768/1093), (53750662152192/1093);
    0, 0, 0, 0, 0, 0, (4906053204480/48991), (7231832458371072/48991);
    0, 0, 0, 0, 0, 0, 0, (15522095027265896448/39432655)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 36, 144, 1008, 6048, 45792, 3338496;
    4, 36, 144, 1008, 6048, 45792, 366336, 33384960;
    36, 144, 1008, 6048, 45792, 366336, 3338496, 367732224;
    144, 1008, 6048, 45792, 366336, 3338496, 33384960, 4412786688;
    1008, 6048, 45792, 366336, 3338496, 33384960, 367732224, 57372198912;
    6048, 45792, 366336, 3338496, 33384960, 367732224, 4412786688, 803210784768;
    45792, 366336, 3338496, 33384960, 367732224, 4412786688, 57372198912, 12048233435136;
    366336, 3338496, 33384960, 367732224, 4412786688, 57372198912, 803210784768, 192771734962176]
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
  have hm14 : (endpointMoment 14).eval (-12)=12048233435136 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-12)=192771734962176 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-12)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_13 :
    (polynomialBorder 8).eval (-13)=404882061711405445176501975349117059072 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    19, (38/15), 1, 0, 0, 0, 0, 0;
    76, (397/15), (1583/172), 1, 0, 0, 0, 0;
    549, (732/5), (4341/43), (121572/8611), 1, 0, 0, 0;
    3294, (18667/15), (43202/43), (5467256/25833), (278112373/13352594), 1, 0, 0;
    25255, 10102, (460875/43), (25015008/8611), (2549256006/6676297), (61911333889182/1890649592983), 1, 0;
    202040, (480947/5), (20578599/172), (351021611/8611), (86309729973/13352594), (1529063081414787/1890649592983), (2063885532753252428/45428950424538463), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 38, 152, 1098, 6588, 50510, 3693842;
    0, 30, 76, 794, 4392, 37334, 303060, 29550736;
    0, 0, (2752/15), (25328/15), (92608/5), (2764928/15), 1966400, (3930305152/15);
    0, 0, 0, (103332/43), (1458864/43), (21869024/43), (300180096/43), (60648912096/43);
    0, 0, 0, 0, (854566016/8611), (17799191872/8611), (326304768768/8611), (92937749602560/8611);
    0, 0, 0, 0, 0, (60500786975456/20028891), (660387561484608/6676297), (358318261639751936/6676297);
    0, 0, 0, 0, 0, 0, (209336603556273237504/1890649592983), (305347951991979532081152/1890649592983);
    0, 0, 0, 0, 0, 0, 0, (20948655784927176372484509696/45428950424538463)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 38, 152, 1098, 6588, 50510, 3693842;
    4, 38, 152, 1098, 6588, 50510, 404080, 36938420;
    38, 152, 1098, 6588, 50510, 404080, 3693842, 407065206;
    152, 1098, 6588, 50510, 404080, 3693842, 36938420, 4884782472;
    1098, 6588, 50510, 404080, 3693842, 36938420, 407065206, 63511825754;
    6588, 50510, 404080, 3693842, 36938420, 407065206, 4884782472, 889165560556;
    50510, 404080, 3693842, 36938420, 407065206, 4884782472, 63511825754, 13337608905374;
    404080, 3693842, 36938420, 407065206, 4884782472, 63511825754, 889165560556, 213401742485984]
  have hm0 : (endpointMoment 0).eval (-13)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-13)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-13)=38 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-13)=152 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-13)=1098 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-13)=6588 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-13)=50510 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-13)=404080 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-13)=3693842 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-13)=36938420 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-13)=407065206 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-13)=4884782472 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-13)=63511825754 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-13)=889165560556 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have hm14 : (endpointMoment 14).eval (-13)=13337608905374 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-13)=213401742485984 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-13)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_14 :
    (polynomialBorder 8).eval (-14)=773412937806714545676418323532423888896 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    20, (5/2), 1, 0, 0, 0, 0, 0;
    80, (109/4), (443/48), 1, 0, 0, 0, 0;
    596, 149, (1237/12), (437572/31631), 1, 0, 0, 0;
    3576, 1289, (12391/12), (6608044/31631), (568999482/27442871), 1, 0, 0;
    27776, 10416, (22211/2), (90718824/31631), (10464295296/27442871), (2857688458191/87292646314), 1, 0;
    222208, 99617, (498085/4), (1277136588/31631), (177264562272/27442871), (141747212200755/174585292628), (14930361723359887/331952483990084), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 40, 160, 1192, 7152, 55552, 4076576;
    0, 32, 80, 872, 4768, 41248, 333312, 32612608;
    0, 0, 192, 1772, 19792, 198256, 2132256, 286435968;
    0, 0, 0, (31631/12), (109393/3), (1652011/3), 7559902, 1535603160;
    0, 0, 0, 0, (3512687488/31631), (72831933696/31631), (1339429797888/31631), (382046312868864/31631);
    0, 0, 0, 0, 0, (89387669825536/27442871), (2926272981187584/27442871), (1599899555673108480/27442871);
    0, 0, 0, 0, 0, 0, (5353729661792074752/43646323157), (7714506698693879519232/43646323157);
    0, 0, 0, 0, 0, 0, 0, (44661267886847120045203968/82988120997521)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 40, 160, 1192, 7152, 55552, 4076576;
    4, 40, 160, 1192, 7152, 55552, 444416, 40765760;
    40, 160, 1192, 7152, 55552, 444416, 4076576, 449499008;
    160, 1192, 7152, 55552, 444416, 4076576, 40765760, 5393988096;
    1192, 7152, 55552, 444416, 4076576, 40765760, 449499008, 70136904320;
    7152, 55552, 444416, 4076576, 40765760, 449499008, 5393988096, 981916660480;
    55552, 444416, 4076576, 40765760, 449499008, 5393988096, 70136904320, 14728960734208;
    444416, 4076576, 40765760, 449499008, 5393988096, 70136904320, 981916660480, 235663371747328]
  have hm0 : (endpointMoment 0).eval (-14)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-14)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-14)=40 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-14)=160 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-14)=1192 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-14)=7152 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-14)=55552 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-14)=444416 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-14)=4076576 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-14)=40765760 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-14)=449499008 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-14)=5393988096 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-14)=70136904320 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-14)=981916660480 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have hm14 : (endpointMoment 14).eval (-14)=14728960734208 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-14)=235663371747328 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-14)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_15 :
    (polynomialBorder 8).eval (-15)=1441403936367185693315034576322560000000 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    21, (42/17), 1, 0, 0, 0, 0, 0;
    84, (477/17), (657/71), 1, 0, 0, 0, 0;
    645, (2580/17), (7470/71), (3215/237), 1, 0, 0, 0;
    3870, (22725/17), (75300/71), (48925/237), (139705/6761), 1, 0, 0;
    30465, (182790/17), (816525/71), (671575/237), (2579305/6761), (17919698/547669), 1, 0;
    243720, (1756665/17), (9196245/71), (9484850/237), (43747685/6761), (446288879/547669), (9597775904/215716479), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 42, 168, 1290, 7740, 60930, 4488210;
    0, 34, 84, 954, 5160, 45450, 365580, 35905680;
    0, 0, (3408/17), (31536/17), (358560/17), (3614400/17), (39193200/17), (5308441920/17);
    0, 0, 0, (204768/71), (2777760/71), (42271200/71), (580240800/71), (118475213760/71);
    0, 0, 0, 0, (9735840/79), (201175200/79), (3714199200/79), (1062057355200/79);
    0, 0, 0, 0, 0, (23659300800/6761), (774130953600/6761), (426485118067200/6761);
    0, 0, 0, 0, 0, 0, (74551615142400/547669), (105984726719846400/547669);
    0, 0, 0, 0, 0, 0, 0, (44906401026755481600/71905493)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 42, 168, 1290, 7740, 60930, 4488210;
    4, 42, 168, 1290, 7740, 60930, 487440, 44882100;
    42, 168, 1290, 7740, 60930, 487440, 4488210, 495221850;
    168, 1290, 7740, 60930, 487440, 4488210, 44882100, 5942662200;
    1290, 7740, 60930, 487440, 4488210, 44882100, 495221850, 77277389850;
    7740, 60930, 487440, 4488210, 44882100, 495221850, 5942662200, 1081883457900;
    60930, 487440, 4488210, 44882100, 495221850, 5942662200, 77277389850, 16228593587250;
    487440, 4488210, 44882100, 495221850, 5942662200, 77277389850, 1081883457900, 259657497396000]
  have hm0 : (endpointMoment 0).eval (-15)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-15)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-15)=42 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-15)=168 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-15)=1290 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-15)=7740 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-15)=60930 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-15)=487440 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-15)=4488210 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-15)=44882100 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-15)=495221850 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-15)=5942662200 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-15)=77277389850 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-15)=1081883457900 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have hm14 : (endpointMoment 14).eval (-15)=16228593587250 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-15)=259657497396000 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-15)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem sample_J_8_16 :
    (polynomialBorder 8).eval (-16)=2623185945497527452714344240894227513344 := by
  rw [polynomialBorder_eval 8 (by norm_num)]
  let L : Matrix (Fin 8) (Fin 8) ℚ := !![1, 0, 0, 0, 0, 0, 0, 0;
    2, 1, 0, 0, 0, 0, 0, 0;
    22, (22/9), 1, 0, 0, 0, 0, 0;
    88, (260/9), (436/47), 1, 0, 0, 0, 0;
    696, (464/3), (25224/235), (892/67), 1, 0, 0, 0;
    4176, (12488/9), (255824/235), (944084/4623), (7323866/355331), 1, 0, 0;
    33328, (33328/3), (2797032/235), (4317960/1541), (135823218/355331), (11736813097746/358991782357), 1, 0;
    266624, 107328, (6328512/47), (61180016/1541), (2307619920/355331), (293519695943928/358991782357), (518423649211368104/11785182873295075), 1]
  let U : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 44, 176, 1392, 8352, 66656, 4930304;
    0, 36, 88, 1040, 5568, 49952, 399936, 39442432;
    0, 0, (1880/9), (17440/9), (67264/3), (2046592/9), (7458752/3), (3055941632/9);
    0, 0, 0, (147936/47), (1969536/47), (30210688/47), (414524160/47), (85069664256/47);
    0, 0, 0, 0, (45482368/335), (937454848/335), (17385371904/335), (4988046348288/335);
    0, 0, 0, 0, 0, (91901896283392/24517839), (1001541384340992/8172613), (555958755774545920/8172613);
    0, 0, 0, 0, 0, 0, (54306122680143705600/358991782357), (76097903649663653167104/358991782357);
    0, 0, 0, 0, 0, 0, 0, (8482751001582970728613773312/11785182873295075)]
  let A : Matrix (Fin 8) (Fin 8) ℚ := !![2, 4, 44, 176, 1392, 8352, 66656, 4930304;
    4, 44, 176, 1392, 8352, 66656, 533248, 49303040;
    44, 176, 1392, 8352, 66656, 533248, 4930304, 544430592;
    176, 1392, 8352, 66656, 533248, 4930304, 49303040, 6533167104;
    1392, 8352, 66656, 533248, 4930304, 49303040, 544430592, 84964726784;
    8352, 66656, 533248, 4930304, 49303040, 544430592, 6533167104, 1189506174976;
    66656, 533248, 4930304, 49303040, 544430592, 6533167104, 84964726784, 17843129495552;
    533248, 4930304, 49303040, 544430592, 6533167104, 84964726784, 1189506174976, 285490071928832]
  have hm0 : (endpointMoment 0).eval (-16)=2 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
  have hm1 : (endpointMoment 1).eval (-16)=4 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm0]
  have hm2 : (endpointMoment 2).eval (-16)=44 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm1]
  have hm3 : (endpointMoment 3).eval (-16)=176 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm2]
  have hm4 : (endpointMoment 4).eval (-16)=1392 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm3]
  have hm5 : (endpointMoment 5).eval (-16)=8352 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm4]
  have hm6 : (endpointMoment 6).eval (-16)=66656 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm5]
  have hm7 : (endpointMoment 7).eval (-16)=533248 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm6]
  have hm8 : (endpointMoment 8).eval (-16)=4930304 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm7]
  have hm9 : (endpointMoment 9).eval (-16)=49303040 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm8]
  have hm10 : (endpointMoment 10).eval (-16)=544430592 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm9]
  have hm11 : (endpointMoment 11).eval (-16)=6533167104 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm10]
  have hm12 : (endpointMoment 12).eval (-16)=84964726784 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm11]
  have hm13 : (endpointMoment 13).eval (-16)=1189506174976 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm12]
  have hm14 : (endpointMoment 14).eval (-16)=17843129495552 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm13]
  have hm15 : (endpointMoment 15).eval (-16)=285490071928832 := by
    norm_num [endpointMoment,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X,hm14]
  have he : (Matrix.of (fun i j : Fin 8 =>
      (endpointMoment (i.val+borderColumn 8 j)).eval (-16)))=A := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [A,borderColumn,hm0,hm1,hm2,hm3,hm4,hm5,hm6,hm7,hm8,hm9,hm10,hm11,hm12,hm13,hm14,hm15]
  have hA : A=L*U := by decide +kernel
  rw [he]
  rw [determinant_LU_certificate _ L U hA]
  · norm_num [L,U,Fin.prod_univ_succ]
  · decide +kernel
  · decide +kernel

theorem table_H_8 : polynomialHankel 8=C (89060441849856)*appendixG16 := by
  apply eq_of_natDegree_lt_card_of_eval_eq (f:=fun i : Fin 17 => -(i.val:ℚ))
  · intro i j h
    apply Fin.ext
    exact_mod_cast neg_inj.mp h
  · intro i
    fin_cases i <;>
      norm_num [sample_H_8_0,sample_H_8_1,sample_H_8_2,sample_H_8_3,sample_H_8_4,sample_H_8_5,sample_H_8_6,sample_H_8_7,sample_H_8_8,sample_H_8_9,sample_H_8_10,sample_H_8_11,sample_H_8_12,sample_H_8_13,sample_H_8_14,sample_H_8_15,sample_H_8_16,appendixG16]
  · apply max_lt
    · rw [polynomialHankel_natDegree]
      norm_num [hankelDegree]
    · unfold appendixG16
      compute_degree!

theorem table_J_8 : polynomialBorder 8=C (6412351813189632)*appendixG16-X*(C (3562417673994240)*appendixG15) := by
  apply eq_of_natDegree_lt_card_of_eval_eq (f:=fun i : Fin 17 => -(i.val:ℚ))
  · intro i j h
    apply Fin.ext
    exact_mod_cast neg_inj.mp h
  · intro i
    fin_cases i <;>
      norm_num [sample_J_8_0,sample_J_8_1,sample_J_8_2,sample_J_8_3,sample_J_8_4,sample_J_8_5,sample_J_8_6,sample_J_8_7,sample_J_8_8,sample_J_8_9,sample_J_8_10,sample_J_8_11,sample_J_8_12,sample_J_8_13,sample_J_8_14,sample_J_8_15,sample_J_8_16,appendixG16,appendixG15]
  · apply max_lt
    · rw [polynomialBorder_natDegree 8 (by norm_num)]
      norm_num [hankelDegree]
    · unfold appendixG16 appendixG15
      compute_degree!

theorem recurrenceFamily_appendix_16 : recurrenceFamily 16=appendixG16 := by
  have h := recurrenceFamily_hankel_eq (n:=8) (by norm_num) appendixG16
    (89060441849856) (by norm_num) appendixG16_monic table_H_8
  simpa only [hankelDegree,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceMul] using h

theorem recurrenceFamily_appendix_15 : recurrenceFamily 15=appendixG15 := by
  have h := recurrenceFamily_numerator_eq (n:=8) (by norm_num) appendixG15
    (3562417673994240) (by norm_num) appendixG15_monic (by
      rw [polynomialNumerator,table_H_8,table_J_8]
      norm_num only [Nat.cast_ofNat,map_ofNat,map_neg]
      ring)
  simpa only [hankelDegree,Nat.reduceDiv,Nat.reduceAdd,Nat.reduceMul,Nat.reduceSub] using h

end OscillatoryRecurrence
