import OscillatoryRecurrence.FiniteCertificates

noncomputable section
open Polynomial
namespace OscillatoryRecurrence

/-- The degree-2 polynomial printed in Appendix C(4). -/
def appendixG2 : ℚ[X] :=
  C (1)*X^2 + C (-13)*X^1 + C (6)

theorem appendixG2_monic : appendixG2.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (n:=2)
  · unfold appendixG2
    compute_degree!
  · norm_num [appendixG2]

/-- The degree-3 polynomial printed in Appendix C(4). -/
def appendixG3 : ℚ[X] :=
  C (1)*X^3 + C (-7)*X^2 + C (12)*X^1 + C (-360)

theorem appendixG3_monic : appendixG3.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (n:=3)
  · unfold appendixG3
    compute_degree!
  · norm_num [appendixG3]

/-- The degree-4 polynomial printed in Appendix C(4). -/
def appendixG4 : ℚ[X] :=
  C (1)*X^4 + C (-14)*X^3 + C (165)*X^2 + C (-1224)*X^1 + C (216)

theorem appendixG4_monic : appendixG4.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (n:=4)
  · unfold appendixG4
    compute_degree!
  · norm_num [appendixG4]

/-- The degree-5 polynomial printed in Appendix C(4). -/
def appendixG5 : ℚ[X] :=
  C (1)*X^5 + C (-133)*X^4 + C (1929)*X^3 + C (-5940)*X^2 + C (-4320)*X^1 + C (-64800)

theorem appendixG5_monic : appendixG5.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (n:=5)
  · unfold appendixG5
    compute_degree!
  · norm_num [appendixG5]

/-- The degree-6 polynomial printed in Appendix C(4). -/
def appendixG6 : ℚ[X] :=
  C (1)*X^6 + C (-77)*X^5 + C (1101)*X^4 + C (-4932)*X^3 + C (17361)*X^2 + C (-113400)*X^1 + C (9720)

theorem appendixG6_monic : appendixG6.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (n:=6)
  · unfold appendixG6
    compute_degree!
  · norm_num [appendixG6]

/-- The degree-8 polynomial printed in Appendix C(4). -/
def appendixG8 : ℚ[X] :=
  C (1)*X^8 + C (-39)*X^7 + C ((1089/2))*X^6 + C ((-70785/2))*X^5 + C ((1578285/2))*X^4 + C (-5829975)*X^3 + C ((21402225/2))*X^2 + C (11481750)*X^1 + C (38272500)

theorem appendixG8_monic : appendixG8.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (n:=8)
  · unfold appendixG8
    compute_degree!
  · norm_num [appendixG8]

/-- The degree-9 polynomial printed in Appendix C(4). -/
def appendixG9 : ℚ[X] :=
  C (1)*X^9 + C (-54)*X^8 + C (2286)*X^7 + C (-105966)*X^6 + C (1927125)*X^5 + C (-13601520)*X^4 + C (31122225)*X^3 + C (-30362850)*X^2 + C (273375000)*X^1 + C (-13122000)

theorem appendixG9_monic : appendixG9.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (n:=9)
  · unfold appendixG9
    compute_degree!
  · norm_num [appendixG9]

/-- The degree-11 polynomial printed in Appendix C(4). -/
def appendixG11 : ℚ[X] :=
  C (1)*X^11 + C ((-829/2))*X^10 + C ((58275/2))*X^9 + C (-716715)*X^8 + C (6765075)*X^7 + C ((-117734175/2))*X^6 + C ((3083335875/2))*X^5 + C ((-41419987875/2))*X^4 + C ((211076026875/2))*X^3 + C (-132499395000)*X^2 + C (-136632825000)*X^1 + C (-192893400000)

theorem appendixG11_monic : appendixG11.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (n:=11)
  · unfold appendixG11
    compute_degree!
  · norm_num [appendixG11]

/-- The degree-12 polynomial printed in Appendix C(4). -/
def appendixG12 : ℚ[X] :=
  C (1)*X^12 + C (-252)*X^11 + C (16437)*X^10 + C (-425835)*X^9 + C (6134265)*X^8 + C (-120820950)*X^7 + C (2458605150)*X^6 + C (-26341594875)*X^5 + C (124060399875)*X^4 + C (-176784778125)*X^3 + C (-8439086250)*X^2 + C (-699238575000)*X^1 + C (20667150000)

theorem appendixG12_monic : appendixG12.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (n:=12)
  · unfold appendixG12
    compute_degree!
  · norm_num [appendixG12]

/-- The degree-15 polynomial printed in Appendix C(4). -/
def appendixG15 : ℚ[X] :=
  C (1)*X^15 + C (-126)*X^14 + C (6654)*X^13 + C (-749439)*X^12 + C (71087220)*X^11 + C (-3142068435)*X^10 + C (67831410825)*X^9 + C (-727590460275)*X^8 + C (3449814897375)*X^7 + C (-12254173249500)*X^6 + C (266877060778125)*X^5 + C (-2987052554075625)*X^4 + C (12107364149475000)*X^3 + C (-11246939027100000)*X^2 + C (-10207918728000000)*X^1 + C (-7655939046000000)

theorem appendixG15_monic : appendixG15.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (n:=15)
  · unfold appendixG15
    compute_degree!
  · norm_num [appendixG15]

/-- The degree-16 polynomial printed in Appendix C(4). -/
def appendixG16 : ℚ[X] :=
  C (1)*X^16 + C (-152)*X^15 + C (15804)*X^14 + C (-2021700)*X^13 + C (157758030)*X^12 + C (-6308511300)*X^11 + C (132164631450)*X^10 + C (-1493816296500)*X^9 + C (10920101842125)*X^8 + C (-117706861125000)*X^7 + C (1646298202263750)*X^6 + C (-13233804005362500)*X^5 + C (47682964163165625)*X^4 + C (-47494695181500000)*X^3 + C (-22188045568500000)*X^2 + C (-93572588340000000)*X^1 + C (1822842630000000)

theorem appendixG16_monic : appendixG16.Monic := by
  apply monic_of_natDegree_le_of_coeff_eq_one (n:=16)
  · unfold appendixG16
    compute_degree!
  · norm_num [appendixG16]

end OscillatoryRecurrence
