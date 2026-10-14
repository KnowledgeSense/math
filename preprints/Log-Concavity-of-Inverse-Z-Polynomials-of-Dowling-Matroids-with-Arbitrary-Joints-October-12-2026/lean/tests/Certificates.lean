import Dowling
import Mathlib.GroupTheory.Perm.Finite

noncomputable section
open Dowling
open scoped Classical

example : StrictInverseZRow (matroid Unit 4 (∅ : Set (Fin 4))).eRank.toNat
    (MatroidInverseZ.matroidInverseZ (matroid Unit 4 ∅)) :=
  retained_dowling_inverseZ Unit 4 (by norm_num) ∅

example : StrictInverseZRow (matroid Unit 4 ({0} : Set (Fin 4))).eRank.toNat
    (MatroidInverseZ.matroidInverseZ (matroid Unit 4 {0})) :=
  retained_dowling_inverseZ Unit 4 (by norm_num) {0}

example : StrictInverseZRow (matroid Unit 5 ({0,2} : Set (Fin 5))).eRank.toNat
    (MatroidInverseZ.matroidInverseZ (matroid Unit 5 {0,2})) :=
  retained_dowling_inverseZ Unit 5 (by norm_num) {0,2}

example : StrictInverseZRow (matroid Unit 4 Set.univ).eRank.toNat
    (MatroidInverseZ.matroidInverseZ (matroid Unit 4 Set.univ)) :=
  retained_dowling_inverseZ Unit 4 (by norm_num) Set.univ

example : StrictInverseZRow (matroid (Equiv.Perm (Fin 3)) 4 ({0,2} : Set (Fin 4))).eRank.toNat
    (MatroidInverseZ.matroidInverseZ (matroid (Equiv.Perm (Fin 3)) 4 {0,2})) :=
  retained_dowling_inverseZ (Equiv.Perm (Fin 3)) 4 (by norm_num) {0,2}

example : StrictInverseZRow (matroid (Equiv.Perm (Fin 2)) 2 (∅ : Set (Fin 2))).eRank.toNat
    (MatroidInverseZ.matroidInverseZ (matroid (Equiv.Perm (Fin 2)) 2 ∅)) :=
  retained_dowling_inverseZ (Equiv.Perm (Fin 2)) 2 (by norm_num) ∅

example : configurationY (G := Equiv.Perm (Fin 3)) (∅ : Set (Fin 1))=1 :=
  configurationY_one_empty

example : configurationY (G := Unit) ({0} : Set (Fin 1))=1+Polynomial.X :=
  configurationY_one_nonempty {0} ⟨0,by simp⟩

example : (configurationY (G := Unit) (∅ : Set (Fin 4))).natDegree=3 :=
  (trivial_jointless_main (G := Unit) 3).1

example : (configurationY (G := Unit) ({0} : Set (Fin 4))).natDegree=4 :=
  retained_natDegree (by norm_num) {0} (Or.inr ⟨0,by simp⟩)

example : 0<(configurationY (G := Unit) ({0,2} : Set (Fin 5))).coeff 3 :=
  apex_retained_positive (by norm_num) {0,2} ⟨0,by simp⟩ 3 (by norm_num)

example : (configurationY (G := Unit) ({0} : Set (Fin 4))).coeff 1*
    (configurationY (G := Unit) ({0} : Set (Fin 4))).coeff 3<
    ((configurationY (G := Unit) ({0} : Set (Fin 4))).coeff 2)^2 :=
  apex_retained_strict (by norm_num) {0} ⟨0,by simp⟩ 2 (by norm_num) (by norm_num)

example : (configurationY (G := Equiv.Perm (Fin 2)) (∅ : Set (Fin 2))).coeff 0*
    (configurationY (G := Equiv.Perm (Fin 2)) (∅ : Set (Fin 2))).coeff 2<
    ((configurationY (G := Equiv.Perm (Fin 2)) (∅ : Set (Fin 2))).coeff 1)^2 :=
  retained_nontrivial_strict (by norm_num) ∅ 1 (by norm_num) (by norm_num)

example : (configurationY (G := Unit) ({0,2} : Set (Fin 5))).coeff 1=
    (configurationY (G := Unit) ({0,2} : Set (Fin 5))).coeff 4 :=
  retained_coeff_symm (by norm_num) {0,2} (Or.inr ⟨0,by simp⟩) 1 (by norm_num)

example : (configurationY (G := Unit) ({0} : Set (Fin 4))).coeff 5=0 :=
  retained_coeff_above (by norm_num) {0} (Or.inr ⟨0,by simp⟩) 5 (by norm_num)

example : apexNormalizedWeight 4 1 0=
    ((4 : ℝ)/(4+1))^0*((4+1)/2)^2/(4/2)^2*
      apexClosedRatio (4/2) ((4+1)/2-0)/4 :=
  by simpa only [Nat.cast_ofNat, Nat.cast_zero] using apexNormalizedWeight_one_closed 4 0 (by norm_num) (by norm_num)

example : apexNormalizedWeight 4 1 2=
    ((4 : ℝ)/(4+1))^2*((4+1)/2)^2/(4/2)^2*
      apexClosedRatio (4/2) ((4+1)/2-2)/4 :=
  by simpa only [Nat.cast_ofNat] using apexNormalizedWeight_one_closed 4 2 (by norm_num) (by norm_num)

example : StrictInverseZRow 0 (fullY Unit 0) := full_dowling_inverseZ 0
