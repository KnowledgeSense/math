import Paving.ActualMixtures
import Paving.GeometricMixturePayment
import Paving.EvenMixtures
import Paving.HyperplaneWeight

noncomputable section
open Finset
namespace Paving
variable {α : Type*} [Fintype α]

theorem hyperplaneWeight_bound (M : Matroid α) (hr : 2 ≤ rank M) (H : StressedIndex M) :
    hyperplaneWeight M H ≤ (H.val.ncard:ℝ)/
      ((H.val.ncard:ℝ)+(rank M-1:ℕ)*(M.E.ncard-H.val.ncard:ℕ)) := by
  have hh := (mem_stressedHyperplanes M H.val).mp H.property
  have hlt := hyperplane_card_lt hh.1
  have hb := choose_weight_ratio_bound (h:=H.val.ncard) (s:=M.E.ncard-H.val.ncard)
    (r:=rank M-1) (by omega) (by omega)
  rw [Nat.add_sub_of_le hlt.le] at hb
  exact hb

theorem actualPosition_bounds (M : Matroid α) (m : ℕ) (_hm : 1 ≤ m) (hr : rank M=2*m)
    (j : MixtureIndex M) :
    (m:ℝ)-1 ≤ componentPosition m (actualParameter M j) ∧
      componentPosition m (actualParameter M j) ≤ (M.E.ncard:ℝ)-m-1 := by
  have hn : 2*m ≤ M.E.ncard := hr ▸ rank_le_ground_card M
  cases j with
  | none =>
    have hnR : (2:ℝ)*m ≤ M.E.ncard := by exact_mod_cast hn
    simp only [actualParameter,componentPosition]
    constructor <;> linarith
  | some H =>
    have hh := (mem_stressedHyperplanes M H.val).mp H.property
    have hlo : (2:ℝ)*m ≤ H.val.ncard := by exact_mod_cast (hr ▸ hh.2)
    have hhi : (H.val.ncard:ℝ)+1 ≤ M.E.ncard := by exact_mod_cast hyperplane_card_lt hh.1
    simp only [actualParameter,componentPosition]
    constructor <;> linarith

theorem IsPaving.actual_large_payment {M : Matroid α} (hM : IsPaving M)
    (m : ℕ) (hm : 2 ≤ m) (hr : rank M=2*m) (j : MixtureIndex M)
    (hj : (M.E.ncard:ℝ)-m+m-2 < 2*componentPosition m (actualParameter M j)) :
    actualWeight M j ≤ (componentPosition m (actualParameter M j)+m)/
      (componentPosition m (actualParameter M j)+m+(2*m-1)*
        ((M.E.ncard:ℝ)-m-componentPosition m (actualParameter M j))) ∧
    ∀i:MixtureIndex M,i≠j → componentPosition m (actualParameter M i) ≤
      (M.E.ncard:ℝ)-m+m-2-componentPosition m (actualParameter M j) := by
  have hn : 2*m ≤ M.E.ncard := hr ▸ rank_le_ground_card M
  have hnR : (2:ℝ)*m ≤ M.E.ncard := by exact_mod_cast hn
  cases j with
  | none =>
    simp only [actualParameter,componentPosition] at hj
    linarith
  | some H =>
    have hh := (mem_stressedHyperplanes M H.val).mp H.property
    have hlt := hyperplane_card_lt hh.1
    constructor
    · have hb := hyperplaneWeight_bound M (by omega) H
      change hyperplaneWeight M H ≤ _
      simp only [actualParameter,componentPosition]
      convert hb using 1
      rw [Nat.cast_sub (by omega : 1 ≤ rank M),Nat.cast_sub hlt.le,hr]
      push_cast
      ring
    · intro i hi
      cases i with
      | none =>
        have hhi : (H.val.ncard:ℝ)+1 ≤ M.E.ncard := by exact_mod_cast hlt
        simp only [actualParameter,componentPosition]
        linarith
      | some K =>
        have hk := (mem_stressedHyperplanes M K.val).mp K.property
        have hne : H.val≠K.val := by
          intro he
          apply hi
          congr 1
          exact Subtype.ext he.symm
        have hg := hM.hyperplane_size_coupling hh.1 hk.1 hne
        have hgR : (H.val.ncard:ℝ)+K.val.ncard+2 ≤ M.E.ncard+2*m := by
          exact_mod_cast (hr ▸ hg)
        simp only [actualParameter,componentPosition]
        linarith

theorem IsPaving.actual_penultimate_floor {M : Matroid α} (hM : IsPaving M)
    (m : ℕ) (hm : 2 ≤ m) (hr : rank M=2*m) :
    penultimateFloor (middleBinomial m) ((M.E.ncard:ℝ)-m) m <
      ∑j:MixtureIndex M,actualWeight M j*lowerComponent (2*m) M.E.ncard (actualParameter M j) (m-1) := by
  have hn : 2*m ≤ M.E.ncard := hr ▸ rank_le_ground_card M
  have hnr : (2:ℝ)*m ≤ M.E.ncard := by exact_mod_cast hn
  have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
  simp_rw [lowerComponent_penultimate (by omega : 1 ≤ m) hn _ (hr ▸ actualParameter_valid M _)]
  apply geometric_mixture_payment univ (actualWeight M) (fun j => componentPosition m (actualParameter M j))
    (middleBinomial m) m ((M.E.ncard:ℝ)-m) (middleBinomial_positive (by omega)) hmr (by linarith)
  · intro j _; exact hM.actualWeight_nonneg (by omega) j
  · exact actualWeight_sum M
  · intro j _; exact actualPosition_bounds M m (by omega) hr j
  · intro j _ hj
    exact ⟨(hM.actual_large_payment m hm hr j hj).1,
      fun i _ hi => (hM.actual_large_payment m hm hr j hj).2 i hi⟩

theorem IsPaving.actual_penultimate_strict {M : Matroid α} (hM : IsPaving M)
    (m : ℕ) (hm : 2 ≤ m) (hr : rank M=2*m) :
    (∑j:MixtureIndex M,actualWeight M j*lowerComponent (2*m) M.E.ncard (actualParameter M j) (m-2))*
      ((∑j:MixtureIndex M,actualWeight M j*lowerComponent (2*m) M.E.ncard (actualParameter M j) (m-1))+
        middleIncrement (middleBinomial m) ((M.E.ncard:ℝ)-m) m) <
      (∑j:MixtureIndex M,actualWeight M j*lowerComponent (2*m) M.E.ncard (actualParameter M j) (m-1))^2 := by
  apply even_penultimate_mixture_strict univ (actualWeight M) (actualParameter M) m M.E.ncard hm
    (hr ▸ rank_le_ground_card M)
  · intro j _; exact hM.actualWeight_nonneg (by omega) j
  · exact actualWeight_sum M
  · intro j _; exact hr ▸ actualParameter_valid M j
  · exact (hM.actual_penultimate_floor m hm hr).le

end Paving
