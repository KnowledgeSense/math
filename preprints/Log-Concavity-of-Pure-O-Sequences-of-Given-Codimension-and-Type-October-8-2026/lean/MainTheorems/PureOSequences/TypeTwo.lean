/-
Copyright 2026 Google LLC
Adapted from AlphaProof Nexus Results, under the Apache 2.0 license.
See THIRD_PARTY_LICENSES/Apache-2.0.txt.
-/
import MainTheorems.PureOSequences.CoordinateCounts
import Mathlib.CategoryTheory.ComposableArrows.Basic
import Mathlib.Basic.Real.Basic

namespace ResearchMain.PureOSequences.TypeTwo

open ResearchMain.PureOSequences

set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

lemma type_two_implies_two_maximals {r : ℕ} (P : PureOrderIdeal r) (h_type : typePO P = 2) :
    ∃ m1 m2, m1 ≠ m2 ∧ maximalMonomials P.ideal = {m1, m2} := by
  exact Finset.card_eq_two.mp h_type

lemma ideal_carrier_eq_union {r : ℕ} (P : PureOrderIdeal r) (m1 m2 : Monomial r)
    (h_max_eq : maximalMonomials P.ideal = {m1, m2}) :
    P.ideal.carrier = divisorsFinset m1 ∪ divisorsFinset m2 := by
  classical
  ext m
  constructor
  · intro hm
    obtain ⟨g, hg, hmg⟩ := exists_le_maximal P.ideal m hm
    have hpair : g = m1 ∨ g = m2 := by
      simpa only [h_max_eq, Finset.mem_insert, Finset.mem_singleton] using hg
    rcases hpair with rfl | rfl
    · exact Finset.mem_union_left _ (mem_divisorsFinset_iff.mpr hmg)
    · exact Finset.mem_union_right _ (mem_divisorsFinset_iff.mpr hmg)
  · intro hm
    have hm1 : m1 ∈ P.ideal.carrier := by
      apply (mem_maximalMonomials_iff P.ideal m1).mp
        (by simp only [h_max_eq, Finset.mem_insert, true_or])
      |>.1
    have hm2 : m2 ∈ P.ideal.carrier := by
      have hmax : m2 ∈ maximalMonomials P.ideal := by simp [h_max_eq]
      exact (mem_maximalMonomials_iff P.ideal m2).mp hmax |>.1
    rcases Finset.mem_union.mp hm with h | h
    · exact P.ideal.downward_closed hm1 (mem_divisorsFinset_iff.mp h)
    · exact P.ideal.downward_closed hm2 (mem_divisorsFinset_iff.mp h)

lemma exists_single_greater_var {m1 m2 : Monomial 3} (h_deg : totalDeg m1 = totalDeg m2) (h_neq : m1 ≠ m2) :
    (∃ x : Fin 3, m1 x > m2 x ∧ ∀ y, y ≠ x → m1 y ≤ m2 y) ∨
    (∃ x : Fin 3, m2 x > m1 x ∧ ∀ y, y ≠ x → m2 y ≤ m1 y) := by
  have hsum : m1 0 + m1 1 + m1 2 = m2 0 + m2 1 + m2 2 := by
    simpa only [totalDeg_eq_sum_univ, Fin.sum_univ_three] using h_deg
  have hne : m1 0 ≠ m2 0 ∨ m1 1 ≠ m2 1 ∨ m1 2 ≠ m2 2 := by
    by_contra h
    push Not at h
    apply h_neq
    ext i
    fin_cases i <;> tauto
  norm_num [Fin.exists_iff_succ, Fin.forall_iff_succ]
  omega

lemma filter_union_card_eq_add_diff {α : Type*} [DecidableEq α] (s1 s2 : Finset α) (p : α → Prop) [DecidablePred p] :
    (Finset.filter p (s1 ∪ s2)).card = (Finset.filter p s1).card + (Finset.filter p (s2 \ s1)).card := by
  exact (congr_arg ↑_ (by grind) ).trans ( Finset.card_union_of_disjoint (Finset.disjoint_left.mpr ↑(by simp_all)))

noncomputable def reduced_monomial (m1 m2 : Monomial 3) (x : Fin 3) : Monomial 3 :=
  Finsupp.equivFunOnFinite.symm (fun y => if y = x then m2 y - m1 y - 1 else m2 y)

lemma pureOSeq_decomposition {m1 m2 : Monomial 3} (x : Fin 3)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (d : ℕ) :
    (Finset.filter (fun m => totalDeg m = d) (divisorsFinset m1 ∪ divisorsFinset m2)).card =
    (Finset.filter (fun m => totalDeg m = d) (divisorsFinset m1)).card +
    if d ≥ m1 x + 1 then
      (Finset.filter (fun m => totalDeg m = d - (m1 x + 1)) (divisorsFinset (reduced_monomial m1 m2 x))).card
    else 0 := by
  have h1 := filter_union_card_eq_add_diff (divisorsFinset m1) (divisorsFinset m2) (fun m => totalDeg m = d)
  delta reduced_monomial totalDeg Monomial Ne divisorsFinset at*
  simp_all -contextual [divisorsFinset,totalDeg, Finsupp.sum_of_support_subset (s:=⊤), Finset.filter_union,Nat.sub_sub _ _ _]
  split
  · apply Finset.card_bij
    show∀ a ∈ _, Finsupp.equivFunOnFinite.symm ( fun and=>ite (and=x) (a x - (m1 x + 1)) (a and)) ∈_
    · norm_num[ Finsupp.le_def]
      obtain ⟨@c⟩ :=eq_or_ne x 0
      · use fun and A B R L=>⟨ (by bound),L▸.trans ( Fin.sum_univ_three _) ((symm (.trans (by rw [ Fin.sum_univ_three]) (by_contra (absurd (h_le 1) ∘ fun and=>absurd (h_le 2) ∘by grind)))))⟩
      use fun and a s A B=>B▸⟨by bound,Nat.eq_sub_of_add_eq (.trans (?_) ( Finset.sum_erase_add _ _ (Finset.mem_univ x)))⟩
      norm_num[← Finset.sum_erase_add _ _ (Finset.mem_univ x), Finset.sum_congr rfl fun and μ=>ite_eq_right _,Nat.succ_le_iff, add_assoc, add_left_comm, (by_contra (not_le.2 A ∘(a s).trans ∘h_le s)▸A)]
      cases (by_contra (by valid ∘(a s).trans ∘(h_le s))) with grind
    · use fun and R M a s=>and.ext (if α:. = _ then α▸by_contra fun and=>absurd (congrFun (Equiv.injective _ s) x) ?_ else (ite_eq_right α▸congrFun (Equiv.injective _ s) _)▸ite_eq_right α)
      simp_all[]
      use R.1.2 ∘fun A B=> if I: B = _ then I▸not_lt.1 (a.1.2 ∘fun K V=> if I:V = _ then(I▸not_lt.1 (and ∘by valid))else(a.1.1 V).trans (h_le V I))else(R.1.1 B).trans (h_le B I)
    norm_num
    use fun and R M=>⟨∑B, and B •.single B (1)+.single x (m1 x+1), ⟨⟨ fun and=>? _,mt (. x) ?_⟩,?_⟩,Equiv.symm_apply_eq _|>.2 (funext ? _)⟩
    · if k:and=x then norm_num[*,(R x).trans, Finsupp.single_apply,←Nat.le_sub_iff_add_le _,Nat.succ_le_iff]else norm_num[k,(R and).trans, Finsupp.single_apply,id]
    · norm_num[add_left_comm]
    · norm_num[*, Finsupp.single_apply, Finset.sum_add_distrib,Nat.succ_le_iff]
    · simp_all[comm]
  · refine(congr_arg _) (Finset.filter_false_of_mem fun and R M=>(Finset.mem_sdiff.1 R).elim fun and true => true (Finset.mem_Iic.2 ?_))
    exact ( if a :· = _ then a▸(M▸ Finset.single_le_sum (by valid) ( Finset.mem_univ _)).trans (not_lt.mp (by assumption))else(Finset.mem_Iic.mp and _).trans ( (h_le _) a))
noncomputable def h_seq (m : Monomial 3) (d : ℕ) : ℕ :=
  (Finset.filter (fun m' => totalDeg m' = d) (divisorsFinset m)).card

def diff (h : ℕ → ℤ) (d : ℕ) : ℤ :=
  if d = 0 then h 0 else h d - h (d - 1)

def diff2 (h : ℕ → ℤ) (d : ℕ) : ℤ :=
  if d = 0 then diff h 0 else diff h d - diff h (d - 1)

def L_seq (A B d : ℕ) : ℕ :=
  (Finset.filter (fun x => d - x < B ∧ x ≤ d) (Finset.range A)).card

lemma delta_L (A B d : ℕ) (hd : d > 0) :
  (L_seq A B d : ℤ) - (L_seq A B (d - 1) : ℤ) =
  (if d < A then 1 else 0) + (if d < B then 1 else 0) - (if d < A + B then 1 else 0) := by
  push_cast[d.sub_add_cancel hd▸L_seq /em, L_seq, sub_eq_sub_iff_add_eq_add]
  refine match(d) with | S+1=>mod_cast match A with|0=> by aesop|n + 1=>.trans (by rw [ Finset.card_filter, Finset.sum_range_succ']) (.symm (.trans (by rw [ Finset.card_filter, Finset.sum_range_succ]) (by grind)))

def H_calc (A B C d : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (d + 1), if d - k < C then L_seq A B k else 0

lemma H_eq_H_calc (m : Monomial 3) (d : ℕ) :
  ((divisorsFinset m).filter (fun x => totalDeg x = d)).card =
  H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) d := by
  delta totalDeg divisorsFinset H_calc Monomial at*
  trans{ a ∈.Icc 0 (m 0) ×ˢ Finset.Icc 0 (m (1 ) ) ×ˢ.Icc 0 (m (2)) | a.fst+ a.snd.fst+ a.snd.snd = d}.card
  · refine Finset.card_equiv ⟨ fun and=> (and 0, and (1), and 2), fun and=> Finsupp.equivFunOnFinite.symm (@![ _,_, _]), fun and=> Finsupp.ext ↑(by simp_all[ Fin.forall_fin_succ]), fun and=>rfl⟩ ?_
    norm_num[Fin.sum_univ_three,Finsupp.sum_of_support_subset (s:=⊤),Finsupp.le_def,Fin.forall_iff_succ]
    intro i
    rfl
  push_cast[add_comm, L_seq,←Nat.range_succ_eq_Icc_zero, Finset.card_filter, Finset.sum_product_right]
  rw [←funext fun and=> Finset.sum_comm, Finset.sum_comm,eq_comm,← Finset.sum_filter]
  refine Finset.sum_comm.trans ( Finset.sum_congr rfl fun and x =>( Finset.sum_filter _ _).symm.trans (.trans (? _) Finset.sum_comm))
  rw [← Finset.sum_product']
  exact ( Finset.sum_bij (fun a s=>(a-and, d-a)) (by simp_all[·.lt_succ_iff]) (by simp_all[tsub_left_inj]) (fun(a, b)R=>⟨a+and, by aesop⟩) (by valid)).trans ( Finset.sum_filter _ _)

lemma delta_H_calc (A B C d : ℕ) (hd : d > 0) :
  (H_calc A B C d : ℤ) - (H_calc A B C (d - 1) : ℤ) =
  (L_seq A B d : ℤ) - (if d ≥ C then (L_seq A B (d - C) : ℤ) else 0) := by
  simp_rw [.>·, sub_eq_sub_iff_add_eq_add, H_calc] at*
  refine(d.sub_add_cancel hd).symm▸mod_cast match(d) with | S+1 =>.trans (by rw [ Finset.sum_range_succ_comm, add_assoc]) @?_
  refine(S+1).sub_self.symm▸match C with|0=>by norm_num|n + 1=>congr_arg _ (( Finset.sum_congr rfl fun and μ=>if_congr .rfl rfl rfl ).trans (? _)).symm
  refine(em _).elim (ite_eq_left ·▸ (Finset.sum_eq_add_sum_sdiff_singleton_of_mem (List.mem_range.2 (by valid: S-n<_)) _).trans (?_)) (ite_eq_right ·▸.trans ( Finset.sum_congr rfl (by grind)) (add_zero _).symm)
  exact (congr_arg₂ @_ (ite_eq_left (by valid) |>.trans (by rw [ S.add_sub_add_right])) (( Finset.sum_congr ↑rfl fun and (R) =>if_congr (by·grind) rfl rfl ).trans ( Finset.sum_subset Finset.sdiff_subset fun and R L=>ite_eq_right (by (grind))))).trans (add_comm _ _)

def Z_calc (A B C d : ℕ) : ℤ :=
  (if d < A then 1 else 0) + (if d < B then 1 else 0) + (if d < C then 1 else 0)
  - (if d < A + B then 1 else 0) - (if d < B + C then 1 else 0) - (if d < C + A then 1 else 0)
  + (if d < A + B + C then 1 else 0)

lemma L_seq_zero (A B : ℕ) :
  (L_seq A B 0 : ℤ) = if 0 < A ∧ 0 < B then 1 else 0 := by
  norm_num[L_seq, true,pos_iff_ne_zero]
  cases A with cases B with norm_num[ Finset.filter_eq']

lemma H_calc_zero (A B C : ℕ) :
  H_calc A B C 0 = if 0 < C then L_seq A B 0 else 0 := by
  unfold H_calc
  rw [Finset.sum_range_one]

lemma diff2_H_calc_eq_1 (A B C : ℕ) :
  diff2 (fun k => (H_calc A B C k : ℤ)) 1 = Z_calc A B C 1 := by
  delta H_calc diff2 Z_calc
  norm_num[diff,Finset.sum_range_succ,L_seq,sub_sub,Nat.one_lt_iff_ne_zero_and_ne_one]
  match A with|0| (1) | S+2=>_
  · norm_num
  · match B with|0|1 | S+2=>match C with|0|1 | S+2=>simp_all[ Finset.filter_singleton, add_assoc,Nat.add_eq_one_iff]
  simp_all[add_comm (1 : ℤ),pos_iff_ne_zero, sub_add,Nat.add_eq_one_iff, Finset.filter_and, Finset.filter_or, Finset.filter_eq',Nat.le_succ_iff]
  match B with|0|1 | S+2=>cases C with simp_all[add_comm]

lemma diff2_H_calc_d_unfold (A B C d : ℕ) (hd : d > 1) :
  diff2 (fun k => (H_calc A B C k : ℤ)) d =
  (L_seq A B d : ℤ) - (if d ≥ C then (L_seq A B (d - C) : ℤ) else 0) -
  ((L_seq A B (d - 1) : ℤ) - (if d - 1 ≥ C then (L_seq A B (d - 1 - C) : ℤ) else 0)) := by
  unfold diff2 diff
  have h_d0 : d ≠ 0 := by omega
  have h_d1 : d - 1 ≠ 0 := by omega
  rw [ite_eq_right h_d0, ite_eq_right h_d0, ite_eq_right h_d1]
  have h1 := delta_H_calc A B C d (by omega)
  have h2 := delta_H_calc A B C (d - 1) (by omega)
  linarith

lemma diff2_H_calc_L2 (A B C d : ℕ) (hd : d > 1) :
  (if d ≥ C then (L_seq A B (d - C) : ℤ) else 0) - (if d - 1 ≥ C then (L_seq A B (d - 1 - C) : ℤ) else 0) =
    if d > C then (L_seq A B (d - C) : ℤ) - (L_seq A B (d - 1 - C) : ℤ) else if d = C then (L_seq A B 0 : ℤ) else 0 := by
  have hdC : d > C ∨ d = C ∨ d < C := by omega
  rcases hdC with hd_gt | hd_eq | hd_lt
  · have h1 : d ≥ C := by omega
    have h2 : d - 1 ≥ C := by omega
    have h3 : d > C := hd_gt
    rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h3]
  · have h1 : d ≥ C := by omega
    have h2 : ¬(d - 1 ≥ C) := by omega
    have h3 : ¬(d > C) := by omega
    have h4 : d = C := hd_eq
    rw [ite_eq_left h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]
    have h_sub : d - C = 0 := by omega
    rw [h_sub]
    ring
  · have h1 : ¬(d ≥ C) := by omega
    have h2 : ¬(d - 1 ≥ C) := by omega
    have h3 : ¬(d > C) := by omega
    have h4 : ¬(d = C) := by omega
    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_right h4]
    ring

lemma diff2_H_calc_eq_d (A B C d : ℕ) (hd : d > 1) :
  diff2 (fun k => (H_calc A B C k : ℤ)) d = Z_calc A B C d := by
  rw [diff2_H_calc_d_unfold A B C d hd]
  have h_rearrange : (L_seq A B d : ℤ) - (if d ≥ C then (L_seq A B (d - C) : ℤ) else 0) - ((L_seq A B (d - 1) : ℤ) - (if d - 1 ≥ C then (L_seq A B (d - 1 - C) : ℤ) else 0)) = ((L_seq A B d : ℤ) - (L_seq A B (d - 1) : ℤ)) - ((if d ≥ C then (L_seq A B (d - C) : ℤ) else 0) - (if d - 1 ≥ C then (L_seq A B (d - 1 - C) : ℤ) else 0)) := by ring
  rw [h_rearrange]
  have h_L_delta := delta_L A B d (by omega)
  have h_L2 := diff2_H_calc_L2 A B C d hd
  rw [h_L2]
  rw [h_L_delta]
  have hdC : d > C ∨ d = C ∨ d < C := by omega
  rcases hdC with hd_gt | hd_eq | hd_lt
  · have h1 : d > C := hd_gt
    have h2 : d ≠ C := by omega
    rw [ite_eq_left h1]
    have h_L_delta_C := delta_L A B (d - C) (by omega)
    have h_sub : d - 1 - C = d - C - 1 := by omega
    rw [h_sub]
    rw [h_L_delta_C]
    unfold Z_calc
    omega
  · rw [hd_eq]
    have h1 : ¬(C > C) := by omega
    have h2 : C = C := rfl
    rw [ite_eq_right h1, ite_eq_left h2]
    have h_L0 := L_seq_zero A B
    rw [h_L0]
    unfold Z_calc
    omega
  · have h1 : ¬(d > C) := by omega
    have h2 : d ≠ C := by omega
    rw [ite_eq_right h1, ite_eq_right h2]
    unfold Z_calc
    omega

lemma diff2_H_calc_eq (A B C d : ℕ) (hd : d > 0) :
  diff2 (fun k => (H_calc A B C k : ℤ)) d = Z_calc A B C d := by
  have h_cases : d = 1 ∨ d > 1 := by omega
  rcases h_cases with hd1 | hd_gt1
  · rw [hd1]
    exact diff2_H_calc_eq_1 A B C
  · exact diff2_H_calc_eq_d A B C d hd_gt1

lemma Z_calc_le_one (A B C d : ℕ) : Z_calc A B C d ≤ 1 := by
  unfold Z_calc
  omega

lemma diff2_eq_func {h1 h2 : ℕ → ℤ} (heq : ∀ d, h1 d = h2 d) (d : ℕ) :
  diff2 h1 d = diff2 h2 d := by
  have h_fun : h1 = h2 := funext heq
  rw [h_fun]

lemma diff2_h_seq_le_one (m : Monomial 3) (d : ℕ) :
  diff2 (fun k => (h_seq m k : ℤ)) d ≤ 1 := by
  have h_cases : d = 0 ∨ d > 0 := by omega
  rcases h_cases with h0 | hd
  · rw [h0]
    unfold diff2 diff
    have hz1 : (0:ℕ) = 0 := rfl
    rw [ite_eq_left hz1, ite_eq_left hz1]
    have h_seq_zero : h_seq m 0 = 1 := boxCount_degree_zero m
    have h_val : (fun k => (h_seq m k : ℤ)) 0 = (h_seq m 0 : ℤ) := rfl
    rw [h_val, h_seq_zero]
    omega
  · have h_eq : ∀ k, (fun j => (h_seq m j : ℤ)) k = (fun j => (H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) j : ℤ)) k := by
      intro k
      have h1 : h_seq m k = H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) k := by
        unfold h_seq
        exact H_eq_H_calc m k
      have h2 : (fun j => (h_seq m j : ℤ)) k = (h_seq m k : ℤ) := rfl
      have h3 : (fun j => (H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) j : ℤ)) k = (H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) k : ℤ) := rfl
      rw [h2, h3, h1]
    have h_diff2 : diff2 (fun k => (h_seq m k : ℤ)) d = diff2 (fun k => (H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) k : ℤ)) d := diff2_eq_func h_eq d
    rw [h_diff2]
    rw [diff2_H_calc_eq _ _ _ _ hd]
    exact Z_calc_le_one _ _ _ _

lemma log_concave_core (x y z : ℤ) (hx : x ≥ 0) (hz : z ≤ 2) (hy : z = 1 → y^2 ≥ x) (hy2 : z = 2 → y^2 ≥ 2*x) :
  y^2 ≥ x * z := by
  have h_cases : z ≤ 0 ∨ z = 1 ∨ z = 2 := by omega
  rcases h_cases with h0 | h1 | h2
  · have h1 : x * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hx h0
    have h2 : 0 ≤ y^2 := sq_nonneg y
    omega
  · rw [h1]
    have h3 : y^2 ≥ x := hy h1
    omega
  · rw [h2]
    have h3 : y^2 ≥ 2*x := hy2 h2
    omega

lemma diff_eq (h : ℕ → ℤ) (d : ℕ) (hd : d > 0) :
  h d = h (d - 1) + diff h d := by
  unfold diff
  have h0 : d ≠ 0 := by omega
  rw [ite_eq_right h0]
  omega

lemma diff2_eq (h : ℕ → ℤ) (d : ℕ) (hd : d > 0) :
  diff h (d + 1) = diff h d + diff2 h (d + 1) := by
  unfold diff2
  have h0 : d + 1 ≠ 0 := by omega
  rw [ite_eq_right h0]
  have h1 : d + 1 - 1 = d := by omega
  rw [h1]
  omega

noncomputable def shifted_h_seq (m : Monomial 3) (c : ℕ) (d : ℕ) : ℤ :=
  if d ≥ c then (h_seq m (d - c) : ℤ) else 0

lemma diff_add (h1 h2 : ℕ → ℤ) (d : ℕ) :
  diff (fun k => h1 k + h2 k) d = diff h1 d + diff h2 d := by
  unfold diff
  split_ifs
  · ring
  · ring

lemma diff2_add (h1 h2 : ℕ → ℤ) (d : ℕ) :
  diff2 (fun k => h1 k + h2 k) d = diff2 h1 d + diff2 h2 d := by
  unfold diff2
  split_ifs
  · rw [diff_add]
  · rw [diff_add, diff_add]
    ring

noncomputable def H_seq {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) : ℤ :=
  (h_seq m1 d + if d ≥ m1 x + 1 then h_seq (reduced_monomial m1 m2 x) (d - (m1 x + 1)) else 0 : ℕ)

lemma H_seq_eq_add {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) :
  H_seq (m1:=m1) (m2:=m2) x d = (fun k => (h_seq m1 k : ℤ)) d + shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) d := by
  unfold H_seq shifted_h_seq
  push_cast
  split_ifs
  · rfl
  · rfl

lemma diff2_h_seq_eq_Z_calc (m : Monomial 3) (d : ℕ) (hd : d > 0) :
  diff2 (fun k => (h_seq m k : ℤ)) d = Z_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) d := by
  have h_eq : ∀ k, (fun j => (h_seq m j : ℤ)) k = (fun j => (H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) j : ℤ)) k := by
    intro k
    exact congrArg (fun (x : ℕ) => (x : ℤ)) (H_eq_H_calc m k)
  have h_diff2 := diff2_eq_func h_eq d
  rw [h_diff2]
  exact diff2_H_calc_eq _ _ _ _ hd

lemma Z_calc_eq_one_cases (A B C d : ℕ) :
  Z_calc A B C d = 1 → (d < A ∧ d < B ∧ d < C) ∨ (d ≥ A + B ∧ d ≥ B + C ∧ d ≥ C + A ∧ d < A + B + C) := by
  unfold Z_calc
  omega

lemma diff2_h_seq_eq_one_implies_pos (m : Monomial 3) (d : ℕ) (hd : d > 0) :
  diff2 (fun k => (h_seq m k : ℤ)) d = 1 → (d ≤ m 0 ∧ d ≤ m 1 ∧ d ≤ m 2) ∨ (d ≥ m 0 + m 1 + 2 ∧ d ≥ m 1 + m 2 + 2 ∧ d ≥ m 0 + m 2 + 2 ∧ d ≤ m 0 + m 1 + m 2 + 2) := by
  have h_eq : ∀ k, (fun j => (h_seq m j : ℤ)) k = (fun j => (H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) j : ℤ)) k := by
    intro k
    have h1 : h_seq m k = H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) k := by
      unfold h_seq
      exact H_eq_H_calc m k
    exact congrArg (fun (x : ℕ) => (x : ℤ)) h1
  have h_diff2 : diff2 (fun k => (h_seq m k : ℤ)) d = diff2 (fun k => (H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) k : ℤ)) d := diff2_eq_func h_eq d
  rw [h_diff2]
  rw [diff2_H_calc_eq _ _ _ _ hd]
  intro h1
  have h2 := Z_calc_eq_one_cases (m 0 + 1) (m 1 + 1) (m 2 + 1) d h1
  rcases h2 with h_lt | h_ge
  · left
    omega
  · right
    omega

lemma diff2_h_seq_eq_one_implies (m : Monomial 3) (d : ℕ) :
  diff2 (fun k => (h_seq m k : ℤ)) d = 1 → (d ≤ m 0 ∧ d ≤ m 1 ∧ d ≤ m 2) ∨ (d ≥ m 0 + m 1 + 2 ∧ d ≥ m 1 + m 2 + 2 ∧ d ≥ m 0 + m 2 + 2 ∧ d ≤ m 0 + m 1 + m 2 + 2) := by
  have h_cases : d = 0 ∨ d > 0 := by omega
  rcases h_cases with hd0 | hd_pos
  · intro _
    left
    omega
  · exact diff2_h_seq_eq_one_implies_pos m d hd_pos

lemma diff2_shifted_h_seq_eq_zero_lt (m : Monomial 3) (c d : ℕ) (h : d < c) :
  diff2 (shifted_h_seq m c) d = 0 := by
  unfold diff2 diff shifted_h_seq
  split_ifs <;> omega

lemma diff2_shifted_h_seq_le_one_lt (m : Monomial 3) (c d : ℕ) (h : d < c) :
  diff2 (shifted_h_seq m c) d ≤ 1 := by
  rw [diff2_shifted_h_seq_eq_zero_lt m c d h]
  omega

lemma diff2_shifted_h_seq_eq_ge (m : Monomial 3) (c d : ℕ) (h : d ≥ c) :
  diff2 (shifted_h_seq m c) d = diff2 (fun k => (h_seq m k : ℤ)) (d - c) := by
  simp_all[diff2]
  delta shifted_h_seq diff
  match(d) with|0|1 | S+2 =>match c with|0|1 | S+2 =>grind

lemma diff2_shifted_h_seq_le_one_ge (m : Monomial 3) (c d : ℕ) (h : d ≥ c) :
  diff2 (shifted_h_seq m c) d ≤ 1 := by
  have h_eq : diff2 (shifted_h_seq m c) d = diff2 (fun k => (h_seq m k : ℤ)) (d - c) := diff2_shifted_h_seq_eq_ge m c d h
  rw [h_eq]
  exact diff2_h_seq_le_one m (d - c)

lemma diff2_shifted_h_seq_le_one (m : Monomial 3) (c d : ℕ) :
  diff2 (shifted_h_seq m c) d ≤ 1 := by
  have h_cases : d < c ∨ d ≥ c := by omega
  rcases h_cases with h_lt | h_ge
  · exact diff2_shifted_h_seq_le_one_lt m c d h_lt
  · exact diff2_shifted_h_seq_le_one_ge m c d h_ge

lemma diff2_shifted_h_seq_eq_one_implies (m : Monomial 3) (c d : ℕ) :
  diff2 (shifted_h_seq m c) d = 1 → d ≥ c := by
  intro h
  by_contra hc
  push Not at hc
  have h_zero := diff2_shifted_h_seq_eq_zero_lt m c d hc
  omega

lemma diff2_shifted_h_seq_eq_one_implies_eq (m : Monomial 3) (c d : ℕ) :
  diff2 (shifted_h_seq m c) d = 1 → diff2 (fun k => (h_seq m k : ℤ)) (d - c) = 1 := by
  intro h
  have hc := diff2_shifted_h_seq_eq_one_implies m c d h
  have h_eq : diff2 (shifted_h_seq m c) d = diff2 (fun k => (h_seq m k : ℤ)) (d - c) := diff2_shifted_h_seq_eq_ge m c d hc
  omega

lemma H_seq_eval_add {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) :
  H_seq (m1:=m1) (m2:=m2) x d = (h_seq m1 d : ℤ) + shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) d := by
  exact H_seq_eq_add x d

lemma diff_H_seq_eval_add {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) :
  diff (H_seq (m1:=m1) (m2:=m2) x) d = diff (fun k => (h_seq m1 k : ℤ)) d + diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d := by
  have h_eq : H_seq (m1:=m1) (m2:=m2) x = fun k => (fun j => (h_seq m1 j : ℤ)) k + shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) k := by
    funext k
    exact H_seq_eq_add x k
  rw [h_eq, diff_add]

lemma diff2_H_seq_eq_add {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) :
  diff2 (H_seq (m1:=m1) (m2:=m2) x) d = diff2 (fun k => (h_seq m1 k : ℤ)) d + diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d := by
  have h_eq : H_seq (m1:=m1) (m2:=m2) x = fun k => (fun j => (h_seq m1 j : ℤ)) k + shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) k := by
    funext k
    exact H_seq_eq_add x k
  rw [h_eq, diff2_add]

lemma diff2_H_seq_le_two {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) :
  diff2 (H_seq (m1:=m1) (m2:=m2) x) d ≤ 2 := by
  rw [diff2_H_seq_eq_add]
  have h1 := diff2_h_seq_le_one m1 d
  have h2 := diff2_shifted_h_seq_le_one (reduced_monomial m1 m2 x) (m1 x + 1) d
  omega

lemma h_seq_pure_lower (m : Monomial 3) (d : ℕ) (h : d ≤ m 0 ∧ d ≤ m 1 ∧ d ≤ m 2) :
  (h_seq m d : ℤ) * 2 = (d + 1) * (d + 2) := by
  exact_mod_cast boxCount_three_saturated m d h.1 h.2.1 h.2.2

lemma h_seq_pure_lower_diff (m : Monomial 3) (d : ℕ) (h : d + 1 ≤ m 0 ∧ d + 1 ≤ m 1 ∧ d + 1 ≤ m 2) :
  diff (fun k => (h_seq m k : ℤ)) (d + 1) = d + 2 := by
  have h1 : (h_seq m (d + 1) : ℤ) * 2 = (d + 2) * (d + 3) := by
    apply h_seq_pure_lower
    omega
  have h2 : (h_seq m d : ℤ) * 2 = (d + 1) * (d + 2) := by
    apply h_seq_pure_lower
    omega
  unfold diff
  have h_ne : d + 1 ≠ 0 := by omega
  rw [ite_eq_right h_ne]
  have h_sub : d + 1 - 1 = d := by omega
  rw [h_sub]
  have h_diff_mul : ((h_seq m (d + 1) : ℤ) - (h_seq m d : ℤ)) * 2 = (d + 2) * 2 := by
    calc
      ((h_seq m (d + 1) : ℤ) - (h_seq m d : ℤ)) * 2 = (h_seq m (d + 1) : ℤ) * 2 - (h_seq m d : ℤ) * 2 := by ring
      _ = (d + 2) * (d + 3) - (d + 1) * (d + 2) := by rw [h1, h2]
      _ = (d + 2) * 2 := by ring
  linarith

lemma h_seq_symm (m : Monomial 3) (d : ℕ) (hd : d ≤ m 0 + m 1 + m 2) :
  h_seq m d = h_seq m (m 0 + m 1 + m 2 - d) := by
  simpa only [boxCount, h_seq, totalDeg_eq_sum_univ, Fin.sum_univ_three] using
    boxCount_symmetry m d (by
      simpa only [totalDeg_eq_sum_univ, Fin.sum_univ_three] using hd)

lemma h_seq_upper_bound_int (m : Monomial 3) (d : ℕ) (h_le : d ≤ m 0 + m 1 + m 2) :
  (h_seq m d : ℤ) * 2 ≤ (m 0 + m 1 + m 2 - d + 1 : ℤ) * (m 0 + m 1 + m 2 - d + 2 : ℤ) := by
  rw [h_seq_symm m d h_le]
  have h := boxCount_three_bound m (m 0 + m 1 + m 2 - d)
  have hcast : (h_seq m (m 0 + m 1 + m 2 - d) : ℤ) * 2 ≤
      ((m 0 + m 1 + m 2 - d : ℕ) + 1 : ℤ) *
      ((m 0 + m 1 + m 2 - d : ℕ) + 2 : ℤ) := by exact_mod_cast h
  convert hcast using 1
  congr 1 <;> omega

lemma h_seq_pure_upper (m : Monomial 3) (d : ℕ) (h : d ≥ m 0 + m 1 ∧ d ≥ m 1 + m 2 ∧ d ≥ m 0 + m 2 ∧ d ≤ m 0 + m 1 + m 2 + 1) :
  (h_seq m d : ℤ) * 2 = (m 0 + m 1 + m 2 + 1 - d : ℤ) * (m 0 + m 1 + m 2 + 2 - d : ℤ) := by
  have h_cases : d ≤ m 0 + m 1 + m 2 ∨ d = m 0 + m 1 + m 2 + 1 := by omega
  rcases h_cases with hd | hd
  · have h_symm := h_seq_symm m d hd
    have h_eq : (h_seq m d : ℤ) = (h_seq m (m 0 + m 1 + m 2 - d) : ℤ) := congrArg Nat.cast h_symm
    rw [h_eq]
    have h_lower := h_seq_pure_lower m (m 0 + m 1 + m 2 - d) (by omega)
    have h_sub_cast : ((m 0 + m 1 + m 2 - d : ℕ) : ℤ) = m 0 + m 1 + m 2 - d := by omega
    rw [h_sub_cast] at h_lower
    have h_cast1 : (m 0 + m 1 + m 2 - d + 1 : ℤ) = (m 0 + m 1 + m 2 + 1 - d : ℤ) := by omega
    have h_cast2 : (m 0 + m 1 + m 2 - d + 2 : ℤ) = (m 0 + m 1 + m 2 + 2 - d : ℤ) := by omega
    rw [h_cast1, h_cast2] at h_lower
    exact h_lower
  · rw [hd]
    have h_zero : h_seq m (m 0 + m 1 + m 2 + 1) = 0 := by
      have h := boxCountZ_zero m ((m 0 + m 1 + m 2 + 1 : ℕ) : ℤ)
        (Or.inr (by
          simp only [totalDeg_eq_sum_univ, Fin.sum_univ_three]
          omega))
      rw [boxCountZ_nat] at h
      exact_mod_cast h
    have hz_cast : (h_seq m (m 0 + m 1 + m 2 + 1) : ℤ) = 0 := by exact congrArg Nat.cast h_zero
    rw [hz_cast]
    omega

lemma h_seq_pure_upper_diff (m : Monomial 3) (d : ℕ) (h : d ≥ m 0 + m 1 + 1 ∧ d ≥ m 1 + m 2 + 1 ∧ d ≥ m 0 + m 2 + 1 ∧ d ≤ m 0 + m 1 + m 2 + 1) :
  diff (fun k => (h_seq m k : ℤ)) d = - (m 0 + m 1 + m 2 + 2 - d : ℤ) := by
  have hd_upper : d ≥ m 0 + m 1 ∧ d ≥ m 1 + m 2 ∧ d ≥ m 0 + m 2 ∧ d ≤ m 0 + m 1 + m 2 + 1 := by omega
  have h1 : (h_seq m d : ℤ) * 2 = (m 0 + m 1 + m 2 + 1 - d : ℤ) * (m 0 + m 1 + m 2 + 2 - d : ℤ) := h_seq_pure_upper m d hd_upper
  have hd_1_upper : d - 1 ≥ m 0 + m 1 ∧ d - 1 ≥ m 1 + m 2 ∧ d - 1 ≥ m 0 + m 2 ∧ d - 1 ≤ m 0 + m 1 + m 2 + 1 := by omega
  have h2 : (h_seq m (d - 1) : ℤ) * 2 = (m 0 + m 1 + m 2 + 1 - (d - 1 : ℕ) : ℤ) * (m 0 + m 1 + m 2 + 2 - (d - 1 : ℕ) : ℤ) := h_seq_pure_upper m (d - 1) hd_1_upper
  unfold diff
  have h_ne : d ≠ 0 := by omega
  rw [ite_eq_right h_ne]
  have h_diff_mul : ((h_seq m d : ℤ) - (h_seq m (d - 1) : ℤ)) * 2 = - (m 0 + m 1 + m 2 + 2 - d : ℤ) * 2 := by
    calc
      ((h_seq m d : ℤ) - (h_seq m (d - 1) : ℤ)) * 2 = (h_seq m d : ℤ) * 2 - (h_seq m (d - 1) : ℤ) * 2 := by ring
      _ = (m 0 + m 1 + m 2 + 1 - d : ℤ) * (m 0 + m 1 + m 2 + 2 - d : ℤ) - (m 0 + m 1 + m 2 + 1 - (d - 1 : ℕ) : ℤ) * (m 0 + m 1 + m 2 + 2 - (d - 1 : ℕ) : ℤ) := by rw [h1, h2]
      _ = - (m 0 + m 1 + m 2 + 2 - d : ℤ) * 2 := by
        have hd_1 : ((d - 1 : ℕ) : ℤ) = d - 1 := by omega
        rw [hd_1]
        ring
  linarith

lemma int_add_eq_two_of_le_one (a b : ℤ) (ha : a ≤ 1) (hb : b ≤ 1) (hab : a + b = 2) : a = 1 ∧ b = 1 := by omega

lemma diff2_H_seq_eq_two_implies_both_one {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) :
  diff2 (H_seq (m1:=m1) (m2:=m2) x) d = 2 →
  diff2 (fun k => (h_seq m1 k : ℤ)) d = 1 ∧ diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d = 1 := by
  intro h
  have h_add : diff2 (fun k => (h_seq m1 k : ℤ)) d + diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d = 2 := by
    have hd_h := diff2_H_seq_eq_add (m1:=m1) (m2:=m2) x d
    rw [← hd_h, h]
  exact int_add_eq_two_of_le_one _ _ (diff2_h_seq_le_one m1 d) (diff2_shifted_h_seq_le_one (reduced_monomial m1 m2 x) (m1 x + 1) d) h_add

lemma int_add_eq_one_of_le_one_cases (a b : ℤ) (ha : a ≤ 1) (hb : b ≤ 1) (hab : a + b = 1) :
  (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by omega

lemma diff2_H_seq_eq_one_implies_cases {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) :
  diff2 (H_seq (m1:=m1) (m2:=m2) x) d = 1 →
  (diff2 (fun k => (h_seq m1 k : ℤ)) d = 1 ∧ diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d = 0) ∨
  (diff2 (fun k => (h_seq m1 k : ℤ)) d = 0 ∧ diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d = 1) := by
  intro h
  have h_add : diff2 (fun k => (h_seq m1 k : ℤ)) d + diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d = 1 := by
    have hd_h := diff2_H_seq_eq_add (m1:=m1) (m2:=m2) x d
    rw [← hd_h, h]
  exact int_add_eq_one_of_le_one_cases _ _ (diff2_h_seq_le_one m1 d) (diff2_shifted_h_seq_le_one (reduced_monomial m1 m2 x) (m1 x + 1) d) h_add

lemma log_concave_algebra_upper_eval (U1 U2 : ℤ) (h1 : U1 ≥ -1) (h2 : U2 ≥ -1) :
  (U1 + 2) * (U1 + 3) + (U2 + 2) * (U2 + 3) ≤ (- (U1 + 2) - (U2 + 2)) ^ 2 := by
  have heq : (- (U1 + 2) - (U2 + 2)) ^ 2 - ((U1 + 2) * (U1 + 3) + (U2 + 2) * (U2 + 3)) =
    2 * (U1 + 1) * (U2 + 1) + U1 + U2 + 2 := by ring
  have hp1 : U1 + 1 ≥ 0 := by omega
  have hp2 : U2 + 1 ≥ 0 := by omega
  nlinarith

lemma diff2_eq_one_reduction (H_d_minus_1 H_d_plus_1 diff_H_d diff_H_d_plus_1 : ℤ) :
  diff_H_d_plus_1 - diff_H_d = 1 →
  H_d_plus_1 - diff_H_d_plus_1 - diff_H_d = H_d_minus_1 →
  H_d_plus_1 ≤ diff_H_d_plus_1 ^ 2 →
  H_d_minus_1 ≤ diff_H_d ^ 2 := by
  intro h1 h2 h3
  have h4 : diff_H_d = diff_H_d_plus_1 - 1 := by linarith
  have h5 : H_d_minus_1 = H_d_plus_1 - 2 * diff_H_d_plus_1 + 1 := by linarith
  nlinarith

lemma H_seq_identity {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0) :
  H_seq (m1:=m1) (m2:=m2) x (d + 1) - diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1) - diff (H_seq (m1:=m1) (m2:=m2) x) d = H_seq (m1:=m1) (m2:=m2) x (d - 1) := by
  have h1 : H_seq (m1:=m1) (m2:=m2) x (d + 1) - H_seq (m1:=m1) (m2:=m2) x d = diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1) := by
    unfold diff
    have hz : d + 1 ≠ 0 := by omega
    rw [ite_eq_right hz]
    have hz2 : d + 1 - 1 = d := by omega
    rw [hz2]
  have h2 : H_seq (m1:=m1) (m2:=m2) x d - H_seq (m1:=m1) (m2:=m2) x (d - 1) = diff (H_seq (m1:=m1) (m2:=m2) x) d := by
    unfold diff
    have hz : d ≠ 0 := by omega
    rw [ite_eq_right hz]
  linarith

lemma H_seq_diff2_reduction {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0) :
  diff2 (H_seq (m1:=m1) (m2:=m2) x) (d + 1) = 1 →
  H_seq (m1:=m1) (m2:=m2) x (d + 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1))^2 →
  H_seq (m1:=m1) (m2:=m2) x (d - 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 := by
  intro h1 h2
  apply diff2_eq_one_reduction (H_seq (m1:=m1) (m2:=m2) x (d - 1)) (H_seq (m1:=m1) (m2:=m2) x (d + 1)) (diff (H_seq (m1:=m1) (m2:=m2) x) d) (diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1))
  · exact h1
  · exact H_seq_identity x d hd
  · exact h2

lemma shifted_h_seq_zero_of_lt (m : Monomial 3) (c d : ℕ) (h : d < c) :
  shifted_h_seq m c d = 0 := by
  unfold shifted_h_seq
  rw [ite_eq_right (by omega)]

lemma diff_shifted_h_seq_zero_of_lt (m : Monomial 3) (c d : ℕ) (hd : d > 0) (h : d < c) :
  diff (shifted_h_seq m c) d = 0 := by
  unfold diff
  have h_ne : d ≠ 0 := by omega
  rw [ite_eq_right h_ne]
  have h1 : shifted_h_seq m c d = 0 := shifted_h_seq_zero_of_lt m c d h
  have h2 : shifted_h_seq m c (d - 1) = 0 := shifted_h_seq_zero_of_lt m c (d - 1) (by omega)
  rw [h1, h2]
  ring

lemma diff2_H_seq_eq_one_implies_inl_low {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (_h_gt : m2 x > m1 x) (_h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (_h_deg : totalDeg m1 = totalDeg m2)
    (_h1 : diff2 (fun k => (h_seq m1 k : ℤ)) (d + 1) = 1)
    (_h2 : diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = 0)
    (h1_low : d + 1 ≤ m1 0 ∧ d + 1 ≤ m1 1 ∧ d + 1 ≤ m1 2) :
  H_seq (m1:=m1) (m2:=m2) x (d - 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 := by
  have hc : d + 1 < m1 x + 1 := by
    have h : x.val < 3 := x.isLt
    have hx_val : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by omega
    rcases hx_val with hx | hx | hx
    · have h_eq : m1 x = m1 0 := by apply congrArg; exact Fin.ext hx
      rw [h_eq]; omega
    · have h_eq : m1 x = m1 1 := by apply congrArg; exact Fin.ext hx
      rw [h_eq]; omega
    · have h_eq : m1 x = m1 2 := by apply congrArg; exact Fin.ext hx
      rw [h_eq]; omega
  have h_H_eval : H_seq (m1:=m1) (m2:=m2) x (d - 1) = (h_seq m1 (d - 1) : ℤ) := by
    rw [H_seq_eval_add]
    have hc_d_1 : d - 1 < m1 x + 1 := by omega
    have hz := shifted_h_seq_zero_of_lt (reduced_monomial m1 m2 x) (m1 x + 1) (d - 1) hc_d_1
    rw [hz]
    ring
  have h_H_diff : diff (H_seq (m1:=m1) (m2:=m2) x) d = diff (fun k => (h_seq m1 k : ℤ)) d := by
    rw [diff_H_seq_eval_add]
    have hc_d : d < m1 x + 1 := by omega
    have hz := diff_shifted_h_seq_zero_of_lt (reduced_monomial m1 m2 x) (m1 x + 1) d hd hc_d
    rw [hz]
    ring
  have hd_1_bound : d - 1 ≤ m1 0 ∧ d - 1 ≤ m1 1 ∧ d - 1 ≤ m1 2 := by omega
  have h_low1 : (h_seq m1 (d - 1) : ℤ) * 2 = (d : ℤ) * (d + 1 : ℤ) := by
    have h_val := h_seq_pure_lower m1 (d - 1) hd_1_bound
    have h_cast1 : ((d - 1 : ℕ) : ℤ) = d - 1 := by omega
    rw [h_cast1] at h_val
    have h_alg : ((d : ℤ) - 1 + 1) * ((d : ℤ) - 1 + 2) = (d : ℤ) * ((d : ℤ) + 1) := by ring
    rw [h_alg] at h_val
    exact h_val
  have h_diff : diff (fun k => (h_seq m1 k : ℤ)) d = d + 1 := by
    have h_sub : d - 1 + 1 = d := by omega
    have hd_bound2 : d - 1 + 1 ≤ m1 0 ∧ d - 1 + 1 ≤ m1 1 ∧ d - 1 + 1 ≤ m1 2 := by omega
    have h_val := h_seq_pure_lower_diff m1 (d - 1) hd_bound2
    rw [h_sub] at h_val
    have h_cast : ((d - 1 : ℕ) : ℤ) = d - 1 := by omega
    rw [h_cast] at h_val
    have h_alg : (d : ℤ) - 1 + 2 = (d : ℤ) + 1 := by ring
    rw [h_alg] at h_val
    exact h_val
  rw [h_H_eval, h_H_diff, h_diff]
  nlinarith

lemma h_seq_zero_of_gt (m : Monomial 3) (d : ℕ) (hgt : d > m 0 + m 1 + m 2) : h_seq m d = 0 := by
  have h := boxCountZ_zero m (d : ℤ) (Or.inr (by
    simp only [totalDeg_eq_sum_univ, Fin.sum_univ_three]
    omega))
  rw [boxCountZ_nat] at h
  exact_mod_cast h

lemma h_seq_upper_bound_int_all (m : Monomial 3) (d : ℕ) :
  (h_seq m d : ℤ) * 2 ≤ (m 0 + m 1 + m 2 - (d : ℤ) + 1) * (m 0 + m 1 + m 2 - (d : ℤ) + 2) := by
  have h_cases : d ≤ m 0 + m 1 + m 2 ∨ d > m 0 + m 1 + m 2 := by omega
  rcases h_cases with hle | hgt
  · have h1 := h_seq_upper_bound_int m d hle
    have hc1 : (m 0 + m 1 + m 2 - d + 1 : ℤ) = m 0 + m 1 + m 2 - (d : ℤ) + 1 := by omega
    have hc2 : (m 0 + m 1 + m 2 - d + 2 : ℤ) = m 0 + m 1 + m 2 - (d : ℤ) + 2 := by omega
    rw [hc1, hc2] at h1
    exact h1
  · have hz := h_seq_zero_of_gt m d hgt
    have h_cast : (h_seq m d : ℤ) = 0 := by exact_mod_cast hz
    rw [h_cast]
    let X : ℤ := m 0 + m 1 + m 2 - (d : ℤ)
    have h_alg : 0 * 2 ≤ (X + 1) * (X + 2) := by
      have hX : X ≤ -1 := by omega
      have h_cases : X = -1 ∨ X ≤ -2 := by omega
      rcases h_cases with hx1 | hx2
      · rw [hx1]; norm_num
      · have h1 : X + 1 ≤ 0 := by omega
        have h2 : X + 2 ≤ 0 := by omega
        nlinarith
    exact h_alg

lemma m_deg_eq_2 (m1 m2 : Monomial 3) (h_deg : totalDeg m1 = totalDeg m2) :
  m1 0 + m1 1 + m1 2 = m2 0 + m2 1 + m2 2 := by
  simp_all only [totalDeg]
  simp_all[Monomial, Fin.sum_univ_three _, Finsupp.sum_of_support_subset (s:=⊤)]

lemma M_red_eq {m1 m2 : Monomial 3} (x : Fin 3) (h_gt : m2 x > m1 x) (_h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2) :
  (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 = m1 0 + m1 1 + m1 2 - (m1 x + 1) := by
  have h_sum := m_deg_eq_2 m1 m2 h_deg
  have hx_val : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by
    have h : x.val < 3 := x.isLt
    omega
  rcases hx_val with hx | hx | hx
  · have eqx : x = 0 := by apply Fin.ext; exact hx
    rw [eqx] at h_gt _h_le ⊢
    have eq0 : (reduced_monomial m1 m2 0) 0 = m2 0 - m1 0 - 1 := by norm_num[reduced_monomial]
    have eq1 : (reduced_monomial m1 m2 0) 1 = m2 1 := by norm_num [reduced_monomial]
    have eq2 : (reduced_monomial m1 m2 0) 2 = m2 2 := by push_cast[reduced_monomial]at *
                                                         rfl
    rw [eq0, eq1, eq2]
    have hm : m2 0 ≥ m1 0 + 1 := by omega
    have hm2 : m1 0 + m1 1 + m1 2 ≥ m1 0 + 1 := by omega
    omega
  · have eqx : x = 1 := by apply Fin.ext; exact hx
    rw [eqx] at h_gt _h_le ⊢
    have eq0 : (reduced_monomial m1 m2 1) 0 = m2 0 := by norm_num+decide[reduced_monomial]
    have eq1 : (reduced_monomial m1 m2 1) 1 = m2 1 - m1 1 - 1 := by rfl
    have eq2 : (reduced_monomial m1 m2 1) 2 = m2 2 := by norm_num+decide [reduced_monomial]
    rw [eq0, eq1, eq2]
    have hm : m2 1 ≥ m1 1 + 1 := by omega
    have hm2 : m1 0 + m1 1 + m1 2 ≥ m1 1 + 1 := by omega
    omega
  · have eqx : x = 2 := by apply Fin.ext; exact hx
    rw [eqx] at h_gt _h_le ⊢
    have eq0 : (reduced_monomial m1 m2 2) 0 = m2 0 := by norm_num +decide[reduced_monomial]
    have eq1 : (reduced_monomial m1 m2 2) 1 = m2 1 := by simp_all [reduced_monomial]
    have eq2 : (reduced_monomial m1 m2 2) 2 = m2 2 - m1 2 - 1 := by norm_num [reduced_monomial,tsub_tsub]
    rw [eq0, eq1, eq2]
    have hm : m2 2 ≥ m1 2 + 1 := by omega
    have hm2 : m1 0 + m1 1 + m1 2 ≥ m1 2 + 1 := by omega
    omega

lemma inl_high_algebra (U1 h_shift diff_shift h_shift_d : ℤ)
  (hU1_pos : U1 ≥ -1)
  (_h_shift_bound : h_shift * 2 ≤ (U1 + 2) * (U1 + 3))
  (h_shift_d_bound : h_shift_d * 2 ≤ (U1 + 1) * (U1 + 2))
  (h_diff_eq : diff_shift = h_shift_d - h_shift)
  (h_diff_shift_le : diff_shift ≤ 0) :
  (U1 + 2) * (U1 + 3) + 2 * h_shift ≤ 2 * (- (U1 + 2) + diff_shift) ^ 2 := by
  have h_eq : h_shift = h_shift_d - diff_shift := by omega
  rw [h_eq]
  nlinarith

lemma algebra_helper_1 (A B C d : ℕ) (hd : d > 0) (U1 : ℤ) (hU1 : U1 = A + B + C - d) (h1_high : d + 1 ≤ A + B + C + 2) :
  U1 ≥ -1 ∧
  (A + B + C + 1 - (d - 1 : ℕ) : ℤ) = U1 + 2 ∧
  (A + B + C + 2 - (d - 1 : ℕ) : ℤ) = U1 + 3 ∧
  -(A + B + C + 2 - (d : ℤ)) = -(U1 + 2) ∧
  (A + B + C - (d - 1 : ℤ) + 1) = U1 + 2 ∧
  (A + B + C - (d - 1 : ℤ) + 2) = U1 + 3 ∧
  (A + B + C - (d : ℤ) + 1) = U1 + 1 ∧
  (A + B + C - (d : ℤ) + 2) = U1 + 2 := by omega

lemma algebra_helper_2 (A B C M_red c d : ℕ) (hd : d > 0) (hM : M_red = A + B + C - c) (h_ge : d - 1 ≥ c) (hc : A + B + C ≥ c) :
  (M_red - ((d - 1 - c : ℕ) : ℤ) + 1) = (A + B + C - (d - 1 : ℤ) + 1) ∧
  (M_red - ((d - 1 - c : ℕ) : ℤ) + 2) = (A + B + C - (d - 1 : ℤ) + 2) := by omega

lemma algebra_helper_3 (A B C M_red c d : ℕ) (_hd : d > 0) (hM : M_red = A + B + C - c) (h_ge : d ≥ c) (hc : A + B + C ≥ c) :
  (M_red - ((d - c : ℕ) : ℤ) + 1) = (A + B + C - (d : ℤ) + 1) ∧
  (M_red - ((d - c : ℕ) : ℤ) + 2) = (A + B + C - (d : ℤ) + 2) := by omega

lemma ineq_helper (A B C d : ℕ) (h11 : d + 1 ≥ A + B + 2) (h12 : d + 1 ≥ B + C + 2) (h13 : d + 1 ≥ A + C + 2) (h14 : d + 1 ≤ A + B + C + 2) :
  (d - 1 ≥ A + B ∧ d - 1 ≥ B + C ∧ d - 1 ≥ A + C ∧ d - 1 ≤ A + B + C + 1) ∧
  (d ≥ A + B + 1 ∧ d ≥ B + C + 1 ∧ d ≥ A + C + 1 ∧ d ≤ A + B + C + 1) := by omega

lemma diff_shifted_h_seq_eq_ge (m : Monomial 3) (c d : ℕ) (hd : d > 0) (hc : d ≥ c) :
  diff (shifted_h_seq m c) d = diff (fun k => (h_seq m k : ℤ)) (d - c) := by
  have hd_cases : d = c ∨ d > c := by omega
  rcases hd_cases with heq | hgt
  · subst heq
    unfold diff
    have hne : d ≠ 0 := by omega
    rw [ite_eq_right hne]
    have hz : d - d = 0 := by omega
    have h1 : shifted_h_seq m d d = (h_seq m 0 : ℤ) := by
      unfold shifted_h_seq; rw [ite_eq_left (by omega), hz]
    have h2 : shifted_h_seq m d (d - 1) = 0 := by
      unfold shifted_h_seq; rw [ite_eq_right (by omega)]
    rw [h1, h2, hz]
    have h_sub : (h_seq m 0 : ℤ) - 0 = (h_seq m 0 : ℤ) := by ring
    rw [h_sub]
    have hz_diff : (0 : ℕ) = 0 := rfl
    have h_diff_eval : diff (fun k => (h_seq m k : ℤ)) 0 = (h_seq m 0 : ℤ) := by
      unfold diff; rw [ite_eq_left hz_diff]
    exact h_diff_eval.symm
  · unfold diff
    have hne : d ≠ 0 := by omega
    rw [ite_eq_right hne]
    have h1 : shifted_h_seq m c d = (h_seq m (d - c) : ℤ) := by
      unfold shifted_h_seq; rw [ite_eq_left (by omega)]
    have h2 : shifted_h_seq m c (d - 1) = (h_seq m (d - 1 - c) : ℤ) := by
      unfold shifted_h_seq; rw [ite_eq_left (by omega)]
    rw [h1, h2]
    have h_sub : d - 1 - c = d - c - 1 := by omega
    rw [h_sub]
    have hne_dc : d - c ≠ 0 := by omega
    have h_diff_eval : diff (fun k => (h_seq m k : ℤ)) (d - c) = (h_seq m (d - c) : ℤ) - (h_seq m (d - c - 1) : ℤ) := by
      unfold diff; rw [ite_eq_right hne_dc]
    exact h_diff_eval.symm

lemma L_seq_eq_min (A B d : ℕ) : L_seq A B d = min A (d + 1) - (if d + 1 ≥ B then min A (d + 1 - B) else 0) := by
  delta min L_seq
  refine show _ = A⊓_-ite (_) (A⊓ _) 0 from(em _).elim (ite_eq_left ·▸(((congr_arg _)).comp Finset.ext fun and=>.trans ( by aesop) ( Finset.mem_Ico.trans (by valid)).symm).trans (Nat.card_Ico _ _)) (ite_eq_right ·▸? _)
  exact (congr_arg _ (Finset.ext fun and=>.trans (by rw [ Finset.mem_filter, Finset.mem_range]) (List.mem_range.trans (by valid)).symm)).trans ( Finset.card_range _)

lemma L_seq_eq_min_z (A B d : ℕ) : (L_seq A B d : ℤ) = (min A (d + 1) : ℤ) - (if d + 1 ≥ B then (min A (d + 1 - B) : ℤ) else 0) := by
  rw [L_seq_eq_min A B d]
  split_ifs with hB
  · omega
  · omega

lemma diff_h_seq_eq_L_seq (m : Monomial 3) (d : ℕ) (hd : d > 0) :
  diff (fun k => (h_seq m k : ℤ)) d = (L_seq (m 0 + 1) (m 1 + 1) d : ℤ) - (if d ≥ m 2 + 1 then (L_seq (m 0 + 1) (m 1 + 1) (d - (m 2 + 1)) : ℤ) else 0) := by
  have h_eq1 : (fun k => (h_seq m k : ℤ)) d = h_seq m d := rfl
  have h_eq2 : (fun k => (h_seq m k : ℤ)) (d - 1) = h_seq m (d - 1) := rfl
  unfold diff
  have hne : d ≠ 0 := by omega
  rw [ite_eq_right hne]
  have hz1 : (h_seq m d : ℤ) = H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) d := by exact_mod_cast H_eq_H_calc m d
  have hz2 : (h_seq m (d - 1) : ℤ) = H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) (d - 1) := by exact_mod_cast H_eq_H_calc m (d - 1)
  rw [h_eq1, h_eq2, hz1, hz2]
  exact delta_H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) d hd

lemma h_seq_diff_le_zero_of_past_mid (m : Monomial 3) (d : ℕ) (hd : d * 2 ≥ m 0 + m 1 + m 2 + 1) :
  diff (fun k => (h_seq m k : ℤ)) d ≤ 0 := by
  have hd_pos : d > 0 := by omega
  rw [diff_h_seq_eq_L_seq m d hd_pos]
  rw [L_seq_eq_min_z]
  split_ifs
  all_goals
    try rw [L_seq_eq_min_z]
    try split_ifs
    all_goals
      try split_ifs
      all_goals omega

lemma inl_high_shift_diff {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
    (h1_high : d + 1 ≥ m1 0 + m1 1 + 2 ∧ d + 1 ≥ m1 1 + m1 2 + 2 ∧ d + 1 ≥ m1 0 + m1 2 + 2 ∧ d + 1 ≤ m1 0 + m1 1 + m1 2 + 2) :
    diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d ≤ 0 := by
  have hc : d < m1 x + 1 ∨ d ≥ m1 x + 1 := by omega
  rcases hc with h_lt | h_ge
  · have hz := diff_shifted_h_seq_zero_of_lt (reduced_monomial m1 m2 x) (m1 x + 1) d hd h_lt
    rw [hz]
  · have h_eq := diff_shifted_h_seq_eq_ge (reduced_monomial m1 m2 x) (m1 x + 1) d hd h_ge
    rw [h_eq]
    apply h_seq_diff_le_zero_of_past_mid
    have h_red_deg : (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 = m1 0 + m1 1 + m1 2 - (m1 x + 1) := M_red_eq x h_gt h_le h_deg
    have h_ineqs := ineq_helper (m1 0) (m1 1) (m1 2) d h1_high.1 h1_high.2.1 h1_high.2.2.1 h1_high.2.2.2
    have hd1 : d ≥ m1 0 + m1 1 + 1 := h_ineqs.2.1
    have hd2 : d ≥ m1 1 + m1 2 + 1 := h_ineqs.2.2.1
    have hd3 : d ≥ m1 0 + m1 2 + 1 := h_ineqs.2.2.2.1
    have h_sum := m_deg_eq_2 m1 m2 h_deg
    have hm2_x_le : m2 x ≤ m2 0 + m2 1 + m2 2 := by
      have h : x.val < 3 := x.isLt
      rcases (by omega : x.val = 0 ∨ x.val = 1 ∨ x.val = 2) with hx0 | hx1 | hx2
      · have hx_eq : x = 0 := Fin.ext hx0; rw [hx_eq]; omega
      · have hx_eq : x = 1 := Fin.ext hx1; rw [hx_eq]; omega
      · have hx_eq : x = 2 := Fin.ext hx2; rw [hx_eq]; omega
    have hm1_x_le : m1 x + 1 ≤ m1 0 + m1 1 + m1 2 := by omega
    have h_cast1 : ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 : ℤ) = (m1 0 + m1 1 + m1 2 : ℤ) - (m1 x + 1 : ℤ) := by
      have hc : ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 : ℤ) = ((m1 0 + m1 1 + m1 2 - (m1 x + 1) : ℕ) : ℤ) := by exact_mod_cast h_red_deg
      rw [hc]
      exact Nat.cast_sub hm1_x_le
    have hc_sub : ((d - (m1 x + 1) : ℕ) : ℤ) = (d : ℤ) - (m1 x + 1 : ℤ) := by omega
    have hm1_x_le_m10 : m1 x ≤ m1 0 + m1 1 + m1 2 := by omega
    have h_d_bound : (d : ℤ) * 2 ≥ (m1 x : ℤ) + (m1 0 + m1 1 + m1 2 : ℤ) + 2 := by
      have hd1_z : (d : ℤ) ≥ (m1 0 : ℤ) + (m1 1 : ℤ) + 1 := by exact_mod_cast hd1
      have hd2_z : (d : ℤ) ≥ (m1 1 : ℤ) + (m1 2 : ℤ) + 1 := by exact_mod_cast hd2
      have hd3_z : (d : ℤ) ≥ (m1 0 : ℤ) + (m1 2 : ℤ) + 1 := by exact_mod_cast hd3
      have h : x.val < 3 := x.isLt
      rcases (by omega : x.val = 0 ∨ x.val = 1 ∨ x.val = 2) with hx0 | hx1 | hx2
      · have hx_eq : x = 0 := Fin.ext hx0; rw [hx_eq]; linarith
      · have hx_eq : x = 1 := Fin.ext hx1; rw [hx_eq]; linarith
      · have hx_eq : x = 2 := Fin.ext hx2; rw [hx_eq]; linarith
    have h_final : ((d - (m1 x + 1) : ℕ) : ℤ) * 2 ≥ ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 : ℤ) + 1 := by linarith
    exact_mod_cast h_final

lemma m1_x_le_M1 {m1 m2 : Monomial 3} (x : Fin 3) (h_gt : m2 x > m1 x) (h_deg : totalDeg m1 = totalDeg m2) :
  m1 x + 1 ≤ m1 0 + m1 1 + m1 2 := by
  have h_sum := m_deg_eq_2 m1 m2 h_deg
  have hx_val : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by have h := x.isLt; omega
  rcases hx_val with h0 | h1 | h2
  · have eqx : x = 0 := Fin.ext h0; subst eqx; omega
  · have eqx : x = 1 := Fin.ext h1; subst eqx; omega
  · have eqx : x = 2 := Fin.ext h2; subst eqx; omega

lemma inl_high_H_eval_bounds_shift_d {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
    (U1 : ℤ) (hU1 : U1 = m1 0 + m1 1 + m1 2 - d) :
    shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) d * 2 ≤ (U1 + 1) * (U1 + 2) := by
  have hm1x := m1_x_le_M1 x h_gt h_deg
  have h_red_deg : (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 = m1 0 + m1 1 + m1 2 - (m1 x + 1) := M_red_eq x h_gt h_le h_deg
  have h_cases : d < m1 x + 1 ∨ d ≥ m1 x + 1 := by omega
  rcases h_cases with h_lt | h_ge
  · have hz : shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) d = 0 := shifted_h_seq_zero_of_lt _ _ _ h_lt
    rw [hz]
    have h0 : (0:ℤ) * 2 = 0 := rfl
    rw [h0]
    have h_pos1 : U1 + 1 ≥ 0 := by omega
    have h_pos2 : U1 + 2 ≥ 0 := by omega
    exact mul_nonneg h_pos1 h_pos2
  · have hz : shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) d = (h_seq (reduced_monomial m1 m2 x) (d - (m1 x + 1)) : ℤ) := by
      unfold shifted_h_seq
      rw [ite_eq_left h_ge]
    rw [hz]
    have h_bound := h_seq_upper_bound_int_all (reduced_monomial m1 m2 x) (d - (m1 x + 1))
    have h_alg := algebra_helper_3 (m1 0) (m1 1) (m1 2) ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2) (m1 x + 1) d hd h_red_deg h_ge hm1x
    have hc1 : ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 - ((d - (m1 x + 1) : ℕ) : ℤ) + 1) = (m1 0 + m1 1 + m1 2 - (d : ℤ) + 1) := h_alg.1
    have hc2 : ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 - ((d - (m1 x + 1) : ℕ) : ℤ) + 2) = (m1 0 + m1 1 + m1 2 - (d : ℤ) + 2) := h_alg.2
    rw [hc1, hc2] at h_bound
    have h_sub4 : (m1 0 + m1 1 + m1 2 - (d : ℤ) + 1) = U1 + 1 := by omega
    have h_sub5 : (m1 0 + m1 1 + m1 2 - (d : ℤ) + 2) = U1 + 2 := by omega
    rw [h_sub4, h_sub5] at h_bound
    exact h_bound

lemma inl_high_H_eval_bounds_shift_d_minus_1 {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
    (U1 : ℤ) (hU1 : U1 = m1 0 + m1 1 + m1 2 - d) :
    shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d - 1) * 2 ≤ (U1 + 2) * (U1 + 3) := by
  have hm1x := m1_x_le_M1 x h_gt h_deg
  have h_red_deg : (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 = m1 0 + m1 1 + m1 2 - (m1 x + 1) := M_red_eq x h_gt h_le h_deg
  have h_cases : d - 1 < m1 x + 1 ∨ d - 1 ≥ m1 x + 1 := by exact lt_or_ge _ _
  rcases h_cases with h_lt | h_ge
  · have hz : shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d - 1) = 0 := shifted_h_seq_zero_of_lt _ _ _ h_lt
    rw [hz]
    have h0 : (0:ℤ) * 2 = 0 := rfl
    rw [h0]
    have h_pos1 : U1 + 2 ≥ 0 := by omega
    have h_pos2 : U1 + 3 ≥ 0 := by omega
    exact mul_nonneg h_pos1 h_pos2
  · have hz : shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d - 1) = (h_seq (reduced_monomial m1 m2 x) (d - 1 - (m1 x + 1)) : ℤ) := by
      unfold shifted_h_seq
      rw [ite_eq_left h_ge]
    rw [hz]
    have h_bound := h_seq_upper_bound_int_all (reduced_monomial m1 m2 x) (d - 1 - (m1 x + 1))
    have h_alg := algebra_helper_2 (m1 0) (m1 1) (m1 2) ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2) (m1 x + 1) d hd h_red_deg h_ge hm1x
    have hc1 : ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 - ((d - 1 - (m1 x + 1) : ℕ) : ℤ) + 1) = (m1 0 + m1 1 + m1 2 - (d - 1 : ℤ) + 1) := h_alg.1
    have hc2 : ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 - ((d - 1 - (m1 x + 1) : ℕ) : ℤ) + 2) = (m1 0 + m1 1 + m1 2 - (d - 1 : ℤ) + 2) := h_alg.2
    rw [hc1, hc2] at h_bound
    have h_sub4 : (m1 0 + m1 1 + m1 2 - (d - 1 : ℤ) + 1) = U1 + 2 := by omega
    have h_sub5 : (m1 0 + m1 1 + m1 2 - (d - 1 : ℤ) + 2) = U1 + 3 := by omega
    rw [h_sub4, h_sub5] at h_bound
    exact h_bound

lemma inl_high_H_eval_bounds {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
    (h1_high : d + 1 ≥ m1 0 + m1 1 + 2 ∧ d + 1 ≥ m1 1 + m1 2 + 2 ∧ d + 1 ≥ m1 0 + m1 2 + 2 ∧ d + 1 ≤ m1 0 + m1 1 + m1 2 + 2) :
  H_seq (m1:=m1) (m2:=m2) x (d - 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 := by
  have h_ineqs := ineq_helper (m1 0) (m1 1) (m1 2) d h1_high.1 h1_high.2.1 h1_high.2.2.1 h1_high.2.2.2
  have hd_1_upper : d - 1 ≥ m1 0 + m1 1 ∧ d - 1 ≥ m1 1 + m1 2 ∧ d - 1 ≥ m1 0 + m1 2 ∧ d - 1 ≤ m1 0 + m1 1 + m1 2 + 1 := h_ineqs.1
  have heval1 : (h_seq m1 (d - 1) : ℤ) * 2 = (m1 0 + m1 1 + m1 2 + 1 - (d - 1 : ℕ) : ℤ) * (m1 0 + m1 1 + m1 2 + 2 - (d - 1 : ℕ) : ℤ) := h_seq_pure_upper m1 (d - 1) hd_1_upper
  have hd_upper : d ≥ m1 0 + m1 1 + 1 ∧ d ≥ m1 1 + m1 2 + 1 ∧ d ≥ m1 0 + m1 2 + 1 ∧ d ≤ m1 0 + m1 1 + m1 2 + 1 := h_ineqs.2
  have hdiff1 : diff (fun k => (h_seq m1 k : ℤ)) d = - (m1 0 + m1 1 + m1 2 + 2 - d : ℤ) := h_seq_pure_upper_diff m1 d hd_upper
  have h_shift_diff : diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d ≤ 0 := inl_high_shift_diff x d hd h_gt h_le h_deg h1_high
  have h_H_eval : H_seq (m1:=m1) (m2:=m2) x (d - 1) = (h_seq m1 (d - 1) : ℤ) + shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d - 1) := by
    rw [H_seq_eval_add]
  have h_H_diff : diff (H_seq (m1:=m1) (m2:=m2) x) d = diff (fun k => (h_seq m1 k : ℤ)) d + diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d := by
    rw [diff_H_seq_eval_add]
  let U1 : ℤ := m1 0 + m1 1 + m1 2 - d
  have h_alg_vars := algebra_helper_1 (m1 0) (m1 1) (m1 2) d hd U1 rfl h1_high.2.2.2
  have hU1_pos : U1 ≥ -1 := h_alg_vars.1
  have h_sub1 : (m1 0 + m1 1 + m1 2 + 1 - (d - 1 : ℕ) : ℤ) = U1 + 2 := h_alg_vars.2.1
  have h_sub2 : (m1 0 + m1 1 + m1 2 + 2 - (d - 1 : ℕ) : ℤ) = U1 + 3 := h_alg_vars.2.2.1
  have h_sub3 : - (m1 0 + m1 1 + m1 2 + 2 - d : ℤ) = - (U1 + 2) := h_alg_vars.2.2.2.1
  rw [h_sub1, h_sub2] at heval1
  rw [h_sub3] at hdiff1
  have h_shift_eval : shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d - 1) * 2 ≤ (U1 + 2) * (U1 + 3) := inl_high_H_eval_bounds_shift_d_minus_1 x d hd h_gt h_le h_deg U1 rfl
  have h_shift_d_bound : shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) d * 2 ≤ (U1 + 1) * (U1 + 2) := inl_high_H_eval_bounds_shift_d x d hd h_gt h_le h_deg U1 rfl
  have h_LHS : 2 * H_seq (m1:=m1) (m2:=m2) x (d - 1) = 2 * (h_seq m1 (d - 1) : ℤ) + 2 * shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d - 1) := by
    rw [h_H_eval]; ring
  have h_heval1_mul2 : 2 * (h_seq m1 (d - 1) : ℤ) = (U1 + 2) * (U1 + 3) := by
    calc
      2 * (h_seq m1 (d - 1) : ℤ) = (h_seq m1 (d - 1) : ℤ) * 2 := by ring
      _ = (U1 + 2) * (U1 + 3) := heval1
  have h_shift_bound_sub : shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d - 1) * 2 ≤ (U1 + 2) * (U1 + 3) := h_shift_eval
  have h_diff_eq_val : diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d = shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) d - shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d - 1) := by
    unfold diff
    have hne : d ≠ 0 := by omega
    rw [ite_eq_right hne]
  have h_alg := inl_high_algebra U1 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d - 1)) (diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d) (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) d) hU1_pos h_shift_bound_sub h_shift_d_bound h_diff_eq_val h_shift_diff
  have h_RHS : (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 = (-(U1 + 2) + diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d)^2 := by
    rw [h_H_diff, hdiff1]
  have h_final : 2 * H_seq (m1:=m1) (m2:=m2) x (d - 1) ≤ 2 * (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 := by
    calc
      2 * H_seq (m1:=m1) (m2:=m2) x (d - 1) = 2 * (h_seq m1 (d - 1) : ℤ) + 2 * shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d - 1) := h_LHS
      _ = (U1 + 2) * (U1 + 3) + 2 * shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d - 1) := by rw [h_heval1_mul2]
      _ ≤ 2 * (- (U1 + 2) + diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d) ^ 2 := h_alg
      _ = 2 * (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 := by rw [← h_RHS]
  clear * - h_final
  linarith

lemma diff2_H_seq_eq_one_implies_inl_high {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
    (_h1 : diff2 (fun k => (h_seq m1 k : ℤ)) (d + 1) = 1)
    (_h2 : diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = 0)
    (h1_high : d + 1 ≥ m1 0 + m1 1 + 2 ∧ d + 1 ≥ m1 1 + m1 2 + 2 ∧ d + 1 ≥ m1 0 + m1 2 + 2 ∧ d + 1 ≤ m1 0 + m1 1 + m1 2 + 2) :
  H_seq (m1:=m1) (m2:=m2) x (d - 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 := by
  exact inl_high_H_eval_bounds x d hd h_gt h_le h_deg h1_high

lemma diff2_H_seq_eq_one_implies_inl {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
    (h1 : diff2 (fun k => (h_seq m1 k : ℤ)) (d + 1) = 1)
    (h2 : diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = 0) :
  H_seq (m1:=m1) (m2:=m2) x (d - 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 := by
  have h1_cases := diff2_h_seq_eq_one_implies m1 (d + 1) h1
  rcases h1_cases with h1_low | h1_high
  · exact diff2_H_seq_eq_one_implies_inl_low x d hd h_gt h_le h_deg h1 h2 h1_low
  · exact diff2_H_seq_eq_one_implies_inl_high x d hd h_gt h_le h_deg h1 h2 h1_high

lemma shifted_h_seq_eval_lower (m : Monomial 3) (c d : ℕ) (hc : d ≥ c) (h_low : d - c ≤ m 0 ∧ d - c ≤ m 1 ∧ d - c ≤ m 2) :
  shifted_h_seq m c d * 2 = (d - c + 1 : ℤ) * (d - c + 2 : ℤ) := by
  unfold shifted_h_seq
  rw [ite_eq_left hc]
  exact_mod_cast h_seq_pure_lower m (d - c) h_low

lemma diff_shifted_h_seq_eval_lower (m : Monomial 3) (c d : ℕ) (hd : d > 0) (hc : d ≥ c) (h_low : d - c ≤ m 0 ∧ d - c ≤ m 1 ∧ d - c ≤ m 2) :
  diff (shifted_h_seq m c) d = (d - c + 1 : ℤ) := by
  have hd_cases : d = c ∨ d > c := by omega
  rcases hd_cases with heq | hgt
  · subst heq
    unfold diff shifted_h_seq
    have hne : d ≠ 0 := by omega
    rw [ite_eq_right hne]
    have hc_ge : d ≥ d := by omega
    have hc_lt : ¬(d - 1 ≥ d) := by omega
    rw [ite_eq_left hc_ge, ite_eq_right hc_lt]
    have hz : d - d = 0 := by omega
    rw [hz]
    have h_seq0 : h_seq m 0 = 1 := by
      have h1 : h_seq m 0 = H_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) 0 := H_eq_H_calc m 0
      rw [h1, H_calc_zero]
      have hm2 : m 2 + 1 > 0 := by omega
      rw [ite_eq_left hm2]
      have hl := L_seq_zero (m 0 + 1) (m 1 + 1)
      have h_cond : 0 < m 0 + 1 ∧ 0 < m 1 + 1 := by omega
      rw [ite_eq_left h_cond] at hl
      exact_mod_cast hl
    have h_cast : (h_seq m 0 : ℤ) = 1 := by exact_mod_cast h_seq0
    rw [h_cast]
    ring
  · unfold diff shifted_h_seq
    have hne : d ≠ 0 := by omega
    rw [ite_eq_right hne]
    have hc1 : d - 1 ≥ c := by omega
    rw [ite_eq_left hc, ite_eq_left hc1]
    have hd1 : d - 1 - c = d - c - 1 := by omega
    rw [hd1]
    have hd_bound : d - c - 1 + 1 ≤ m 0 ∧ d - c - 1 + 1 ≤ m 1 ∧ d - c - 1 + 1 ≤ m 2 := by omega
    have h_diff_eq := h_seq_pure_lower_diff m (d - c - 1) hd_bound
    have h_sub : d - c - 1 + 1 = d - c := by omega
    rw [h_sub] at h_diff_eq
    unfold diff at h_diff_eq
    have h_d_c_ne : d - c ≠ 0 := by omega
    rw [ite_eq_right h_d_c_ne] at h_diff_eq
    have hd_c_1 : d - c - 1 = d - c - 1 := by omega
    have h_eval1 : (fun k => (h_seq m k : ℤ)) (d - c) = (h_seq m (d - c) : ℤ) := rfl
    have h_eval2 : (fun k => (h_seq m k : ℤ)) (d - c - 1) = (h_seq m (d - c - 1) : ℤ) := rfl
    rw [h_eval1, h_eval2] at h_diff_eq
    have h_cast : ((d - c - 1 : ℕ) : ℤ) = d - c - 1 := by omega
    rw [h_cast] at h_diff_eq
    have h_eq : (d - c - 1 : ℤ) + 2 = d - c + 1 := by omega
    linarith

lemma h_le_diff_mul_of_diff2_nonneg (h : ℕ → ℤ) (d : ℕ) (h_diff2 : ∀ k, 0 < k → k ≤ d → diff2 h k ≥ 0) :
  h d ≤ diff h d * (d + 1 : ℤ) := by
  induction d with
  | zero =>
    have hz : diff h 0 = h 0 := by unfold diff; rw [ite_eq_left rfl]
    rw [← hz]
    omega
  | succ d ih =>
    have h_diff_eq : h (d + 1) = h d + diff h (d + 1) := diff_eq h (d + 1) (by omega)
    have h_diff2_nonneg := h_diff2 (d + 1) (by omega) (by omega)
    have h_diff_mono : diff h d ≤ diff h (d + 1) := by
      have hd : diff2 h (d + 1) = diff h (d + 1) - diff h d := by
        unfold diff2
        have h_ne : d + 1 ≠ 0 := by omega
        rw [ite_eq_right h_ne]
        have h_sub : d + 1 - 1 = d := by omega
        rw [h_sub]
      omega
    have h_ih_bound : h d ≤ diff h d * (d + 1 : ℤ) := by
      apply ih
      intro k hk0 hkd
      exact h_diff2 k hk0 (by omega)
    have hd_cast : ((d + 1 : ℕ) : ℤ) = (d : ℤ) + 1 := by omega
    have hd_pos : (d : ℤ) + 1 ≥ 0 := by omega
    have h_step : h d + diff h (d + 1) ≤ diff h (d + 1) * (d + 1 : ℤ) + diff h (d + 1) := by nlinarith
    have h_goal : diff h (d + 1) * (d + 1 : ℤ) + diff h (d + 1) = diff h (d + 1) * ((d + 1 : ℕ) + 1 : ℤ) := by
      have hd2 : ((d + 1 : ℕ) + 1 : ℤ) = (d : ℤ) + 2 := by omega
      rw [hd2]
      ring
    linarith

lemma h_seq_le_diff_mul_of_low (m : Monomial 3) (d : ℕ)
    (h_low : d < (m 0 + 1) + (m 1 + 1) ∧ d < (m 1 + 1) + (m 2 + 1) ∧ d < (m 0 + 1) + (m 2 + 1)) (hz : Z_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) d = 0) :
  (h_seq m d : ℤ) ≤ diff (fun k => (h_seq m k : ℤ)) d * (d + 1 : ℤ) := by
  apply h_le_diff_mul_of_diff2_nonneg
  intro k hk0 hkd
  have hz_calc := diff2_h_seq_eq_Z_calc m k hk0
  rw [hz_calc]
  unfold Z_calc at hz ⊢
  omega

lemma h_seq_diff_ge_min (m : Monomial 3) (d : ℕ) (x : Fin 3) (hd_c : d ≥ m x + 1)
    (h_low : d < (m 0 + 1) + (m 1 + 1) ∧ d < (m 1 + 1) + (m 2 + 1) ∧ d < (m 0 + 1) + (m 2 + 1)) (hz : Z_calc (m 0 + 1) (m 1 + 1) (m 2 + 1) d = 0) :
  diff (fun k => (h_seq m k : ℤ)) d ≥ m x + 1 := by
  have h_x_val : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by
    have h : x.val < 3 := x.isLt
    omega
  have hd_pos : d > 0 := by omega
  rw [diff_h_seq_eq_L_seq m d hd_pos]
  unfold Z_calc at hz
  rcases h_x_val with hx | hx | hx
  · have hx0 : x = 0 := Fin.ext hx; subst hx0
    rw [L_seq_eq_min_z]
    split_ifs
    all_goals
      try rw [L_seq_eq_min_z]
      try split_ifs
      all_goals
        try split_ifs
        all_goals omega
  · have hx1 : x = 1 := Fin.ext hx; subst hx1
    rw [L_seq_eq_min_z]
    split_ifs
    all_goals
      try rw [L_seq_eq_min_z]
      try split_ifs
      all_goals
        try split_ifs
        all_goals omega
  · have hx2 : x = 2 := Fin.ext hx; subst hx2
    rw [L_seq_eq_min_z]
    split_ifs
    all_goals
      try rw [L_seq_eq_min_z]
      try split_ifs
      all_goals
        try split_ifs
        all_goals omega

lemma inr_low_hd_bound (m1 m2 : Monomial 3) (x : Fin 3) (d : ℕ)
    (_h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (_h_deg : totalDeg m1 = totalDeg m2)
    (hz : Z_calc (m1 0 + 1) (m1 1 + 1) (m1 2 + 1) (d + 1) = 0) (hd_c : d + 1 ≥ m1 x + 1)
    (h2_low : d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 0 ∧ d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 1 ∧ d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 2) :
  d + 1 < (m1 0 + 1) + (m1 1 + 1) ∧ d + 1 < (m1 1 + 1) + (m1 2 + 1) ∧ d + 1 < (m1 0 + 1) + (m1 2 + 1) := by
  simp_all-contextual[reduced_monomial,totalDeg,←add_assoc, add_right_comm,Z_calc]
  grind

lemma inr_low_H_eval_bounds {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
    (hz : Z_calc (m1 0 + 1) (m1 1 + 1) (m1 2 + 1) (d + 1) = 0) (hd_c : d + 1 ≥ m1 x + 1)
    (h2_low : d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 0 ∧ d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 1 ∧ d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 2) :
  (h_seq m1 (d + 1) : ℤ) ≤ (diff (fun k => (h_seq m1 k : ℤ)) (d + 1)) * (d + 2 : ℤ) ∧
  diff (fun k => (h_seq m1 k : ℤ)) (d + 1) ≥ m1 x + 1 ∧
  shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) * 2 = (d + 1 - (m1 x + 1) + 1 : ℤ) * (d + 1 - (m1 x + 1) + 2 : ℤ) ∧
  diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = (d + 1 - (m1 x + 1) + 1 : ℤ) := by
  have h_low := inr_low_hd_bound m1 m2 x d h_gt h_le h_deg hz hd_c h2_low
  have h1 : (h_seq m1 (d + 1) : ℤ) ≤ diff (fun k => (h_seq m1 k : ℤ)) (d + 1) * (d + 2 : ℤ) := by
    have h_le_diff := h_seq_le_diff_mul_of_low m1 (d + 1) h_low hz
    have hc : ((d + 1 : ℕ) : ℤ) + 1 = d + 2 := by omega
    rw [hc] at h_le_diff
    exact h_le_diff
  have h2_eval : shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) * 2 = (d + 1 - (m1 x + 1) + 1 : ℤ) * (d + 1 - (m1 x + 1) + 2 : ℤ) := by
    exact shifted_h_seq_eval_lower (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) hd_c h2_low
  have h2_diff : diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = (d + 1 - (m1 x + 1) + 1 : ℤ) := by
    have hd_pos : d + 1 > 0 := by omega
    exact diff_shifted_h_seq_eval_lower (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) hd_pos hd_c h2_low
  have h_diff_ge : diff (fun k => (h_seq m1 k : ℤ)) (d + 1) ≥ m1 x + 1 := by
    exact h_seq_diff_ge_min m1 (d + 1) x hd_c h_low hz
  exact ⟨h1, h_diff_ge, h2_eval, h2_diff⟩

lemma inr_low_master_ineq (S1 X c d_val : ℤ) (hS1 : S1 ≥ c) (hX : X ≥ 1) (hc : c ≥ 1) (hd : d_val + 2 = X + c) :
  2 * S1 * (d_val + 2) + X * (X + 1) ≤ 2 * (S1 + X) ^ 2 := by
  have hd_sub : d_val + 2 = X + c := hd
  rw [hd_sub]
  nlinarith

lemma inr_low_reduction_goal_helper {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
    (h1 : diff2 (fun k => (h_seq m1 k : ℤ)) (d + 1) = 0)
    (h2 : diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = 1)
    (h2_low : d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 0 ∧ d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 1 ∧ d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 2) :
    H_seq (m1:=m1) (m2:=m2) x (d + 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1))^2 := by
  have hc : d + 1 ≥ m1 x + 1 := diff2_shifted_h_seq_eq_one_implies _ _ _ h2
  have hz := diff2_h_seq_eq_Z_calc m1 (d + 1) (by omega)
  rw [h1] at hz
  have h_bounds := inr_low_H_eval_bounds x d hd h_gt h_le h_deg hz.symm hc h2_low
  rcases h_bounds with ⟨h_h1, h_diff1, h_shift, h_diff_shift⟩
  rw [H_seq_eval_add, diff_H_seq_eval_add]
  let S1 := diff (fun k => (h_seq m1 k : ℤ)) (d + 1)
  let X := (d + 1 - (m1 x + 1) + 1 : ℤ)
  let c := (m1 x + 1 : ℤ)
  let d_val := (d : ℤ)
  have h_X_diff : diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = X := by omega
  have h_X_h : shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) * 2 = X * (X + 1) := by
    have hd_sub1 : (d + 1 - (m1 x + 1) + 1 : ℤ) = X := by omega
    have hd_sub2 : (d + 1 - (m1 x + 1) + 2 : ℤ) = X + 1 := by omega
    rw [h_shift, hd_sub1, hd_sub2]
  have h_master := inr_low_master_ineq S1 X c d_val h_diff1 (by omega) (by omega) (by omega)
  have h_LHS : (H_seq (m1:=m1) (m2:=m2) x (d + 1)) * 2 = (h_seq m1 (d + 1) : ℤ) * 2 + shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) * 2 := by
    rw [H_seq_eval_add]
    ring
  have h_mid : (H_seq (m1:=m1) (m2:=m2) x (d + 1)) * 2 ≤ 2 * S1 * (d_val + 2) + X * (X + 1) := by
    have h_sub1 : (h_seq m1 (d + 1) : ℤ) * 2 ≤ 2 * S1 * (d_val + 2) := by
      have hc : diff (fun k => ↑(h_seq m1 k)) (d + 1) = S1 := rfl
      have hd_c : (d + 2 : ℤ) = d_val + 2 := rfl
      rw [hc, hd_c] at h_h1
      linarith
    linarith
  have h_RHS : 2 * (diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1))^2 = 2 * (S1 + X)^2 := by
    have hd_sub : diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1) = S1 + X := by
      rw [diff_H_seq_eval_add, h_X_diff]
    rw [hd_sub]
  have h_final : (H_seq (m1:=m1) (m2:=m2) x (d + 1)) * 2 ≤ 2 * (diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1))^2 := by
    calc
      (H_seq (m1:=m1) (m2:=m2) x (d + 1)) * 2 ≤ 2 * S1 * (d_val + 2) + X * (X + 1) := h_mid
      _ ≤ 2 * (S1 + X)^2 := h_master
      _ = 2 * (diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1))^2 := by rw [← h_RHS]
  have h_final_real : H_seq (m1:=m1) (m2:=m2) x (d + 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1))^2 := by linarith [h_final]
  have h_eq1 : (h_seq m1 (d + 1) : ℤ) + shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) = H_seq (m1:=m1) (m2:=m2) x (d + 1) := by rw [H_seq_eval_add]
  have h_eq2 : diff (fun k => ↑(h_seq m1 k)) (d + 1) + diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1) := by rw [diff_H_seq_eval_add]
  rw [h_eq1, h_eq2]
  exact h_final_real

lemma diff2_H_seq_eq_one_implies_inr_low {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
    (h1 : diff2 (fun k => (h_seq m1 k : ℤ)) (d + 1) = 0)
    (h2 : diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = 1)
    (h2_low : d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 0 ∧ d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 1 ∧ d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 2) :
  H_seq (m1:=m1) (m2:=m2) x (d - 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 := by
  apply H_seq_diff2_reduction x d hd
  · rw [diff2_H_seq_eq_add, h1, h2]; ring
  · exact inr_low_reduction_goal_helper x d hd h_gt h_le h_deg h1 h2 h2_low

lemma h_seq_pure_upper_ext (m : Monomial 3) (d : ℕ) (h : d ≥ m 0 + m 1 ∧ d ≥ m 1 + m 2 ∧ d ≥ m 0 + m 2 ∧ d ≤ m 0 + m 1 + m 2 + 2) :
  (h_seq m d : ℤ) * 2 = (m 0 + m 1 + m 2 + 1 - (d : ℤ)) * (m 0 + m 1 + m 2 + 2 - (d : ℤ)) := by
  have h_cases : d ≤ m 0 + m 1 + m 2 + 1 ∨ d = m 0 + m 1 + m 2 + 2 := by omega
  rcases h_cases with hd | hd
  · exact h_seq_pure_upper m d (by omega)
  · have hd_z : (d : ℤ) = (m 0 : ℤ) + (m 1 : ℤ) + (m 2 : ℤ) + 2 := by omega
    rw [hd_z]
    have hz : h_seq m (m 0 + m 1 + m 2 + 2) = 0 := h_seq_zero_of_gt m _ (by omega)
    have hz_cast : (h_seq m d : ℤ) = 0 := by
      rw [hd]
      exact_mod_cast hz
    rw [hz_cast]
    ring

lemma h_seq_pure_upper_diff_ext (m : Monomial 3) (d : ℕ) (h : d ≥ m 0 + m 1 + 1 ∧ d ≥ m 1 + m 2 + 1 ∧ d ≥ m 0 + m 2 + 1 ∧ d ≤ m 0 + m 1 + m 2 + 2) :
  diff (fun k => (h_seq m k : ℤ)) d = - (m 0 + m 1 + m 2 + 2 - (d : ℤ)) := by
  have h_cases : d ≤ m 0 + m 1 + m 2 + 1 ∨ d = m 0 + m 1 + m 2 + 2 := by omega
  rcases h_cases with hd | hd
  · exact h_seq_pure_upper_diff m d (by omega)
  · have hd_z : (d : ℤ) = (m 0 : ℤ) + (m 1 : ℤ) + (m 2 : ℤ) + 2 := by omega
    rw [hd_z]
    unfold diff
    have hne : d ≠ 0 := by omega
    rw [ite_eq_right hne]
    have hz1 : h_seq m (m 0 + m 1 + m 2 + 2) = 0 := h_seq_zero_of_gt m _ (by omega)
    have hz2 : h_seq m (m 0 + m 1 + m 2 + 2 - 1) = 0 := h_seq_zero_of_gt m _ (by omega)
    have hd_sub : d - 1 = m 0 + m 1 + m 2 + 2 - 1 := by omega
    have hz1_cast : (h_seq m d : ℤ) = 0 := by rw [hd]; exact_mod_cast hz1
    have hz2_cast : (h_seq m (d - 1) : ℤ) = 0 := by rw [hd_sub]; exact_mod_cast hz2
    have h_eval1 : (fun k => (h_seq m k : ℤ)) d = 0 := hz1_cast
    have h_eval2 : (fun k => (h_seq m k : ℤ)) (d - 1) = 0 := hz2_cast
    rw [h_eval1, h_eval2]
    ring

lemma inr_high_H_eval_bounds {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
    (_hz : Z_calc (m1 0 + 1) (m1 1 + 1) (m1 2 + 1) (d + 1) = 0) (hd_c : d + 1 ≥ m1 x + 1)
    (h2_high : d + 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + 2 ∧ d + 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 2 ∧ d + 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 2 + 2 ∧ d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 2) :
  (h_seq m1 (d + 1) : ℤ) * 2 ≤ (m1 0 + m1 1 + m1 2 + 1 - (d + 1 : ℤ)) * (m1 0 + m1 1 + m1 2 + 2 - (d + 1 : ℤ)) ∧
  diff (fun k => (h_seq m1 k : ℤ)) (d + 1) ≤ 0 ∧
  shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) * 2 = (m1 0 + m1 1 + m1 2 + 1 - (d + 1 : ℤ)) * (m1 0 + m1 1 + m1 2 + 2 - (d + 1 : ℤ)) ∧
  diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = (d + 1 : ℤ) - (m1 0 + m1 1 + m1 2 + 2) ∧
  (d + 1 : ℤ) ≤ m1 0 + m1 1 + m1 2 + 2 := by
  have hm1x := m1_x_le_M1 x h_gt h_deg
  have h_red_deg : (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 = m1 0 + m1 1 + m1 2 - (m1 x + 1) := M_red_eq x h_gt h_le h_deg
  have h_red_deg_z : ((reduced_monomial m1 m2 x) 0 : ℤ) + ((reduced_monomial m1 m2 x) 1 : ℤ) + ((reduced_monomial m1 m2 x) 2 : ℤ) = (m1 0 : ℤ) + (m1 1 : ℤ) + (m1 2 : ℤ) - (m1 x + 1 : ℤ) := by
    have h_cast : (((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 : ℕ) : ℤ) = ((m1 0 + m1 1 + m1 2 - (m1 x + 1) : ℕ) : ℤ) := congrArg Nat.cast h_red_deg
    push_cast at h_cast
    have h_sub : ((m1 0 + m1 1 + m1 2 - (m1 x + 1) : ℕ) : ℤ) = (m1 0 : ℤ) + (m1 1 : ℤ) + (m1 2 : ℤ) - (m1 x + 1 : ℤ) := by omega
    rw [h_sub] at h_cast
    exact h_cast
  have h1 : (h_seq m1 (d + 1) : ℤ) * 2 ≤ (m1 0 + m1 1 + m1 2 + 1 - (d + 1 : ℤ)) * (m1 0 + m1 1 + m1 2 + 2 - (d + 1 : ℤ)) := by
    have h_bound := h_seq_upper_bound_int_all m1 (d + 1)
    have hd_cast : ((d + 1 : ℕ) : ℤ) = (d + 1 : ℤ) := by omega
    have h_alg : ((m1 0 : ℤ) + (m1 1 : ℤ) + (m1 2 : ℤ) - ((d + 1 : ℕ) : ℤ) + 1) * ((m1 0 : ℤ) + (m1 1 : ℤ) + (m1 2 : ℤ) - ((d + 1 : ℕ) : ℤ) + 2) = ((m1 0 : ℤ) + (m1 1 : ℤ) + (m1 2 : ℤ) + 1 - (d + 1 : ℤ)) * ((m1 0 : ℤ) + (m1 1 : ℤ) + (m1 2 : ℤ) + 2 - (d + 1 : ℤ)) := by
      rw [hd_cast]
      ring
    rw [h_alg] at h_bound
    exact h_bound
  have h2 : diff (fun k => (h_seq m1 k : ℤ)) (d + 1) ≤ 0 := by
    apply h_seq_diff_le_zero_of_past_mid
    omega
  have h3_eval : shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) * 2 = (m1 0 + m1 1 + m1 2 + 1 - (d + 1 : ℤ)) * (m1 0 + m1 1 + m1 2 + 2 - (d + 1 : ℤ)) := by
    unfold shifted_h_seq
    rw [ite_eq_left hd_c]
    have hd_eval := h_seq_pure_upper_ext (reduced_monomial m1 m2 x) (d + 1 - (m1 x + 1)) (by omega)
    have hd_cast : ((d + 1 - (m1 x + 1) : ℕ) : ℤ) = (d + 1 : ℤ) - (m1 x + 1 : ℤ) := by omega
    have h_alg_1 : ((reduced_monomial m1 m2 x) 0 : ℤ) + ((reduced_monomial m1 m2 x) 1 : ℤ) + ((reduced_monomial m1 m2 x) 2 : ℤ) + 1 - ((d + 1 - (m1 x + 1) : ℕ) : ℤ) = (m1 0 : ℤ) + (m1 1 : ℤ) + (m1 2 : ℤ) + 1 - (d + 1 : ℤ) := by linarith [h_red_deg_z]
    have h_alg_2 : ((reduced_monomial m1 m2 x) 0 : ℤ) + ((reduced_monomial m1 m2 x) 1 : ℤ) + ((reduced_monomial m1 m2 x) 2 : ℤ) + 2 - ((d + 1 - (m1 x + 1) : ℕ) : ℤ) = (m1 0 : ℤ) + (m1 1 : ℤ) + (m1 2 : ℤ) + 2 - (d + 1 : ℤ) := by linarith [h_red_deg_z]
    rw [h_alg_1, h_alg_2] at hd_eval
    exact hd_eval
  have h4_diff : diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = (d + 1 : ℤ) - (m1 0 + m1 1 + m1 2 + 2) := by
    have hd_pos_d1 : d + 1 > 0 := by omega
    have h_diff_eq := diff_shifted_h_seq_eq_ge (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) hd_pos_d1 hd_c
    rw [h_diff_eq]
    have hd_diff_eval := h_seq_pure_upper_diff_ext (reduced_monomial m1 m2 x) (d + 1 - (m1 x + 1)) (by omega)
    have hd_cast : ((d + 1 - (m1 x + 1) : ℕ) : ℤ) = (d + 1 : ℤ) - (m1 x + 1 : ℤ) := by omega
    have h_alg : -(((reduced_monomial m1 m2 x) 0 : ℤ) + ((reduced_monomial m1 m2 x) 1 : ℤ) + ((reduced_monomial m1 m2 x) 2 : ℤ) + 2 - ((d + 1 - (m1 x + 1) : ℕ) : ℤ)) = (d + 1 : ℤ) - ((m1 0 : ℤ) + (m1 1 : ℤ) + (m1 2 : ℤ) + 2) := by linarith [h_red_deg_z]
    rw [h_alg] at hd_diff_eval
    exact hd_diff_eval
  have h5_le : (d + 1 : ℤ) ≤ m1 0 + m1 1 + m1 2 + 2 := by omega
  exact ⟨h1, h2, h3_eval, h4_diff, h5_le⟩

lemma inr_high_master_ineq (S1 U : ℤ) (hS1 : S1 ≥ 0) (hU : U ≥ -2) :
  2 * (U + 1) * (U + 2) ≤ 2 * (S1 + U + 2) ^ 2 := by
  have h_cases : U = -2 ∨ U = -1 ∨ U ≥ 0 := by omega
  rcases h_cases with rfl | rfl | hU_pos
  · nlinarith
  · nlinarith
  · nlinarith

lemma inr_high_reduction_goal_helper {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
    (h1 : diff2 (fun k => (h_seq m1 k : ℤ)) (d + 1) = 0)
    (h2 : diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = 1)
    (h2_high : d + 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + 2 ∧ d + 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 2 ∧ d + 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 2 + 2 ∧ d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 2) :
  H_seq (m1:=m1) (m2:=m2) x (d + 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1))^2 := by
  have hc : d + 1 ≥ m1 x + 1 := diff2_shifted_h_seq_eq_one_implies _ _ _ h2
  have hz := diff2_h_seq_eq_Z_calc m1 (d + 1) (by omega)
  rw [h1] at hz
  have h_bounds := inr_high_H_eval_bounds x d hd h_gt h_le h_deg hz.symm hc h2_high
  rcases h_bounds with ⟨h_h1, h_diff1, h_shift, h_diff_shift, h_d_bound⟩
  rw [H_seq_eval_add, diff_H_seq_eval_add]
  let S1 := - diff (fun k => (h_seq m1 k : ℤ)) (d + 1)
  let U := (m1 0 + m1 1 + m1 2 : ℤ) - (d + 1 : ℤ)
  have h_U_diff : diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = -(U + 2) := by
    have hd_sub2 : -(U + 2) = (d + 1 : ℤ) - (m1 0 + m1 1 + m1 2 + 2 : ℤ) := by omega
    rw [h_diff_shift, hd_sub2]
  have h_U_h : shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) * 2 = (U + 1) * (U + 2) := by
    have h_sub1 : (m1 0 + m1 1 + m1 2 + 1 - (d + 1 : ℤ)) = U + 1 := by omega
    have h_sub2 : (m1 0 + m1 1 + m1 2 + 2 - (d + 1 : ℤ)) = U + 2 := by omega
    rw [h_shift, h_sub1, h_sub2]
  have h_U_h1 : (h_seq m1 (d + 1) : ℤ) * 2 ≤ (U + 1) * (U + 2) := by
    have h_sub1 : (m1 0 + m1 1 + m1 2 + 1 - (d + 1 : ℤ)) = U + 1 := by omega
    have h_sub2 : (m1 0 + m1 1 + m1 2 + 2 - (d + 1 : ℤ)) = U + 2 := by omega
    have h_ineq := h_h1
    rw [h_sub1, h_sub2] at h_ineq
    exact h_ineq
  have h_master := inr_high_master_ineq S1 U (by omega) (by omega)
  have h_LHS : (H_seq (m1:=m1) (m2:=m2) x (d + 1)) * 2 = (h_seq m1 (d + 1) : ℤ) * 2 + shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) * 2 := by
    rw [H_seq_eval_add]
    ring
  have h_mid : (H_seq (m1:=m1) (m2:=m2) x (d + 1)) * 2 ≤ (U + 1) * (U + 2) + (U + 1) * (U + 2) := by
    linarith
  have h_RHS : (diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1))^2 = (-S1 + -(U + 2))^2 := by
    have hd_sub : diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1) = -S1 + -(U + 2) := by
      rw [diff_H_seq_eval_add, h_U_diff]

      have hS1_eq : -S1 = diff (fun k => ↑(h_seq m1 k)) (d + 1) := by
        change -(-diff (fun k => ↑(h_seq m1 k)) (d + 1)) = diff (fun k => ↑(h_seq m1 k)) (d + 1)
        ring
      rw [hS1_eq]
    rw [hd_sub]
  have h_final : (H_seq (m1:=m1) (m2:=m2) x (d + 1)) * 2 ≤ 2 * (diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1))^2 := by
    calc
      (H_seq (m1:=m1) (m2:=m2) x (d + 1)) * 2 ≤ (U + 1) * (U + 2) + (U + 1) * (U + 2) := h_mid
      _ = 2 * (U + 1) * (U + 2) := by ring
      _ ≤ 2 * (S1 + U + 2) ^ 2 := h_master
      _ = 2 * (-S1 + -(U + 2)) ^ 2 := by ring
      _ = 2 * (diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1))^2 := by rw [← h_RHS]
  have h_final_real : H_seq (m1:=m1) (m2:=m2) x (d + 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1))^2 := by linarith [h_final]
  have h_eq1 : (h_seq m1 (d + 1) : ℤ) + shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) = H_seq (m1:=m1) (m2:=m2) x (d + 1) := by rw [H_seq_eval_add]
  have h_eq2 : diff (fun k => ↑(h_seq m1 k)) (d + 1) + diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = diff (H_seq (m1:=m1) (m2:=m2) x) (d + 1) := by rw [diff_H_seq_eval_add]
  rw [h_eq1, h_eq2]
  exact h_final_real

lemma diff2_H_seq_eq_one_implies_inr_high {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
    (h1 : diff2 (fun k => (h_seq m1 k : ℤ)) (d + 1) = 0)
    (h2 : diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = 1)
    (h2_high : d + 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + 2 ∧ d + 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 2 ∧ d + 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 2 + 2 ∧ d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 2) :
  H_seq (m1:=m1) (m2:=m2) x (d - 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 := by
  apply H_seq_diff2_reduction x d hd
  · rw [diff2_H_seq_eq_add, h1, h2]; ring
  · exact inr_high_reduction_goal_helper x d hd h_gt h_le h_deg h1 h2 h2_high

lemma diff2_H_seq_eq_one_implies_inr {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
    (h1 : diff2 (fun k => (h_seq m1 k : ℤ)) (d + 1) = 0)
    (h2 : diff2 (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) (d + 1) = 1) :
  H_seq (m1:=m1) (m2:=m2) x (d - 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 := by
  have hc : d + 1 ≥ m1 x + 1 := diff2_shifted_h_seq_eq_one_implies _ _ _ h2
  have h2_eq : diff2 (fun k => (h_seq (reduced_monomial m1 m2 x) k : ℤ)) (d + 1 - (m1 x + 1)) = 1 := diff2_shifted_h_seq_eq_one_implies_eq _ _ _ h2
  have h2_cases := diff2_h_seq_eq_one_implies (reduced_monomial m1 m2 x) (d + 1 - (m1 x + 1)) h2_eq
  rcases h2_cases with h2_low | h2_high
  · exact diff2_H_seq_eq_one_implies_inr_low x d hd h_gt h_le h_deg h1 h2 h2_low
  · exact diff2_H_seq_eq_one_implies_inr_high x d hd h_gt h_le h_deg h1 h2 h2_high

lemma diff2_H_seq_eq_one_implies {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2) :
  diff2 (H_seq (m1:=m1) (m2:=m2) x) (d + 1) = 1 →
  H_seq (m1:=m1) (m2:=m2) x (d - 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 := by
  intro h_eq
  have h_cases := diff2_H_seq_eq_one_implies_cases x (d + 1) h_eq
  rcases h_cases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact diff2_H_seq_eq_one_implies_inl x d hd h_gt h_le h_deg h1 h2
  · exact diff2_H_seq_eq_one_implies_inr x d hd h_gt h_le h_deg h1 h2

lemma m_deg_eq (m1 m2 : Monomial 3) (h_deg : totalDeg m1 = totalDeg m2) :
  m1 0 + m1 1 + m1 2 = m2 0 + m2 1 + m2 2 := by
  have h1 : totalDeg m1 = m1 0 + m1 1 + m1 2 := by
    unfold totalDeg
    exact ( Finset.sum_subset m1.support.subset_univ (by simp_all)).trans ( Fin.sum_univ_three _)
  have h2 : totalDeg m2 = m2 0 + m2 1 + m2 2 := by
    unfold totalDeg
    exact (m2|>.sum_fintype _ fun and=>rfl).trans (Fin.sum_univ_three _)
  omega

lemma h1_high_h2_low_contradiction {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ)
  (_h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2)
  (h1_high : d + 1 ≥ m1 0 + m1 1 + 2 ∧ d + 1 ≥ m1 1 + m1 2 + 2 ∧ d + 1 ≥ m1 0 + m1 2 + 2 ∧ d + 1 ≤ m1 0 + m1 1 + m1 2 + 2)
  (h2_low : d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 0 ∧ d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 1 ∧ d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 2) :
  False := by
  have h_sum := m_deg_eq m1 m2 h_deg
  have hx_val : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by
    have h : x.val < 3 := x.isLt
    omega
  rcases hx_val with hx | hx | hx
  · have eqx : x = 0 := by apply Fin.ext; exact hx
    rw [eqx] at _h_gt h2_low h_le
    have eq0 : (reduced_monomial m1 m2 0) 0 = m2 0 - m1 0 - 1 := by norm_num[reduced_monomial]
    have eq1 : (reduced_monomial m1 m2 0) 1 = m2 1 := by norm_num[reduced_monomial]
    have eq2 : (reduced_monomial m1 m2 0) 2 = m2 2 := by simp_all!-contextual[reduced_monomial]
    have h_le1 := h_le 1 (by decide)
    have h_le2 := h_le 2 (by decide)
    rw [eq0, eq1, eq2] at h2_low
    omega
  · have eqx : x = 1 := by apply Fin.ext; exact hx
    rw [eqx] at _h_gt h2_low h_le
    have eq0 : (reduced_monomial m1 m2 1) 0 = m2 0 := by norm_num[reduced_monomial]
    have eq1 : (reduced_monomial m1 m2 1) 1 = m2 1 - m1 1 - 1 := by rfl
    have eq2 : (reduced_monomial m1 m2 1) 2 = m2 2 := by norm_num+decide[reduced_monomial]
    have h_le0 := h_le 0 (by decide)
    have h_le2 := h_le 2 (by decide)
    rw [eq0, eq1, eq2] at h2_low
    omega
  · have eqx : x = 2 := by apply Fin.ext; exact hx
    rw [eqx] at _h_gt h2_low h_le
    have eq0 : (reduced_monomial m1 m2 2) 0 = m2 0 := by norm_num+decide[reduced_monomial]
    have eq1 : (reduced_monomial m1 m2 2) 1 = m2 1 := by rfl
    have eq2 : (reduced_monomial m1 m2 2) 2 = m2 2 - m1 2 - 1 := by norm_num[reduced_monomial]
    have h_le0 := h_le 0 (by decide)
    have h_le1 := h_le 1 (by decide)
    rw [eq0, eq1, eq2] at h2_low
    omega

lemma diff2_H_seq_eq_two_implies_inr_inr {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (_h_gt : m2 x > m1 x) (_h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (_h_deg : totalDeg m1 = totalDeg m2)
    (h1_high : d + 1 ≥ m1 0 + m1 1 + 2 ∧ d + 1 ≥ m1 1 + m1 2 + 2 ∧ d + 1 ≥ m1 0 + m1 2 + 2 ∧ d + 1 ≤ m1 0 + m1 1 + m1 2 + 2)
    (h2_high : d + 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + 2 ∧
      d + 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 2 ∧
      d + 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 2 + 2 ∧
      d + 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 2) :
    2 * H_seq (m1:=m1) (m2:=m2) x (d - 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 := by
  rcases h1_high with ⟨h1_1, h1_2, h1_3, h1_4⟩
  rcases h2_high with ⟨h2_1, h2_2, h2_3, h2_4⟩
  have hd_1_upper : d - 1 ≥ m1 0 + m1 1 ∧ d - 1 ≥ m1 1 + m1 2 ∧ d - 1 ≥ m1 0 + m1 2 ∧ d - 1 ≤ m1 0 + m1 1 + m1 2 + 1 := by omega
  have heval1 : (h_seq m1 (d - 1) : ℤ) * 2 = (m1 0 + m1 1 + m1 2 + 1 - (d - 1 : ℕ) : ℤ) * (m1 0 + m1 1 + m1 2 + 2 - (d - 1 : ℕ) : ℤ) := h_seq_pure_upper m1 (d - 1) hd_1_upper
  have hd_upper : d ≥ m1 0 + m1 1 + 1 ∧ d ≥ m1 1 + m1 2 + 1 ∧ d ≥ m1 0 + m1 2 + 1 ∧ d ≤ m1 0 + m1 1 + m1 2 + 1 := by omega
  have hdiff1 : diff (fun k => (h_seq m1 k : ℤ)) d = - (m1 0 + m1 1 + m1 2 + 2 - d : ℤ) := h_seq_pure_upper_diff m1 d hd_upper
  have hc : d - 1 ≥ m1 x + 1 := by omega
  have h_shift_eval : shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1) (d - 1) = (h_seq (reduced_monomial m1 m2 x) (d - 1 - (m1 x + 1)) : ℤ) := by
    unfold shifted_h_seq; rw [ite_eq_left hc]
  have hd_2_upper : d - 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 ∧ d - 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 ∧ d - 1 - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 2 ∧ d - 1 - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 1 := by omega
  have heval2 : (h_seq (reduced_monomial m1 m2 x) (d - 1 - (m1 x + 1)) : ℤ) * 2 = ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 1 - (d - 1 - (m1 x + 1) : ℕ) : ℤ) * ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 2 - (d - 1 - (m1 x + 1) : ℕ) : ℤ) := h_seq_pure_upper (reduced_monomial m1 m2 x) (d - 1 - (m1 x + 1)) hd_2_upper
  have hc2 : d ≥ m1 x + 1 := by omega
  have hc_diff : d - 1 ≥ m1 x + 1 := hc
  have h_shift_diff : diff (shifted_h_seq (reduced_monomial m1 m2 x) (m1 x + 1)) d = diff (fun k => (h_seq (reduced_monomial m1 m2 x) k : ℤ)) (d - (m1 x + 1)) := by
    unfold diff shifted_h_seq
    have h_ne : d ≠ 0 := by omega
    rw [ite_eq_right h_ne, ite_eq_left hc2, ite_eq_left hc_diff]
    have h_sub : d - 1 - (m1 x + 1) = d - (m1 x + 1) - 1 := by omega
    rw [h_sub]
    have h_ne2 : d - (m1 x + 1) ≠ 0 := by omega
    rw [ite_eq_right h_ne2]
  have hd_3_upper : d - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + 1 ∧ d - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 1 ∧ d - (m1 x + 1) ≥ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 2 + 1 ∧ d - (m1 x + 1) ≤ (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 1 := by omega
  have hdiff2 : diff (fun k => (h_seq (reduced_monomial m1 m2 x) k : ℤ)) (d - (m1 x + 1)) = - ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 2 - (d - (m1 x + 1) : ℕ) : ℤ) := h_seq_pure_upper_diff (reduced_monomial m1 m2 x) (d - (m1 x + 1)) hd_3_upper
  have h_H_eval : H_seq (m1:=m1) (m2:=m2) x (d - 1) = (h_seq m1 (d - 1) : ℤ) + (h_seq (reduced_monomial m1 m2 x) (d - 1 - (m1 x + 1)) : ℤ) := by
    rw [H_seq_eval_add, h_shift_eval]
  have h_H_diff : diff (H_seq (m1:=m1) (m2:=m2) x) d = diff (fun k => (h_seq m1 k : ℤ)) d + diff (fun k => (h_seq (reduced_monomial m1 m2 x) k : ℤ)) (d - (m1 x + 1)) := by
    rw [diff_H_seq_eval_add, h_shift_diff]
  rw [h_H_eval, h_H_diff]
  let U1 : ℤ := m1 0 + m1 1 + m1 2 - d
  let U2 : ℤ := (reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 - (d - (m1 x + 1))
  have hU1_pos : U1 ≥ -1 := by clear h2_1 h2_2 h2_3 h2_4; omega
  have hU2_pos : U2 ≥ -1 := by clear h1_1 h1_2 h1_3 h1_4; omega
  have h_alg := log_concave_algebra_upper_eval U1 U2 hU1_pos hU2_pos
  have h_sub1 : (m1 0 + m1 1 + m1 2 + 1 - (d - 1 : ℕ) : ℤ) = U1 + 2 := by clear h2_1 h2_2 h2_3 h2_4; omega
  have h_sub2 : (m1 0 + m1 1 + m1 2 + 2 - (d - 1 : ℕ) : ℤ) = U1 + 3 := by clear h2_1 h2_2 h2_3 h2_4; omega
  have h_sub3 : ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 1 - (d - 1 - (m1 x + 1) : ℕ) : ℤ) = U2 + 2 := by clear h1_1 h1_2 h1_3 h1_4; omega
  have h_sub4 : ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 2 - (d - 1 - (m1 x + 1) : ℕ) : ℤ) = U2 + 3 := by clear h1_1 h1_2 h1_3 h1_4; omega
  have h_sub5 : - (m1 0 + m1 1 + m1 2 + 2 - d : ℤ) = - (U1 + 2) := by clear h2_1 h2_2 h2_3 h2_4; omega
  have h_sub6 : - ((reduced_monomial m1 m2 x) 0 + (reduced_monomial m1 m2 x) 1 + (reduced_monomial m1 m2 x) 2 + 2 - (d - (m1 x + 1) : ℕ) : ℤ) = - (U2 + 2) := by clear h1_1 h1_2 h1_3 h1_4; omega
  rw [h_sub1, h_sub2] at heval1
  rw [h_sub3, h_sub4] at heval2
  rw [h_sub5] at hdiff1
  rw [h_sub6] at hdiff2
  have h_LHS : (2 * H_seq (m1:=m1) (m2:=m2) x (d - 1) : ℤ) = (h_seq m1 (d - 1) : ℤ) * 2 + (h_seq (reduced_monomial m1 m2 x) (d - 1 - (m1 x + 1)) : ℤ) * 2 := by
    rw [h_H_eval]
    ring
  have h_RHS : (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 = (diff (fun k => (h_seq m1 k : ℤ)) d + diff (fun k => (h_seq (reduced_monomial m1 m2 x) k : ℤ)) (d - (m1 x + 1))) ^ 2 := by
    rw [h_H_diff]
  have h_mid : (h_seq m1 (d - 1) : ℤ) * 2 + (h_seq (reduced_monomial m1 m2 x) (d - 1 - (m1 x + 1)) : ℤ) * 2 ≤ (diff (fun k => (h_seq m1 k : ℤ)) d + diff (fun k => (h_seq (reduced_monomial m1 m2 x) k : ℤ)) (d - (m1 x + 1))) ^ 2 := by
    calc
      (h_seq m1 (d - 1) : ℤ) * 2 + (h_seq (reduced_monomial m1 m2 x) (d - 1 - (m1 x + 1)) : ℤ) * 2 = (U1 + 2) * (U1 + 3) + (U2 + 2) * (U2 + 3) := by rw [heval1, heval2]
      _ ≤ (- (U1 + 2) - (U2 + 2)) ^ 2 := h_alg
      _ = (diff (fun k => (h_seq m1 k : ℤ)) d + diff (fun k => (h_seq (reduced_monomial m1 m2 x) k : ℤ)) (d - (m1 x + 1))) ^ 2 := by rw [hdiff1, hdiff2]; ring
  linarith

lemma h1_low_contradiction {m1 : Monomial 3} (x : Fin 3) (d : ℕ)
  (h1_low : d + 1 ≤ m1 0 ∧ d + 1 ≤ m1 1 ∧ d + 1 ≤ m1 2)
  (h_ge : d + 1 ≥ m1 x + 1) : False := by
  have hx_val : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 := by
    have h : x.val < 3 := x.isLt
    omega
  rcases hx_val with hx | hx | hx
  · have h_eq : m1 x = m1 0 := by
      apply congrArg m1
      exact Fin.ext hx
    rw [h_eq] at h_ge
    omega
  · have h_eq : m1 x = m1 1 := by
      apply congrArg m1
      exact Fin.ext hx
    rw [h_eq] at h_ge
    omega
  · have h_eq : m1 x = m1 2 := by
      apply congrArg m1
      exact Fin.ext hx
    rw [h_eq] at h_ge
    omega

lemma diff2_H_seq_eq_two_implies {m1 m2 : Monomial 3} (x : Fin 3) (d : ℕ) (hd : d > 0)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2) :
  diff2 (H_seq (m1:=m1) (m2:=m2) x) (d + 1) = 2 →
  2 * H_seq (m1:=m1) (m2:=m2) x (d - 1) ≤ (diff (H_seq (m1:=m1) (m2:=m2) x) d)^2 := by
  intro h_eq
  have h_both := diff2_H_seq_eq_two_implies_both_one x (d + 1) h_eq
  have h1 := diff2_h_seq_eq_one_implies m1 (d + 1) h_both.1
  have h_ge := diff2_shifted_h_seq_eq_one_implies (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) h_both.2
  have h_shift := diff2_shifted_h_seq_eq_one_implies_eq (reduced_monomial m1 m2 x) (m1 x + 1) (d + 1) h_both.2
  have h2 := diff2_h_seq_eq_one_implies (reduced_monomial m1 m2 x) (d + 1 - (m1 x + 1)) h_shift
  rcases h1 with h1_low | h1_high
  · exfalso; exact h1_low_contradiction x d h1_low h_ge
  · rcases h2 with h2_low | h2_high
    · exfalso; exact h1_high_h2_low_contradiction x d h_gt h_le h_deg h1_high h2_low
    · exact diff2_H_seq_eq_two_implies_inr_inr x d hd h_gt h_le h_deg h1_high h2_high

lemma sum_log_concave_helper {m1 m2 : Monomial 3} (x : Fin 3)
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) (h_deg : totalDeg m1 = totalDeg m2) :
    IsLogConcaveUpTo (totalDeg m1) (fun d =>
      h_seq m1 d + if d ≥ m1 x + 1 then h_seq (reduced_monomial m1 m2 x) (d - (m1 x + 1)) else 0) := by
  intro i hi
  have hi_pos : i > 0 := (Finset.mem_Ioo.mp hi).1
  let h_fun := H_seq (m1:=m1) (m2:=m2) x
  have h_diff2_bound := diff2_H_seq_le_two (m1:=m1) (m2:=m2) x (i + 1)
  have h_diff2_one := diff2_H_seq_eq_one_implies x i hi_pos h_gt h_le h_deg
  have h_diff2_two := diff2_H_seq_eq_two_implies x i hi_pos h_gt h_le h_deg
  have hx_nonneg : h_fun (i - 1) ≥ 0 := by
    exact Nat.cast_nonneg _
  have h_core := log_concave_core (h_fun (i - 1)) (diff h_fun i) (diff2 h_fun (i + 1)) hx_nonneg h_diff2_bound h_diff2_one h_diff2_two
  have h_seq1 : h_fun i = h_fun (i - 1) + diff h_fun i := diff_eq h_fun i hi_pos
  have h_seq2 : diff h_fun (i + 1) = diff h_fun i + diff2 h_fun (i + 1) := diff2_eq h_fun i hi_pos
  have h_seq3 : h_fun (i + 1) = h_fun i + diff h_fun (i + 1) := diff_eq h_fun (i + 1) (by omega)
  have h_alg : (h_fun i)^2 - h_fun (i - 1) * h_fun (i + 1) = (diff h_fun i)^2 - h_fun (i - 1) * diff2 h_fun (i + 1) := by
    calc
      (h_fun i)^2 - h_fun (i - 1) * h_fun (i + 1)
        = (h_fun (i - 1) + diff h_fun i)^2 - h_fun (i - 1) * (h_fun (i - 1) + diff h_fun i + (diff h_fun i + diff2 h_fun (i + 1))) := by
          rw [h_seq3, h_seq1, h_seq2]
      _ = (diff h_fun i)^2 - h_fun (i - 1) * diff2 h_fun (i + 1) := by ring
  have h_ineq : h_fun (i - 1) * h_fun (i + 1) ≤ (h_fun i)^2 := by linarith
  have h_cast : (((h_seq m1 (i - 1) + if i - 1 ≥ m1 x + 1 then h_seq (reduced_monomial m1 m2 x) (i - 1 - (m1 x + 1)) else 0) *
                 (h_seq m1 (i + 1) + if i + 1 ≥ m1 x + 1 then h_seq (reduced_monomial m1 m2 x) (i + 1 - (m1 x + 1)) else 0) : ℕ) : ℤ) ≤
                (((h_seq m1 i + if i ≥ m1 x + 1 then h_seq (reduced_monomial m1 m2 x) (i - (m1 x + 1)) else 0) ^ 2 : ℕ) : ℤ) := by
    rw [Nat.cast_mul, Nat.cast_pow]
    exact h_ineq
  exact Nat.cast_le.mp h_cast

lemma pureOSeq_eq_sum {P : PureOrderIdeal 3} {m1 m2 : Monomial 3} (x : Fin 3)
    (h_max_eq : maximalMonomials P.ideal = {m1, m2})
    (h_gt : m2 x > m1 x) (h_le : ∀ y, y ≠ x → m2 y ≤ m1 y) :
    pureOSequence P.ideal = fun d =>
      h_seq m1 d + if d ≥ m1 x + 1 then h_seq (reduced_monomial m1 m2 x) (d - (m1 x + 1)) else 0 := by
  funext d
  unfold pureOSequence h_seq
  have h_carrier := ideal_carrier_eq_union P m1 m2 h_max_eq
  rw [h_carrier]
  exact pureOSeq_decomposition x h_gt h_le d

theorem type_two_three_variables_logConcave (P : PureOrderIdeal 3)
    (ht : typePO P = 2) :
    IsLogConcaveUpTo (socleDegree P) (pureOSequence P.ideal) := by

  have h_max := type_two_implies_two_maximals P ht
  rcases h_max with ⟨m1, m2, h_neq, h_max_eq⟩
  have h_deg : totalDeg m1 = totalDeg m2 := by
    have h_pure := P.isPure
    have hm1 : m1 ∈ maximalMonomials P.ideal := by
      rw [h_max_eq]
      exact Finset.mem_insert_self m1 {m2}
    have hm2 : m2 ∈ maximalMonomials P.ideal := by
      rw [h_max_eq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self m2)
    exact h_pure m1 m2 hm1 hm2
  have h_var := exists_single_greater_var h_deg h_neq
  rcases h_var with ⟨x, h_gt, h_le⟩ | ⟨x, h_gt, h_le⟩
  · have h_max_eq2 : maximalMonomials P.ideal = {m2, m1} := by
      rw [h_max_eq]
      exact Finset.pair_comm m1 m2
    have h_eq := pureOSeq_eq_sum x h_max_eq2 h_gt h_le
    rw [h_eq]
    have h_socle : socleDegree P = totalDeg m2 := by
      have h_nonempty := P.maximal_nonempty
      have h_choose := Classical.choose_spec h_nonempty
      have h_pure := P.isPure
      have hm2 : m2 ∈ maximalMonomials P.ideal := by
        rw [h_max_eq]
        exact Finset.mem_insert_of_mem (Finset.mem_singleton_self m2)
      unfold socleDegree
      exact h_pure (Classical.choose h_nonempty) m2 h_choose hm2
    rw [h_socle]
    exact sum_log_concave_helper x h_gt h_le h_deg.symm
  · have h_eq := pureOSeq_eq_sum x h_max_eq h_gt h_le
    rw [h_eq]
    have h_socle : socleDegree P = totalDeg m1 := by
      have h_nonempty := P.maximal_nonempty
      have h_choose := Classical.choose_spec h_nonempty
      have h_pure := P.isPure
      have hm1 : m1 ∈ maximalMonomials P.ideal := by
        rw [h_max_eq]
        exact Finset.mem_insert_self m1 {m2}
      unfold socleDegree
      exact h_pure (Classical.choose h_nonempty) m1 h_choose hm1
    rw [h_socle]
    exact sum_log_concave_helper x h_gt h_le h_deg

end ResearchMain.PureOSequences.TypeTwo
