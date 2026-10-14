import Mathlib.Algebra.Polynomial.RuleOfSigns
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

open Finset Polynomial
namespace ReciprocalQGamma

lemma signVariations_lt_support (p : ℝ[X]) (hp : p ≠ 0) :
    p.signVariations < p.support.card := by
  generalize hn : p.support.card = n
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases he : p.eraseLead = 0
    · have hc := Polynomial.card_support_eraseLead_add_one hp
      have hs := Polynomial.signVariations_eq_eraseLead_add_ite hp
      simp only [he, support_zero, card_empty, zero_add] at hc
      have hz : SignType.sign p.leadingCoeff ≠ 0 := by
        simp [hp]
      simp only [he, Polynomial.signVariations_zero, Polynomial.leadingCoeff_zero,
        sign_zero, neg_zero, hz, ite_false, zero_add] at hs
      omega
    · have hlt : p.eraseLead.support.card < n := by
        simpa [hn] using Polynomial.eraseLead_support_card_lt hp
      have hi := ih _ hlt p.eraseLead he rfl
      have hc := Polynomial.card_support_eraseLead_add_one hp
      have hs := Polynomial.signVariations_le_eraseLead_succ p
      omega

lemma generalizedVandermonde_ne_zero {r : ℕ}
    (x : Fin r → ℝ) (d : Fin r → ℕ)
    (hx : StrictMono x) (hpos : ∀ i, 0 < x i) (hd : StrictMono d) :
    Matrix.det (fun i j => x i ^ d j) ≠ 0 := by
  classical
  intro hzero
  obtain ⟨c, hc, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hzero
  let p : ℝ[X] := ∑ j : Fin r, Polynomial.monomial (d j) (c j)
  have hcoeff (j : Fin r) : p.coeff (d j) = c j := by
    simp [p, Polynomial.coeff_monomial, hd.injective.eq_iff]
  have hp : p ≠ 0 := by
    intro hp
    apply hc
    funext j
    simpa [hp] using (hcoeff j).symm
  have hs : p.support ⊆ Finset.univ.image d := by
    intro k hk
    by_contra hn
    have hn' : ∀ j, d j ≠ k := by simpa using hn
    have hz : p.coeff k = 0 := by
      simp [p, Polynomial.coeff_monomial, hn']
    exact Polynomial.mem_support_iff.mp hk hz
  have hcard : p.support.card ≤ r := by
    calc
      p.support.card ≤ (Finset.univ.image d).card := Finset.card_le_card hs
      _ ≤ r := by simpa using Finset.card_image_le (s := Finset.univ) (f := d)
  have heval (i : Fin r) : p.eval (x i) = 0 := by
    have h := congrFun hker i
    simpa [p, Matrix.mulVec, dotProduct, Polynomial.eval_finsetSum, mul_comm] using h
  have hroots : Finset.univ.image x ⊆
      (p.roots.filter (fun a => 0 < a)).toFinset := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    simp [Polynomial.mem_roots hp, heval i, hpos i]
  have hr : r ≤ p.roots.countP (fun a => 0 < a) := by
    calc
      r = (Finset.univ.image x).card := by simp [Finset.card_image_of_injective, hx.injective]
      _ ≤ (p.roots.filter (fun a => 0 < a)).toFinset.card := Finset.card_le_card hroots
      _ ≤ (p.roots.filter (fun a => 0 < a)).card := Multiset.toFinset_card_le _
      _ = _ := (Multiset.countP_eq_card_filter _ _).symm
  have hv := Polynomial.roots_countP_pos_le_signVariations p
  have hl := signVariations_lt_support p hp
  omega

lemma generalizedVandermonde_geometric_pos {r : ℕ} (d : Fin r → ℕ)
    (hd : StrictMono d) :
    0 < Matrix.det (fun i j : Fin r => ((2 : ℝ) ^ i.val) ^ d j) := by
  have heq : (fun i j : Fin r => ((2 : ℝ) ^ i.val) ^ d j) =
      (Matrix.vandermonde (fun j => (2 : ℝ) ^ d j)).transpose := by
    ext i j
    change ((2 : ℝ)^i.val)^d j = ((2 : ℝ)^d j)^i.val
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [heq, Matrix.det_transpose, Matrix.det_vandermonde]
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  apply sub_pos.mpr
  exact pow_lt_pow_right₀ (by norm_num) (hd (Finset.mem_Ioi.mp hj))

lemma generalizedVandermonde_pos {r : ℕ}
    (x : Fin r → ℝ) (d : Fin r → ℕ)
    (hx : StrictMono x) (hpos : ∀ i, 0 < x i) (hd : StrictMono d) :
    0 < Matrix.det (fun i j => x i ^ d j) := by
  let y : ℝ → Fin r → ℝ := fun t i => (1-t) * (2 : ℝ)^i.val + t*x i
  let f : ℝ → ℝ := fun t => Matrix.det (fun i j => y t i ^ d j)
  have hcont : Continuous f := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact (((continuous_const.sub continuous_id).mul continuous_const).add
      (continuous_id.mul continuous_const)).pow _
  have hmono (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : StrictMono (y t) := by
    intro i j hij
    have hp : (2 : ℝ)^i.val < 2^j.val := pow_lt_pow_right₀ (by norm_num) hij
    have hxx := hx hij
    dsimp [y]
    have h1 : 0 ≤ 1-t := sub_nonneg.mpr ht.2
    have h2 := mul_nonneg h1 (le_of_lt (sub_pos.mpr hp))
    have h3 := mul_nonneg ht.1 (le_of_lt (sub_pos.mpr hxx))
    by_cases ht0 : t = 0
    · simp [ht0, hp]
    · have h4 := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) (sub_pos.mpr hxx)
      nlinarith
  have hypos (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ∀ i, 0 < y t i := by
    intro i
    have hp : 0 < (2 : ℝ)^i.val := pow_pos (by norm_num) _
    have hxx := hpos i
    dsimp [y]
    have h1 := mul_nonneg (sub_nonneg.mpr ht.2) hp.le
    by_cases ht0 : t = 0
    · simp [ht0]
    · have h2 := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) hxx
      linarith
  have hne (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : f t ≠ 0 :=
    generalizedVandermonde_ne_zero (y t) d (hmono t ht) (hypos t ht) hd
  have hzero : 0 < f 0 := by
    simpa [f, y] using generalizedVandermonde_geometric_pos d hd
  have hone : f 1 = Matrix.det (fun i j => x i ^ d j) := by simp [f, y]
  by_contra hnot
  have hle : f 1 ≤ 0 := by simpa [hone] using le_of_not_gt hnot
  obtain ⟨t, ht, hft⟩ := intermediate_value_Icc' (show (0 : ℝ) ≤ 1 by norm_num)
    hcont.continuousOn ⟨hle, hzero.le⟩
  exact hne t ht hft

end ReciprocalQGamma
