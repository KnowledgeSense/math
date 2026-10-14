import MainTheorems.Corona.GraphClassification

namespace ResearchMain.Corona

open Classical Polynomial

variable {W : Type} [Fintype W] [DecidableEq W]

noncomputable def excessCount (H : SimpleGraph W) : ℕ :=
  ∑ S ∈ (independentSets H).erase ∅, (S.card - 1)

theorem independentSets_empty_mem (H : SimpleGraph W) : (∅ : Finset W) ∈ independentSets H :=
  (mem_independentSets _ _).mpr (independent_empty H)

theorem independencePolynomial_mean_identity (H : SimpleGraph W) :
    (independencePolynomial H).derivative.eval 1 =
      (independencePolynomial H).eval 1 - 1 + excessCount H := by
  have hc : ∑ S ∈ (independentSets H).erase ∅, S.card =
      excessCount H + ((independentSets H).erase ∅).card := by
    unfold excessCount
    have hone : ((independentSets H).erase ∅).card =
        ∑ _S ∈ (independentSets H).erase ∅, (1 : ℕ) := by simp
    rw [hone, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    have hn : S.card ≠ 0 := by
      intro h
      exact (Finset.mem_erase.mp hS).1 (Finset.card_eq_zero.mp h)
    omega
  have hs := Finset.sum_erase_add (independentSets H) (fun S => S.card) (independentSets_empty_mem H)
  simp only [Finset.card_empty, add_zero] at hs
  have hb := Finset.card_erase_add_one (independentSets_empty_mem H)
  rw [independencePolynomial_derivative_one, independencePolynomial_eval_one,
    ← Nat.cast_sum, ← hs, hc, Nat.cast_add, ← hb, Nat.cast_add, Nat.cast_one]
  ring

theorem independent_card_le_two_of_excess_one (H : SimpleGraph W) (hH : excessCount H = 1)
    {S : Finset W} (hS : H.IsIndepSet (S : Set W)) : S.card ≤ 2 := by
  by_cases he : S = ∅
  · simp [he]
  have hm : S ∈ (independentSets H).erase ∅ :=
    Finset.mem_erase.mpr ⟨he, (mem_independentSets _ _).mpr hS⟩
  have h := Finset.single_le_sum (fun T _ => Nat.zero_le (T.card - 1)) hm
  change S.card - 1 ≤ excessCount H at h
  omega

theorem excessCount_eq_pairCount (H : SimpleGraph W)
    (hcard : ∀ S ∈ independentSets H, S.card ≤ 2) : excessCount H = independentCount H 2 := by
  have he : ((independentSets H).erase ∅).filter (fun S => S.card = 2) =
      (independentSets H).filter (fun S => S.card = 2) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · tauto
    · rintro ⟨hS, hc⟩
      refine ⟨⟨?_, hS⟩, hc⟩
      intro h
      simp [h] at hc
  unfold excessCount independentCount
  rw [← he]
  have hb : (∑ S ∈ (independentSets H).erase ∅, if S.card = 2 then (1 : ℕ) else 0) =
      (((independentSets H).erase ∅).filter (fun S => S.card = 2)).card := by
    exact Finset.sum_boole (R := ℕ) (fun S : Finset W => S.card = 2)
      ((independentSets H).erase ∅)
  rw [← hb]
  apply Finset.sum_congr rfl
  intro S hS
  have hc := hcard S (Finset.mem_erase.mp hS).2
  have hn : S.card ≠ 0 := by
    intro h
    exact (Finset.mem_erase.mp hS).1 (Finset.card_eq_zero.mp h)
  by_cases h₂ : S.card = 2
  · simp [h₂]
  · have h₁ : S.card = 1 := by omega
    simp [h₁]

theorem independencePolynomial_mean_one_iff (H : SimpleGraph W) :
    (independencePolynomial H).derivative.eval 1 = (independencePolynomial H).eval 1 ↔
      CliqueMinusEdge H := by
  rw [cliqueMinusEdge_iff_unique_pair]
  constructor
  · intro h
    have he : excessCount H = 1 := by
      have h' := independencePolynomial_mean_identity H
      rw [h] at h'
      have hc : (excessCount H : ℝ) = 1 := by linarith
      exact_mod_cast hc
    have hc := excessCount_eq_pairCount H (fun S hS =>
      independent_card_le_two_of_excess_one H he ((mem_independentSets _ _).mp hS))
    omega
  · intro h
    rw [unique_pair_polynomial H h, symmetricQuadratic]
    simp [derivative_add]
    ring

end ResearchMain.Corona
