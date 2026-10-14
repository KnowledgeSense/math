import MainTheorems.PureOSequences.Basic
import MainTheorems.PureOSequences.IntervalShadows
import Mathlib.Data.Fin.Tuple.Basic

namespace ResearchMain.PureOSequences

noncomputable def pairMonomial (a b : ℕ) : Monomial 2 :=
  Finsupp.single 0 a + Finsupp.single 1 b

@[simp] theorem pairMonomial_zero (a b : ℕ) : pairMonomial a b 0 = a := by
  simp [pairMonomial]

@[simp] theorem pairMonomial_one (a b : ℕ) : pairMonomial a b 1 = b := by
  simp [pairMonomial]

@[simp] theorem degree_pairMonomial (a b : ℕ) : totalDeg (pairMonomial a b) = a + b := by
  simp [totalDeg_eq_sum_univ, Fin.sum_univ_two]

theorem degree_two (m : Monomial 2) : totalDeg m = m 0 + m 1 := by
  simp [totalDeg_eq_sum_univ, Fin.sum_univ_two]

theorem pairMonomial_ext (m : Monomial 2) : pairMonomial (m 0) (m 1) = m := by
  ext i
  fin_cases i <;> simp

theorem pairMonomial_le {a b : ℕ} {m : Monomial 2} :
    pairMonomial a b ≤ m ↔ a ≤ m 0 ∧ b ≤ m 1 := by
  constructor
  · intro h
    exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨h0, h1⟩ i
    fin_cases i <;> simp_all

theorem maximal_degree {r : ℕ} (P : PureOrderIdeal r) {g : Monomial r}
    (hg : g ∈ maximalMonomials P.ideal) : totalDeg g = socleDegree P :=
  P.isPure g (Classical.choose P.maximal_nonempty) hg
    (Classical.choose_spec P.maximal_nonempty)

noncomputable def degreeIndices (I : OrderIdeal 2) (d : ℕ) : Finset ℕ :=
  (I.carrier.filter fun m => totalDeg m = d).image fun m => m 0

theorem mem_degreeIndices (I : OrderIdeal 2) (d x : ℕ) :
    x ∈ degreeIndices I d ↔ x ≤ d ∧ pairMonomial x (d - x) ∈ I.carrier := by
  classical
  constructor
  · intro hx
    obtain ⟨m, hm, hmx⟩ := Finset.mem_image.mp hx
    obtain ⟨hm, hdeg⟩ := Finset.mem_filter.mp hm
    rw [degree_two] at hdeg
    have hxdeg : x ≤ d := by omega
    have hy : d - x = m 1 := by omega
    refine ⟨hxdeg, ?_⟩
    rw [hy, ← hmx, pairMonomial_ext]
    exact hm
  · rintro ⟨hxd, hm⟩
    apply Finset.mem_image.mpr
    exact ⟨pairMonomial x (d - x),
      Finset.mem_filter.mpr ⟨hm, by simp; omega⟩, by simp⟩

theorem degreeIndices_bound (I : OrderIdeal 2) (d : ℕ) :
    degreeIndices I d ⊆ Finset.range (d + 1) := by
  intro x hx
  exact Finset.mem_range.mpr (by have := (mem_degreeIndices I d x).mp hx; omega)

theorem degreeIndices_card (I : OrderIdeal 2) (d : ℕ) :
    (degreeIndices I d).card = pureOSequence I d := by
  classical
  apply Finset.card_image_of_injOn
  intro m hm n hn heq
  have hmdeg := (Finset.mem_filter.mp hm).2
  have hndeg := (Finset.mem_filter.mp hn).2
  change m 0 = n 0 at heq
  rw [degree_two] at hmdeg hndeg
  ext i
  fin_cases i
  · exact heq
  · change m 1 = n 1
    omega

theorem pure_degreeIndices_shadow (P : PureOrderIdeal 2) (d : ℕ)
    (hd : 1 ≤ d) (hde : d ≤ socleDegree P) :
    degreeIndices P.ideal (d - 1) = lowerShadow d (degreeIndices P.ideal d) := by
  classical
  ext x
  rw [mem_degreeIndices, mem_lowerShadow]
  constructor
  · rintro ⟨hxd, hm⟩
    obtain ⟨g, hg, hmg⟩ := exists_le_maximal P.ideal _ hm
    have hgmem := (mem_maximalMonomials_iff _ _).mp hg |>.1
    have hgdeg := maximal_degree P hg
    rw [degree_two] at hgdeg
    have hcoords := pairMonomial_le.mp hmg
    have hext : x < g 0 ∨ d - 1 - x < g 1 := by omega
    refine ⟨by omega, ?_⟩
    rcases hext with hx | hy
    · apply Or.inr
      apply (mem_degreeIndices P.ideal d (x + 1)).mpr
      refine ⟨by omega, P.ideal.mem_of_dvd hgmem (pairMonomial_le.mpr ⟨by omega, ?_⟩)⟩
      omega
    · apply Or.inl
      apply (mem_degreeIndices P.ideal d x).mpr
      refine ⟨by omega, P.ideal.mem_of_dvd hgmem (pairMonomial_le.mpr ⟨hcoords.1, ?_⟩)⟩
      omega
  · rintro ⟨hxd, hx | hx⟩
    · obtain ⟨_, hm⟩ := (mem_degreeIndices P.ideal d x).mp hx
      refine ⟨by omega, P.ideal.mem_of_dvd hm ?_⟩
      apply pairMonomial_le.mpr
      simp only [pairMonomial_zero, pairMonomial_one]
      omega
    · obtain ⟨_, hm⟩ := (mem_degreeIndices P.ideal d (x + 1)).mp hx
      refine ⟨by omega, P.ideal.mem_of_dvd hm ?_⟩
      apply pairMonomial_le.mpr
      simp only [pairMonomial_zero, pairMonomial_one]
      omega

theorem two_variable_concave (P : PureOrderIdeal 2) (i : ℕ)
    (hi : i ∈ Finset.Ioo 0 (socleDegree P)) :
    pureOSequence P.ideal (i - 1) + pureOSequence P.ideal (i + 1) ≤
      2 * pureOSequence P.ideal i := by
  have hi' := Finset.mem_Ioo.mp hi
  have h := iterated_shadow_concave (i + 1) (degreeIndices P.ideal (i + 1))
    (degreeIndices_bound _ _) (by omega)
  rw [← pure_degreeIndices_shadow P (i + 1) (by omega) (by omega)] at h
  simp only [Nat.add_sub_cancel] at h
  rw [← pure_degreeIndices_shadow P i (by omega) (by omega)] at h
  simpa only [degreeIndices_card] using h

theorem two_variable_logConcave (P : PureOrderIdeal 2) :
    IsLogConcaveUpTo (socleDegree P) (pureOSequence P.ideal) := by
  intro i hi
  have hc := two_variable_concave P i hi
  have hcZ : (pureOSequence P.ideal (i - 1) : ℤ) + pureOSequence P.ideal (i + 1) ≤
      2 * pureOSequence P.ideal i := by exact_mod_cast hc
  have hs := sq_nonneg ((pureOSequence P.ideal (i - 1) : ℤ) -
    pureOSequence P.ideal (i + 1))
  have hnon : 0 ≤ (pureOSequence P.ideal i : ℤ) := by positivity
  have hprod := mul_self_le_mul_self (by positivity : 0 ≤
    (pureOSequence P.ideal (i - 1) : ℤ) + pureOSequence P.ideal (i + 1)) hcZ
  exact_mod_cast (by nlinarith : (pureOSequence P.ideal (i - 1) : ℤ) *
    pureOSequence P.ideal (i + 1) ≤ (pureOSequence P.ideal i : ℤ) ^ 2)

end ResearchMain.PureOSequences
