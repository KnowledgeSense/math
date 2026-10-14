/-
Copyright 2026 Google LLC
Definitions adapted from AlphaProof Nexus Results, under the Apache 2.0 license.
See THIRD_PARTY_LICENSES/Apache-2.0.txt.
-/
import Mathlib.Data.Finsupp.Interval
import Mathlib.Order.Preorder.Finite
import Mathlib.Tactic

namespace ResearchMain.PureOSequences

open Classical

abbrev Monomial (r : ℕ) := Fin r →₀ ℕ

def totalDeg {r : ℕ} (m : Monomial r) : ℕ := m.sum fun _ e => e

structure OrderIdeal (r : ℕ) where
  carrier : Finset (Monomial r)
  downward_closed : ∀ {m n}, n ∈ carrier → m ≤ n → m ∈ carrier

theorem OrderIdeal.mem_of_dvd {r : ℕ} (I : OrderIdeal r) {m n : Monomial r}
    (hn : n ∈ I.carrier) (hmn : m ≤ n) : m ∈ I.carrier :=
  I.downward_closed hn hmn

noncomputable def divisorsFinset {r : ℕ} (g : Monomial r) : Finset (Monomial r) :=
  Finset.Iic g

@[simp] theorem mem_divisorsFinset_iff {r : ℕ} {m g : Monomial r} :
    m ∈ divisorsFinset g ↔ m ≤ g := Finset.mem_Iic

noncomputable def generatedOrderIdeal {r : ℕ} (G : Finset (Monomial r)) : OrderIdeal r where
  carrier := G.biUnion divisorsFinset
  downward_closed := by
    intro m n hn hmn
    obtain ⟨g, hg, hng⟩ := Finset.mem_biUnion.mp hn
    exact Finset.mem_biUnion.mpr ⟨g, hg, mem_divisorsFinset_iff.mpr
      (hmn.trans (mem_divisorsFinset_iff.mp hng))⟩

@[simp] theorem mem_generatedOrderIdeal_iff {r : ℕ} {G : Finset (Monomial r)}
    {m : Monomial r} :
    m ∈ (generatedOrderIdeal G).carrier ↔ ∃ g ∈ G, m ≤ g := by
  simp [generatedOrderIdeal]

def IsMaximalIn {r : ℕ} (I : OrderIdeal r) (m : Monomial r) : Prop :=
  m ∈ I.carrier ∧ ∀ n, n ∈ I.carrier → m ≤ n → n ≤ m

noncomputable def maximalMonomials {r : ℕ} (I : OrderIdeal r) : Finset (Monomial r) :=
  I.carrier.filter (fun m => IsMaximalIn I m)

def IsPure {r : ℕ} (I : OrderIdeal r) : Prop :=
  ∀ m n, m ∈ maximalMonomials I → n ∈ maximalMonomials I → totalDeg m = totalDeg n

structure PureOrderIdeal (r : ℕ) where
  ideal : OrderIdeal r
  isPure : IsPure ideal
  maximal_nonempty : (maximalMonomials ideal).Nonempty

noncomputable def typePO {r : ℕ} (P : PureOrderIdeal r) : ℕ :=
  (maximalMonomials P.ideal).card

noncomputable def socleDegree {r : ℕ} (P : PureOrderIdeal r) : ℕ :=
  totalDeg (Classical.choose P.maximal_nonempty)

def pureOSequence {r : ℕ} (I : OrderIdeal r) (d : ℕ) : ℕ :=
  (I.carrier.filter fun m => totalDeg m = d).card

def IsLogConcaveUpTo (e : ℕ) (h : ℕ → ℕ) : Prop :=
  ∀ i ∈ Finset.Ioo 0 e, h (i - 1) * h (i + 1) ≤ (h i) ^ 2

def UsesEveryVariable {r : ℕ} (P : PureOrderIdeal r) : Prop :=
  ∀ i : Fin r, ∃ m ∈ P.ideal.carrier, 0 < m i

def UniversalLogConcavity (r t : ℕ) : Prop :=
  ∀ P : PureOrderIdeal r, typePO P = t → UsesEveryVariable P →
    IsLogConcaveUpTo (socleDegree P) (pureOSequence P.ideal)

@[simp] theorem mem_maximalMonomials_iff {r : ℕ} (I : OrderIdeal r) (m : Monomial r) :
    m ∈ maximalMonomials I ↔ IsMaximalIn I m := by
  classical
  rw [maximalMonomials, Finset.mem_filter]
  exact and_iff_right_of_imp (fun h => h.1)

theorem totalDeg_eq_sum_univ {r : ℕ} (m : Monomial r) :
    totalDeg m = ∑ i : Fin r, m i := by
  exact m.sum_fintype _ (by simp)

theorem totalDeg_le_of_le {r : ℕ} {m n : Monomial r} (h : m ≤ n) :
    totalDeg m ≤ totalDeg n := by
  simp only [totalDeg_eq_sum_univ]
  exact Finset.sum_le_sum (fun i _ => h i)

@[simp] theorem totalDeg_eq_zero_iff {r : ℕ} (m : Monomial r) :
    totalDeg m = 0 ↔ m = 0 := by
  constructor
  · intro hm
    ext i
    have hle : m i ≤ totalDeg m := by
      rw [totalDeg_eq_sum_univ]
      exact Finset.single_le_sum (fun j _ => Nat.zero_le (m j)) (Finset.mem_univ i)
    simp only [Finsupp.zero_apply]
    omega
  · rintro rfl
    simp [totalDeg]

theorem totalDeg_add {r : ℕ} (m n : Monomial r) :
    totalDeg (m + n) = totalDeg m + totalDeg n := by
  simp [totalDeg, Finsupp.sum_add_index']

theorem totalDeg_complement {r : ℕ} {m g : Monomial r} (hmg : m ≤ g) :
    totalDeg (g - m) = totalDeg g - totalDeg m := by
  have heq : (g - m) + m = g := by
    ext i
    exact Nat.sub_add_cancel (hmg i)
  have hdeg := congrArg totalDeg heq
  rw [totalDeg_add] at hdeg
  omega

theorem eq_of_le_of_totalDeg_le {r : ℕ} {m n : Monomial r}
    (hmn : m ≤ n) (hdeg : totalDeg n ≤ totalDeg m) : m = n := by
  ext i
  by_contra hne
  have hlt : m i < n i := lt_of_le_of_ne (hmn i) hne
  have hsum : totalDeg m < totalDeg n := by
    simp only [totalDeg_eq_sum_univ]
    exact Finset.sum_lt_sum (fun j _ => hmn j) ⟨i, Finset.mem_univ i, hlt⟩
  exact (not_lt_of_ge hdeg) hsum

theorem exists_le_maximal {r : ℕ} (I : OrderIdeal r) (m : Monomial r)
    (hm : m ∈ I.carrier) : ∃ g ∈ maximalMonomials I, m ≤ g := by
  obtain ⟨g, hmg, hg⟩ := I.carrier.exists_le_maximal hm
  exact ⟨g, (mem_maximalMonomials_iff I g).mpr ⟨hg.1, fun n hn hgn => hg.2 hn hgn⟩,
    hmg⟩

theorem maximal_generated {r e : ℕ} (G : Finset (Monomial r))
    (hdeg : ∀ g ∈ G, totalDeg g = e) :
    maximalMonomials (generatedOrderIdeal G) = G := by
  ext m
  rw [mem_maximalMonomials_iff]
  constructor
  · rintro ⟨hm, hmax⟩
    obtain ⟨g, hg, hmg⟩ := mem_generatedOrderIdeal_iff.mp hm
    have hgm := hmax g (mem_generatedOrderIdeal_iff.mpr ⟨g, hg, le_rfl⟩) hmg
    exact (le_antisymm hmg hgm) ▸ hg
  · intro hm
    refine ⟨mem_generatedOrderIdeal_iff.mpr ⟨m, hm, le_rfl⟩, ?_⟩
    intro n hn hmn
    obtain ⟨g, hg, hng⟩ := mem_generatedOrderIdeal_iff.mp hn
    have hmg : m = g := eq_of_le_of_totalDeg_le (hmn.trans hng)
      (by rw [hdeg m hm, hdeg g hg])
    exact hmg ▸ hng

noncomputable def pureGenerated {r e : ℕ} (G : Finset (Monomial r))
    (hdeg : ∀ g ∈ G, totalDeg g = e) (hne : G.Nonempty) : PureOrderIdeal r where
  ideal := generatedOrderIdeal G
  isPure := by
    intro m n hm hn
    rw [maximal_generated G hdeg] at hm hn
    rw [hdeg m hm, hdeg n hn]
  maximal_nonempty := by rw [maximal_generated G hdeg]; exact hne

@[simp] theorem type_pureGenerated {r e : ℕ} (G : Finset (Monomial r))
    (hdeg : ∀ g ∈ G, totalDeg g = e) (hne : G.Nonempty) :
    typePO (pureGenerated G hdeg hne) = G.card := by
  simp [typePO, pureGenerated, maximal_generated G hdeg]

@[simp] theorem socle_pureGenerated {r e : ℕ} (G : Finset (Monomial r))
    (hdeg : ∀ g ∈ G, totalDeg g = e) (hne : G.Nonempty) :
    socleDegree (pureGenerated G hdeg hne) = e := by
  unfold socleDegree
  apply hdeg
  have hm := Classical.choose_spec (pureGenerated G hdeg hne).maximal_nonempty
  simpa [pureGenerated, maximal_generated G hdeg] using hm

end ResearchMain.PureOSequences
