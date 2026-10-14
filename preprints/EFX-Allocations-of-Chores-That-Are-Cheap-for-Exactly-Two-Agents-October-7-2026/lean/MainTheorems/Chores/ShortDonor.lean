import MainTheorems.Chores.PairReversal

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace ExchangeData

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ f : E → A} {a b k : A} {q : ℕ}

theorem short_donor_efx (B : ExchangeData M S f a k)
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hb : b ∈ S) (hunique : UniqueBad M S f a b) (hkb : k ≠ b)
    (hL : expensiveCount M f b b + 2 = q)
    (hsizeK : (bundle f k).card = q) (hcheapK : cheapCount M f k k = 1)
    (hpK : Pure M f k a) {r : ℝ} (hr : 2 < r) : EFX M r B.allocation := by
  let g := B.allocation
  let L := expensiveCount M f b b
  have hsep : Separated M S g := (B.feasible hf.1).1
  have hs' : ∀ c, q ≤ (bundle g c).card ∧ (bundle g c).card ≤ q + 1 := B.balanced hs
  have hpA := optimal_bad_source_pure M hf hs B.source_mem hb hunique.1
  have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs B.source_mem hb hunique.1).1
  have hEk : expensiveCount M f k k + 1 = q := by
    have ht := cheap_add_expensive M f k k
    rw [hsizeK, hcheapK] at ht
    omega
  have hnewA : expensiveCount M g a a = L := by
    have ht := B.source_own_expensive
    change expensiveCount M g a a + 1 = expensiveCount M f a a at ht
    omega
  have hnewK : expensiveCount M g k k = q := by
    have ht := B.target_own_expensive
    change expensiveCount M g k k = expensiveCount M f k k + 1 at ht
    omega
  have hnewKcheap : cheapCount M g k k = 0 := by
    have ht := B.target_cheap_count
    change cheapCount M g k k + 1 = cheapCount M f k k at ht
    omega
  have hnewKsize : (bundle g k).card = q := by rw [B.card, hsizeK]
  have hq : 0 < q := by omega
  have hthK : threshold M r g k = r * ((q : ℝ) - 1) := by
    rw [threshold_eq_counts M r g k
      (by rw [← Finset.card_pos, hnewKsize]; exact hq), hnewKcheap,
      ite_eq_right (Nat.lt_irrefl 0), hnewKsize]
  have hownA : OwnCheap M g a := by
    refine ⟨B.secondChore, ?_, B.sourceCheap⟩
    rw [B.source_bundle]
    exact Finset.mem_insert_self _ _
  have hownK : OwnCheap M f k := by rw [ownCheap_iff_count, hcheapK]; omega
  have hOtherE {v c : A} (hca : c ≠ a) (hck : c ≠ k) :
      expensiveCount M g v c = expensiveCount M f v c := B.other_expensive v hca hck
  have hOutsideE {v : A} (hvS : v ∈ S) (hva : v ≠ a) (hvk : v ≠ k) (c : A) :
      expensiveCount M g v c = expensiveCount M f v c := by
    have hd : ¬M.Cheap v B.secondChore :=
      two_cheap_third M B.distinct B.sourceCheap B.targetCheap hva hvk
    by_cases hca : c = a
    · subst c
      have ht := exchange_expensive_left M f B.chore_distinct B.owner_distinct v
      rw [B.firstOwner, ite_eq_right (filler_not_cheap M hvS B.filler), ite_eq_right hd] at ht
      change (expensiveCount M g v a : ℤ) = (expensiveCount M f v a : ℤ) - 1 + 1 at ht
      omega
    · by_cases hck : c = k
      · subst c
        have ht := exchange_expensive_right M f B.chore_distinct B.owner_distinct v
        rw [B.secondOwner, ite_eq_right (filler_not_cheap M hvS B.filler), ite_eq_right hd] at ht
        change (expensiveCount M g v k : ℤ) = (expensiveCount M f v k : ℤ) - 1 + 1 at ht
        omega
      · exact hOtherE hca hck
  have hr1 : 1 ≤ r := by linarith
  rw [efx_iff_threshold M hr]
  intro v c hvc
  by_cases hva : v = a
  · subst v
    apply positive_comparison M hr1 hownA
    · have h₁ := (hs' a).2
      have h₂ := (hs' c).1
      omega
    · rw [hnewA]
      by_cases hck : c = k
      · subst c
        have ht := B.source_sees_target
        rw [pure_observer_expensive M hf.1.1 B.source_mem hpK] at ht
        change expensiveCount M g a k = expensiveCount M f k k + 1 at ht
        omega
      · rw [hOtherE hvc.symm hck]
        by_cases hcb : c = b
        · subst c
          rw [pure_observer_expensive M hf.1.1 B.source_mem
            (minimum_bad_target_pure M (hf.energyMinimum M) hs B.source_mem hb hunique.1)]
        · by_cases hcS : c ∈ S
          · have ht := optimal_pair_high_margin M hf hs B.source_mem hb hcS hunique.1 hvc.symm hcb
            omega
          · rw [separated_outside_target_expensive M hf.1.1 B.source_mem hcS]
            have ht := (hs c).1
            omega
  · by_cases hvk : v = k
    · subst v
      rw [hthK, bundleCost_eq_size]
      have hsize' : (q : ℝ) ≤ (bundle g c).card := by exact_mod_cast (hs' c).1
      have hE : q ≤ expensiveCount M g k c + 1 := by
        by_cases hca : c = a
        · subst c
          have ht := B.target_sees_source
          rw [pure_outside_expensive M hf.1.1 hunique.1.1 hpA B.target_mem B.distinct.symm hkb] at ht
          change expensiveCount M g k a + 1 = (bundle f a).card at ht
          have ht' := (hs a).1
          omega
        · rw [hOtherE hca hvc.symm]
          have ht : expensiveCount M f k k ≤ expensiveCount M f k c := by
            by_contra ht
            have hbad : Bad M f k c := ⟨hvc, hownK, by omega⟩
            by_cases hcS : c ∈ S
            · exact B.distinct.symm (hunique.2 k B.target_mem c hcS hbad).1
            · have he := separated_outside_target_expensive M hf.1.1 B.target_mem hcS
              have hsize := (hs c).1
              omega
          omega
      have hE' : (q : ℝ) ≤ expensiveCount M g k c + 1 := by exact_mod_cast hE
      nlinarith
    · have ht : threshold M r g v = threshold M r f v := by
        apply threshold_eq_of_counts M r (B.card v)
        exact hOtherE hva hvk
      rw [ht]
      by_cases hvS : v ∈ S
      · rw [cost_eq_of_counts M r (B.card c) (hOutsideE hvS hva hvk c)]
        apply separated_comparison M hr (hf.energyMinimum M) hs hvc
        intro hvS' hcS hbad
        exact hva (hunique.2 v hvS' c hcS hbad).1
      · have ht' := separated_outside_threshold M hf.1.1 r hs hvS
        have hcost := cost_ge_size M hr1 g v c
        have hsize' : (q : ℝ) ≤ (bundle g c).card := by exact_mod_cast (hs' c).1
        linarith

end ExchangeData

end ResearchMain.Chores
