import MainTheorems.Chores.NeutralHandoff
import MainTheorems.Chores.RotatingPairs
import MainTheorems.Chores.SpecialPair

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace ExchangeData

variable {M : TwoCheapModel A E} {S : Finset A} {f₀ f : E → A} {a b k : A} {q : ℕ}

theorem neutral_final_exchange (B : ExchangeData M S f a k)
    (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (hb : b ∈ S) (hunique : UniqueBad M S f a b) (hkb : k ≠ b)
    (hk : expensiveCount M f k k = expensiveCount M f b b)
    (hL : expensiveCount M f b b + 2 ≤ q) {r : ℝ} (hr : 2 < r)
    {w : A} (hw : w ∈ S) (hbad : Bad M B.allocation k w) :
    ∃ g : E → A, EFX M r g := by
  obtain ⟨hunique', hf', hwa, hwb⟩ := B.neutral_pure_pair hf hs hb hunique hkb hk hw hbad
  let h := B.allocation
  let L := expensiveCount M f b b
  change Optimal M S f₀ h at hf'
  change UniqueBad M S h k w at hunique'
  have hab := hunique.1.1
  have hkw := hbad.1
  have hs' : ∀ c, q ≤ (bundle h c).card ∧ (bundle h c).card ≤ q + 1 := B.balanced hs
  have hpA := optimal_bad_source_pure M hf hs B.source_mem hb hunique.1
  have hpB : Pure M h b a := by
    change Pure M B.allocation b a
    simpa only [Pure, B.other_bundle hab.symm hkb.symm] using
      minimum_bad_target_pure M (hf.energyMinimum M) hs B.source_mem hb hunique.1
  have hpK := optimal_bad_source_pure M hf' hs' B.target_mem hw hbad
  have hpW := minimum_bad_target_pure M (hf'.energyMinimum M) hs' B.target_mem hw hbad
  have hcounts := (minimum_bad_counts M (hf.energyMinimum M) hs B.source_mem hb hunique.1).1
  have hcounts' := (minimum_bad_counts M (hf'.energyMinimum M) hs' B.target_mem hw hbad).1
  have hEa : expensiveCount M h a a = L := by
    have h₁ := B.source_own_expensive
    change expensiveCount M h a a + 1 = expensiveCount M f a a at h₁
    omega
  have hEb : expensiveCount M h b b = L := by
    exact B.other_expensive b hab.symm hkb.symm
  have hEk : expensiveCount M h k k = L + 1 := by
    simpa only [hk] using B.target_own_expensive
  have hEw : expensiveCount M h w w = L := by omega
  obtain ⟨d, hd, hdb⟩ := bad_target_ownCheap M hf.1.1 hs B.source_mem hunique.1
  have hd' : d ∈ bundle h b := by
    rw [B.other_bundle hab.symm hkb.symm]
    exact hd
  have hda := hpB d hd' hdb
  obtain ⟨e, he, hew⟩ := bad_target_ownCheap M hf'.1.1 hs' B.target_mem hbad
  have hek := hpW e he hew
  have hdq : h d = b := (mem_bundle h b d).mp hd'
  have heq : h e = w := (mem_bundle h w e).mp he
  have hdne : d ≠ e := by intro ht; exact hwb (heq.symm.trans ((congrArg h ht.symm).trans hdq))
  have howners : h d ≠ h e := by simpa only [hdq, heq] using hwb.symm
  let g := exchange h d e
  have hbBundle : bundle g b = insert e ((bundle h b).erase d) := by
    simpa only [hdq] using exchange_bundle_left h hdne howners
  have hwBundle : bundle g w = insert d ((bundle h w).erase e) := by
    simpa only [heq] using exchange_bundle_right h hdne howners
  have hother {v : A} (hvb : v ≠ b) (hvw : v ≠ w) : bundle g v = bundle h v := by
    apply exchange_bundle_other
    · simpa only [hdq] using hvb
    · simpa only [heq] using hvw
  have hsize (v : A) : (bundle g v).card = (bundle h v).card := exchange_bundle_card h d e v
  have hbE (v : A) : expensiveCount M g v b + (if M.Cheap v d then 0 else 1) =
      expensiveCount M h v b + (if M.Cheap v e then 0 else 1) := by
    apply replacement_expensive M hd'
    · intro ht
      exact hwb (heq.symm.trans ((mem_bundle h b e).mp ht))
    · exact hbBundle
  have hwE (v : A) : expensiveCount M g v w + (if M.Cheap v e then 0 else 1) =
      expensiveCount M h v w + (if M.Cheap v d then 0 else 1) := by
    apply replacement_expensive M he
    · intro ht
      exact hwb ((mem_bundle h w d).mp ht |>.symm.trans hdq)
    · exact hwBundle
  have hdOutside {v : A} (hva : v ≠ a) (hvb : v ≠ b) : ¬M.Cheap v d :=
    two_cheap_third M hab hda hdb hva hvb
  have heOutside {v : A} (hvk : v ≠ k) (hvw : v ≠ w) : ¬M.Cheap v e :=
    two_cheap_third M hkw hek hew hvk hvw
  have hotherE {v c : A} (hcb : c ≠ b) (hcw : c ≠ w) :
      expensiveCount M g v c = expensiveCount M h v c := by
    rw [expensiveCount, hother hcb hcw]
    rfl
  have hownE {v : A} (hv : v = a ∨ v = b ∨ v = k ∨ v = w) :
      expensiveCount M g v v ≤ L + 1 := by
    rcases hv with ht | ht | ht | ht <;> subst v
    · rw [hotherE hab hwa.symm, hEa]
      omega
    · have ht := hbE b
      rw [ite_eq_left hdb, ite_eq_right (heOutside hkb.symm hwb.symm), add_zero, hEb] at ht
      omega
    · rw [hotherE hkb hkw, hEk]
    · have ht := hwE w
      rw [ite_eq_left hew, ite_eq_right (hdOutside hwa hwb), add_zero, hEw] at ht
      omega
  have hown {v : A} (hv : v = a ∨ v = b ∨ v = k ∨ v = w) : OwnCheap M g v := by
    rcases hv with ht | ht | ht | ht <;> subst v
    · rw [OwnCheap, hother hab hwa.symm]
      obtain ⟨x, hx, _, _, hcheap, _⟩ := B.source_mixed
        (B.neutral_nonpure hf hs hb hunique.1 hkb)
      exact ⟨x, hx, hcheap⟩
    · have htwo := optimal_bad_target_two_cheap M hf hs B.source_mem hb hunique.1
      have hcheapEq : cheapCount M h b b = cheapCount M f b b := by
        rw [cheapCount, B.other_bundle hab.symm hkb.symm]
        rfl
      have hsum := cheap_add_expensive M g b b
      have hsum' := cheap_add_expensive M h b b
      have hexp := hbE b
      rw [ite_eq_left hdb, ite_eq_right (heOutside hkb.symm hwb.symm), add_zero] at hexp
      rw [hsize] at hsum
      rw [ownCheap_iff_count]
      omega
    · rw [OwnCheap, hother hkb hkw]
      exact hbad.2.1
    · have htwo := optimal_bad_target_two_cheap M hf' hs' B.target_mem hw hbad
      have hsum := cheap_add_expensive M g w w
      have hsum' := cheap_add_expensive M h w w
      have hexp := hwE w
      rw [ite_eq_left hew, ite_eq_right (hdOutside hwa hwb), add_zero] at hexp
      rw [hsize] at hsum
      rw [ownCheap_iff_count]
      omega
  have hthreshold {v : A} (hv : v = a ∨ v = b ∨ v = k ∨ v = w) :
      threshold M r g v ≤ r * ((q : ℝ) - 1) + 1 := by
    rw [positive_threshold M r (hown hv)]
    have hsize' : ((bundle g v).card : ℝ) ≤ q + 1 := by rw [hsize]; exact_mod_cast (hs' v).2
    have hE : (expensiveCount M g v v : ℝ) ≤ L + 1 := by exact_mod_cast hownE hv
    have hL' : (L : ℝ) + 2 ≤ q := by exact_mod_cast hL
    nlinarith
  have hpair {v c : A} (hv : (v = a ∧ c = b) ∨ (v = b ∧ c = a) ∨
      (v = k ∧ c = w) ∨ (v = w ∧ c = k)) :
      expensiveCount M g v v ≤ expensiveCount M g v c := by
    rcases hv with ⟨hv, hc⟩ | ⟨hv, hc⟩ | ⟨hv, hc⟩ | ⟨hv, hc⟩ <;> subst v <;> subst c
    · rw [hotherE hab hwa.symm, hEa]
      have ht := hbE a
      rw [ite_eq_left hda, ite_eq_right (heOutside B.distinct hwa.symm), add_zero,
        pure_observer_expensive M hf'.1.1 B.source_mem hpB, hEb] at ht
      omega
    · have htarget : expensiveCount M h b a = L + 1 := by
        have ht := exchange_expensive_left M f B.chore_distinct B.owner_distinct b
        rw [B.firstOwner, ite_eq_right (filler_not_cheap M hb B.filler),
          ite_eq_right (two_cheap_third M B.distinct B.sourceCheap B.targetCheap hab.symm hkb.symm),
          pure_observer_expensive M hf.1.1 hb hpA, hcounts] at ht
        change (expensiveCount M h b a : ℤ) = (L : ℤ) + 1 - 1 + 1 at ht
        omega
      rw [hotherE hab hwa.symm, htarget]
      exact hownE (Or.inr (Or.inl rfl))
    · rw [hotherE hkb hkw, hEk]
      have ht := hwE k
      rw [ite_eq_left hek, ite_eq_right (hdOutside B.distinct.symm hkb), add_zero,
        pure_observer_expensive M hf'.1.1 B.target_mem hpW, hEw] at ht
      omega
    · rw [hotherE hkb hkw, pure_observer_expensive M hf'.1.1 hw hpK, hEk]
      exact hownE (Or.inr (Or.inr (Or.inr rfl)))
  have hcross {v c : A}
      (hv : (v = a ∨ v = b) ∧ (c = k ∨ c = w) ∨
        (v = k ∨ v = w) ∧ (c = a ∨ c = b)) :
      (bundle g c).card ≤ expensiveCount M g v c + 1 := by
    rcases hv with ⟨hv, hc⟩ | ⟨hv, hc⟩
    · have hvS : v ∈ S := hv.elim (fun ht => ht ▸ B.source_mem) (fun ht => ht ▸ hb)
      have hvk : v ≠ k := by rcases hv with ht | ht <;> subst v; exact B.distinct; exact hkb.symm
      have hvw : v ≠ w := by rcases hv with ht | ht <;> subst v; exact hwa.symm; exact hwb.symm
      rcases hc with ht | ht <;> subst c
      · rw [hsize, hotherE hkb hkw, pure_outside_expensive M hf'.1.1 hkw hpK hvS hvk hvw]
        omega
      · have ht := hwE v
        rw [ite_eq_right (heOutside hvk hvw),
          pure_outside_expensive M hf'.1.1 hkw.symm hpW hvS hvw hvk] at ht
        rw [hsize]
        split_ifs at ht <;> omega
    · have hvS : v ∈ S := hv.elim (fun ht => ht ▸ B.target_mem) (fun ht => ht ▸ hw)
      have hva : v ≠ a := by rcases hv with ht | ht <;> subst v; exact B.distinct.symm; exact hwa
      have hvb : v ≠ b := by rcases hv with ht | ht <;> subst v; exact hkb; exact hwb
      rcases hc with ht | ht <;> subst c
      · have ht := exchange_expensive_left M f B.chore_distinct B.owner_distinct v
        rw [B.firstOwner, ite_eq_right (filler_not_cheap M hvS B.filler),
          pure_outside_expensive M hf.1.1 hab hpA hvS hva hvb] at ht
        have hn : (0 : ℤ) ≤ (if M.Cheap v B.secondChore then 0 else 1) := by split_ifs <;> norm_num
        rw [hsize, hotherE hab hwa.symm, B.card]
        change (expensiveCount M h v a : ℤ) = ((bundle f a).card : ℤ) - 1 +
          (if M.Cheap v B.secondChore then 0 else 1) at ht
        omega
      · have ht := hbE v
        rw [ite_eq_right (hdOutside hva hvb),
          pure_outside_expensive M hf'.1.1 hab.symm hpB hvS hvb hva] at ht
        rw [hsize]
        split_ifs at ht <;> omega
  refine ⟨g, ?_⟩
  rw [efx_iff_threshold M hr]
  intro v c hvc
  have hr1 : 1 ≤ r := by linarith
  by_cases hv : v = a ∨ v = b ∨ v = k ∨ v = w
  · by_cases hc : c = a ∨ c = b ∨ c = k ∨ c = w
    · by_cases hpartner : (v = a ∧ c = b) ∨ (v = b ∧ c = a) ∨
        (v = k ∧ c = w) ∨ (v = w ∧ c = k)
      · apply positive_comparison M hr1 (hown hv)
        · rw [hsize, hsize]
          have h₁ := (hs' v).2
          have h₂ := (hs' c).1
          omega
        · exact hpair hpartner
      · have hcross' : (v = a ∨ v = b) ∧ (c = k ∨ c = w) ∨
            (v = k ∨ v = w) ∧ (c = a ∨ c = b) := by aesop
        have hE' : ((bundle g c).card : ℝ) ≤ expensiveCount M g v c + 1 := by
          exact_mod_cast hcross hcross'
        have hsize' : (q : ℝ) ≤ (bundle g c).card := by rw [hsize]; exact_mod_cast (hs' c).1
        rw [bundleCost_eq_size]
        have ht := hthreshold hv
        nlinarith
    · have hca : c ≠ a := fun ht => hc (Or.inl ht)
      have hcb : c ≠ b := fun ht => hc (Or.inr (Or.inl ht))
      have hck : c ≠ k := fun ht => hc (Or.inr (Or.inr (Or.inl ht)))
      have hcw : c ≠ w := fun ht => hc (Or.inr (Or.inr (Or.inr ht)))
      apply positive_comparison M hr1 (hown hv)
      · rw [hsize, hsize]
        have h₁ := (hs' v).2
        have h₂ := (hs' c).1
        omega
      · rw [hotherE hcb hcw]
        have hbound : L + 1 ≤ expensiveCount M h v c := by
          by_cases hcS : c ∈ S
          · rcases hv with ht | ht | ht | ht <;> subst v
            · rw [B.other_expensive a hca hck]
              exact optimal_pair_high_margin M hf hs B.source_mem hb hcS hunique.1 hca hcb
            · rw [B.other_expensive b hca hck]
              exact optimal_pair_low_margin M hf hs B.source_mem hb hcS hunique.1 hca hcb
            · have ht := optimal_pair_high_margin M hf' hs' B.target_mem hw hcS hbad hck hcw
              rwa [hEw] at ht
            · have ht := optimal_pair_low_margin M hf' hs' B.target_mem hw hcS hbad hck hcw
              rwa [hEw] at ht
          · have hvS : v ∈ S := by rcases hv with ht | ht | ht | ht <;> subst v; exact B.source_mem; exact hb; exact B.target_mem; exact hw
            rw [separated_outside_target_expensive M hf'.1.1 hvS hcS]
            have hsize' := (hs' c).1
            omega
        exact (hownE hv).trans hbound
  · have hva : v ≠ a := fun ht => hv (Or.inl ht)
    have hvb : v ≠ b := fun ht => hv (Or.inr (Or.inl ht))
    have hvk : v ≠ k := fun ht => hv (Or.inr (Or.inr (Or.inl ht)))
    have hvw : v ≠ w := fun ht => hv (Or.inr (Or.inr (Or.inr ht)))
    have ht : threshold M r g v = threshold M r h v := by
      apply threshold_eq_of_counts M r (hsize v)
      exact hotherE hvb hvw
    rw [ht]
    by_cases hvS : v ∈ S
    · have hE : expensiveCount M g v c = expensiveCount M h v c := by
        by_cases hcb : c = b
        · subst c
          have ht := hbE v
          rw [ite_eq_right (hdOutside hva hvb), ite_eq_right (heOutside hvk hvw)] at ht
          omega
        · by_cases hcw : c = w
          · subst c
            have ht := hwE v
            rw [ite_eq_right (hdOutside hva hvb), ite_eq_right (heOutside hvk hvw)] at ht
            omega
          · exact hotherE hcb hcw
      rw [cost_eq_of_counts M r (hsize c) hE]
      apply separated_comparison M hr (hf'.energyMinimum M) hs' hvc
      intro hvS' hcS hnew
      exact hvk (hunique'.2 v hvS' c hcS hnew).1
    · have ht' := separated_outside_threshold M hf'.1.1 r hs' hvS
      have hcost := cost_ge_size M hr1 g v c
      have hsize' : (q : ℝ) ≤ (bundle g c).card := by rw [hsize]; exact_mod_cast (hs' c).1
      linarith

end ExchangeData

theorem neutral_handoff (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {S : Finset A} {f₀ f : E → A} {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {a b k : A} (ha : a ∈ S) (hb : b ∈ S) (hkS : k ∈ S)
    (hunique : UniqueBad M S f a b) (hka : k ≠ a) (hkb : k ≠ b)
    (hk : expensiveCount M f k k = expensiveCount M f b b)
    (hL : expensiveCount M f b b + 2 ≤ q) {d : E}
    (hd : d ∈ bundle f k) (hda : M.Cheap a d) : ∃ g : E → A, EFX M r g := by
  obtain ⟨e, he, heCheap⟩ := own_expensive_exists M (bad_expensive_positive M hunique.1)
  have heq := (mem_bundle f a e).mp he
  have hdq := (mem_bundle f k d).mp hd
  have hdk : M.Cheap k d := by
    simpa only [hdq] using separated_owner_cheap M hf.1.1 ha hda
  let B : ExchangeData M S f a k :=
    { firstChore := e
      secondChore := d
      firstOwner := heq
      secondOwner := hdq
      source_mem := ha
      target_mem := hkS
      distinct := hka.symm
      filler := separated_expensive_filler M hf.1.1 (by simpa only [heq] using heCheap)
      sourceCheap := hda
      targetCheap := hdk }
  by_cases hmore : ∃ w ∈ S, Bad M B.allocation k w
  · obtain ⟨w, hw, hbad⟩ := hmore
    exact B.neutral_final_exchange hf hs hb hunique hkb hk hL hr hw hbad
  · have hcounts : expensiveCount M f a a = expensiveCount M f k k + 1 := by
      rw [hk]
      exact (minimum_bad_counts M (hf.energyMinimum M) hs ha hb hunique.1).1
    refine ⟨B.allocation, separated_minimum_efx M hr
      (B.minimum_of_counts (hf.energyMinimum M) hcounts) (B.balanced hs) ?_⟩
    intro c hc w hw hnew
    have hck := B.neutral_bad_source hf hs hb hunique hkb hk hc hw hnew
    exact hmore ⟨w, hw, by simpa only [hck] using hnew⟩

end ResearchMain.Chores
