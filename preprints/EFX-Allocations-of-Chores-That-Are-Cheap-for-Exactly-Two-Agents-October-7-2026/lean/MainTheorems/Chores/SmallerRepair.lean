import MainTheorems.Chores.SmallerFrame
import MainTheorems.Chores.InternalBuffer

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

namespace IsolatedSwap

variable {M : TwoCheapModel A E} {S : Finset A} {f : E → A} {a b k : A}

theorem repair_small_pair (B : IsolatedSwap M S f a b k) {f₀ g : E → A} {q : ℕ}
    (hf : Optimal M S f₀ f)
    (hs : ∀ v, q ≤ (bundle f v).card ∧ (bundle f v).card ≤ q + 1)
    (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b)
    (hL : expensiveCount M f b b + 2 ≤ q)
    (hz : ∀ v ∈ B.outside, expensiveCount M f v v = 0)
    (hg : Optimal B.frozenModel B.outside B.allocation g)
    {c w : A} (hc : c ∈ B.outside) (hw : w ∈ B.outside)
    (hunique : UniqueBad B.frozenModel B.outside g c w)
    (hzero : expensiveCount B.frozenModel g w w = 0)
    {r : ℝ} (hr : 2 < r) : ∃ h : E → A, EFX M r h := by
  have hq : 2 ≤ q := by omega
  have C := B.smaller_frame hf hs ha hb hbad hq hz hg.1
  have hUS : B.outside ⊆ S := Finset.sdiff_subset
  have hac : a ≠ c := by intro ht; exact (Finset.mem_sdiff.mp hc).2 (by simp [← ht])
  have haw : a ≠ w := by intro ht; exact (Finset.mem_sdiff.mp hw).2 (by simp [← ht])
  have hbw : b ≠ w := by intro ht; exact (Finset.mem_sdiff.mp hw).2 (by simp [← ht])
  have hga : bundle g a = bundle f a := by
    rw [B.feasible_pair_bundle hg.1 (Or.inl rfl), B.other_bundle B.donor_high.symm B.pair_distinct]
  obtain ⟨e, he, heCheap⟩ := own_expensive_exists M (bad_expensive_positive M hbad)
  have heq := (mem_bundle f a e).mp he
  have hef : Filler M S e := separated_expensive_filler M hf.1.1 (by rwa [heq])
  have heG : g e = a := by
    apply (mem_bundle g a e).mp
    rw [hga]
    exact he
  obtain ⟨d, hd, hdCheap⟩ := bad_target_ownCheap B.frozenModel hg.1.1 C.size hc hunique.1
  have hdHigh := minimum_bad_target_pure B.frozenModel (hg.energyMinimum B.frozenModel)
    C.size hc hw hunique.1 d hd hdCheap
  have hdq := (mem_bundle g w d).mp hd
  have hdInitial : B.allocation d ∈ B.outside := feasible_original_inside B.frozenModel hg.1 (by rwa [hdq])
  have hdOriginal (v : A) : B.frozenModel.Cheap v d ↔ M.Cheap v d :=
    frozen_cheap_inside M B.outside B.allocation a b B.pair_distinct hdInitial v
  let F : ForeignExchange M S g c w a :=
    { firstChore := e
      secondChore := d
      firstOwner := heG
      secondOwner := hdq
      high_mem := hUS hc
      low_mem := hUS hw
      donor_mem := ha
      pair_distinct := hunique.1.1
      donor_high := hac
      donor_low := haw
      filler := hef
      highCheap := (hdOriginal c).mp hdHigh
      lowCheap := (hdOriginal w).mp hdCheap }
  have hcountEq (v : A) (hv : v ∈ B.outside) (u : A) (hu : u ∈ B.outside) :
      expensiveCount B.frozenModel g v u = expensiveCount M g v u :=
    frozen_expensive_eq M B.outside B.allocation a b B.pair_distinct hg.1 hu v
  have hone (v : A) (hv : v ∈ B.outside) : expensiveCount B.frozenModel g v v ≤ 1 := by
    rw [hcountEq v hv v hv]
    exact (C.own v hv).1
  have haU : a ∉ B.outside := by simp [outside]
  obtain ⟨hinternal, hown⟩ := F.internal_one_filler B.frozenModel hg C.size hq hUS hc hw haU
    hunique hzero hone hcountEq hr
  have hpairOutside {v : A} (hv : v = a ∨ v = b) : v ≠ c ∧ v ≠ w := by
    rcases hv with hv | hv <;> subst v
    · exact ⟨hac, haw⟩
    · refine ⟨?_, hbw⟩
      intro ht
      exact (Finset.mem_sdiff.mp hc).2 (by simp [← ht])
  have hvS {v : A} (hv : v = a ∨ v = b) : v ∈ S :=
    hv.elim (fun ht => ht ▸ ha) (fun ht => ht ▸ hb)
  have hpairE {v : A} (hv : v = a ∨ v = b) (u : A) :
      expensiveCount M F.allocation v u = expensiveCount M g v u :=
    F.outsider_expensive (hvS hv) (hpairOutside hv).1 (hpairOutside hv).2 u
  have hpair : OrdinaryStats M f F.allocation a b := C.pair.of_counts
    (fun v _ => F.card v) (fun v u hv _ => hpairE hv u)
  have hsize (v : A) : q ≤ (bundle F.allocation v).card ∧ (bundle F.allocation v).card ≤ q + 1 := by
    rw [F.card]
    exact C.size v
  refine ⟨F.allocation, isolated_frame_efx M hr hq hsize (fun v => (hs v).2) hpair hL hown
    hinternal ?_ ?_ ?_ ?_⟩
  · intro v u hv hu
    rw [F.card, hpairE hv u]
    exact C.pair_bound v u hv hu
  · intro v hv u hu
    rcases hu with hu | hu <;> subst u
    · have ht := F.source_count (hUS hv)
      have hwhole := C.high_whole v hv
      change expensiveCount M F.allocation v a + (if M.Cheap v d then 1 else 0) =
        expensiveCount M g v a at ht
      rw [hwhole] at ht
      rw [F.card]
      split_ifs at ht <;> omega
    · rw [F.card, F.other_expensive v B.pair_distinct.symm hbw]
      exact C.low_bound v hv
  · intro v hv x hx
    have hva : v ≠ a := by intro ht; subst v; exact hv ha
    have hvw : v ≠ w := by intro ht; subst v; exact hv (hUS hw)
    rw [F.other_bundle hva hvw] at hx
    exact C.outside_cheap v hv x hx
  · intro v hv u hu
    have hua : u ≠ a := by intro ht; subst u; exact hu ha
    have huw : u ≠ w := by intro ht; subst u; exact hu (hUS hw)
    rw [F.card, F.other_expensive v hua huw]
    exact C.to_outside v hv u hu

end IsolatedSwap

end ResearchMain.Chores
