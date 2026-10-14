import MainTheorems.PreorderGamma.MacaulayNumerical.ColexIntervals

namespace ResearchMain.PreorderGamma.MacaulayNumerical

open Finset.Colex
open scoped FinsetFamily

theorem strictColex_singleton_card {n : ℕ} (a : Fin n) :
    (strictColex ({a} : Finset (Fin n))).card = a.val := by
  have h := strictColex_card_split (s := ({a} : Finset (Fin n)))
    (Finset.mem_singleton_self a) (by intro b hb; exact (Finset.mem_singleton.mp hb).le)
  simpa using h

theorem macaulayRaise_strictColex_max {n d : ℕ} {s : Finset (Fin n)} {a : Fin n}
    (hcard : s.card = d + 1) (ha : a ∈ s) (hmax : ∀ b ∈ s, b ≤ a) :
    macaulayRaise (d + 1) (strictColex s).card =
      (a.val + 1).choose (d + 2) + macaulayRaise d (strictColex (s.erase a)).card := by
  have htop : binomialTop (d + 1) (strictColex s).card = a.val := by
    simpa [hcard] using binomialTop_strictColex ha hmax
  have hsplit := strictColex_card_split ha hmax
  have hrem : (strictColex s).card - a.val.choose (d + 1) =
      (strictColex (s.erase a)).card := by
    rw [hcard] at hsplit
    omega
  rw [macaulayRaise, htop, hrem]

theorem strictColex_successor_le_raise_erase_min {n : ℕ} (s : Finset (Fin n))
    {b : Fin n} (hb : b ∈ s) (hmin : ∀ c ∈ s, b ≤ c) (hsize : 1 < s.card) :
    (strictColex s).card + 1 ≤
      macaulayRaise (s.card - 1) (strictColex (s.erase b)).card := by
  induction s using Finset.strongInductionOn generalizing b with
  | _ s ih =>
      have hs : s.Nonempty := ⟨b, hb⟩
      let a := s.max' hs
      have ha : a ∈ s := Finset.max'_mem s hs
      have hmax : ∀ c ∈ s, c ≤ a := fun c hc => Finset.le_max' s c hc
      have hba : b < a := by
        have hne : b ≠ a := by
          intro heq
          have hsingle : s = {b} := by
            apply Finset.eq_singleton_iff_unique_mem.mpr
            refine ⟨hb, ?_⟩
            intro c hc
            apply le_antisymm
            · simpa [heq] using hmax c hc
            · exact hmin c hc
          simp [hsingle] at hsize
        exact lt_of_le_of_ne (hmax b hb) hne
      let r := s.erase a
      let t := s.erase b
      let q := t.erase a
      have hbr : b ∈ r := Finset.mem_erase.mpr ⟨hba.ne, hb⟩
      have hat : a ∈ t := Finset.mem_erase.mpr ⟨hba.ne', ha⟩
      have hr : r.card = s.card - 1 := Finset.card_erase_of_mem ha
      have ht : t.card = s.card - 1 := Finset.card_erase_of_mem hb
      have hrt : r.card = t.card := hr.trans ht.symm
      have htpos : 0 < t.card := by omega
      have hq : r.erase b = q := by
        dsimp [r, q, t]
        exact Finset.erase_right_comm
      have hsplit : (strictColex s).card =
          a.val.choose s.card + (strictColex r).card := strictColex_card_split ha hmax
      have hraise : macaulayRaise t.card (strictColex t).card =
          (a.val + 1).choose (t.card + 1) +
            macaulayRaise (t.card - 1) (strictColex q).card := by
        have h := macaulayRaise_strictColex_max
          (d := t.card - 1) (s := t) (a := a)
          (by omega) hat (fun c hc => hmax c (Finset.mem_of_mem_erase hc))
        have hdegree : t.card - 1 + 1 = t.card := by omega
        have hsucc : t.card - 1 + 2 = t.card + 1 := by omega
        simpa only [hdegree, hsucc] using h
      have htail : (strictColex r).card + 1 ≤
          a.val.choose t.card + macaulayRaise (t.card - 1) (strictColex q).card := by
        by_cases hrsize : 1 < r.card
        · have h := ih r (Finset.erase_ssubset ha) hbr
            (fun c hc => hmin c (Finset.mem_of_mem_erase hc)) hrsize
          rw [hrt, hq] at h
          exact h.trans (Nat.le_add_left _ _)
        · have hrpos := Finset.card_pos.mpr ⟨b, hbr⟩
          have hrone : r.card = 1 := by omega
          obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hrone
          have hbc : b = c := by simpa [hc] using hbr
          have hrb : r = {b} := by simpa [hbc] using hc
          have htone : t.card = 1 := by omega
          rw [hrb, strictColex_singleton_card, htone, Nat.choose_one_right]
          have hval : b.val < a.val := hba
          omega
      have hcard : t.card + 1 = s.card := by omega
      have hpascal := Nat.choose_succ_succ' a.val t.card
      rw [hcard] at hpascal
      rw [hcard] at hraise
      rw [← ht, hraise]
      omega

theorem initSeg_card_le_macaulayRaise_shadow {n d : ℕ} {s : Finset (Fin n)}
    (hcard : s.card = d + 1) (hd : 0 < d) :
    (initSeg s).card ≤ macaulayRaise d ((∂ (initSeg s)).card - 1) := by
  have hs : s.Nonempty := Finset.card_pos.mp (by omega)
  let b := s.min' hs
  have hb : b ∈ s := Finset.min'_mem s hs
  have hmin : ∀ c ∈ s, b ≤ c := fun c hc => Finset.min'_le s c hc
  have h := strictColex_successor_le_raise_erase_min s hb hmin (by omega)
  have hshadow : ∂ (initSeg s) = initSeg (s.erase b) := shadow_initSeg hs
  rw [hshadow, initSeg_card_eq_rank_add_one, initSeg_card_eq_rank_add_one,
    Nat.add_sub_cancel]
  simpa [hcard] using h

end ResearchMain.PreorderGamma.MacaulayNumerical
