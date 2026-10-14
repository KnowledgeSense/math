import MainTheorems.PreorderGamma.Macaulay.BallotSets

namespace ResearchMain.PreorderGamma.Macaulay

variable {V : Type*} [DecidableEq V]

theorem prefix_insert (index : V → ℕ) (U : Finset V) (v : V) (m : ℕ) :
    ballotPrefix index (insert v U) m =
      if index v < m then insert v (ballotPrefix index U m) else ballotPrefix index U m := by
  simp only [ballotPrefix, Finset.filter_insert]

theorem ballot_ground_insert_iff {index : V → ℕ} {U A : Finset V} {v : V}
    (hmax : ∀ u ∈ U, index u < index v) (hAU : A ⊆ U) :
    IsBallotWithin index (insert v U) A ↔ IsBallotWithin index U A := by
  constructor
  · intro hb
    refine ⟨hAU, fun m => ?_⟩
    by_cases hm : index v < m
    · have hu : ballotPrefix index U (index v) = U := prefix_eq_self hmax
      have ha : ballotPrefix index A (index v) = A := prefix_eq_self fun a ha => hmax a (hAU ha)
      have h := hb.2 (index v)
      rw [prefix_insert, ite_eq_right (lt_irrefl _), hu, ha] at h
      rw [prefix_eq_self (fun a ha => (hmax a (hAU ha)).trans hm),
        prefix_eq_self (fun u hu => (hmax u hu).trans hm)]
      exact h
    · have h := hb.2 m
      rwa [prefix_insert, ite_eq_right hm] at h
  · exact fun hb => hb.enlarge (Finset.subset_insert _ _)

theorem ballot_insert_iff {index : V → ℕ} {U A : Finset V} {v : V}
    (hmax : ∀ u ∈ U, index u < index v) (hAU : A ⊆ U) (hv : v ∉ U) :
    IsBallotWithin index (insert v U) (insert v A) ↔
      IsBallotWithin index U A ∧ 2 * (A.card + 1) ≤ U.card + 1 := by
  have hvA : v ∉ A := fun h => hv (hAU h)
  constructor
  · intro hb
    refine ⟨(ballot_ground_insert_iff hmax hAU).mp
      (hb.subset (Finset.subset_insert _ _)), ?_⟩
    simpa only [Finset.card_insert_of_notMem hv, Finset.card_insert_of_notMem hvA] using hb.card_bound
  · rintro ⟨hb, hc⟩
    refine ⟨Finset.insert_subset_insert v hAU, fun m => ?_⟩
    by_cases hm : index v < m
    · have hu : ballotPrefix index U m = U := prefix_eq_self fun u hu => (hmax u hu).trans hm
      have ha : ballotPrefix index A m = A :=
        prefix_eq_self fun a ha => (hmax a (hAU ha)).trans hm
      simpa only [prefix_insert, ite_eq_left hm, hu, ha,
        Finset.card_insert_of_notMem hv, Finset.card_insert_of_notMem hvA] using hc
    · simpa only [prefix_insert, ite_eq_right hm] using hb.2 m

theorem ballotSets_succ_insert {index : V → ℕ} {U : Finset V} {v : V}
    (hmax : ∀ u ∈ U, index u < index v) (hv : v ∉ U) (r : ℕ) :
    ballotSets index (insert v U) (r + 1) = ballotSets index U (r + 1) ∪
      if 2 * (r + 1) ≤ U.card + 1 then (ballotSets index U r).image (insert v) else ∅ := by
  classical
  ext A
  constructor
  · intro ha
    obtain ⟨hb, hc⟩ := mem_ballotSets.mp ha
    by_cases hvA : v ∈ A
    · have hAU : A.erase v ⊆ U := by
        intro a ha
        obtain ⟨hav, haA⟩ := Finset.mem_erase.mp ha
        exact (Finset.mem_insert.mp (hb.1 haA)).resolve_left hav
      have hball : IsBallotWithin index U (A.erase v) ∧
          2 * ((A.erase v).card + 1) ≤ U.card + 1 :=
        (ballot_insert_iff hmax hAU hv).mp (by simpa only [Finset.insert_erase hvA] using hb)
      have herase : (A.erase v).card = r := by
        have h := Finset.card_erase_add_one hvA
        omega
      have hcap : 2 * (r + 1) ≤ U.card + 1 := by simpa only [herase] using hball.2
      apply Finset.mem_union_right
      rw [ite_eq_left hcap]
      exact Finset.mem_image.mpr
        ⟨A.erase v, mem_ballotSets.mpr ⟨hball.1, herase⟩, Finset.insert_erase hvA⟩
    · have hAU : A ⊆ U := by
        intro a ha
        exact (Finset.mem_insert.mp (hb.1 ha)).resolve_left (fun hav => hvA (hav ▸ ha))
      apply Finset.mem_union_left
      exact mem_ballotSets.mpr ⟨(ballot_ground_insert_iff hmax hAU).mp hb, hc⟩
  · intro ha
    rcases Finset.mem_union.mp ha with ha | ha
    · obtain ⟨hb, hc⟩ := mem_ballotSets.mp ha
      exact mem_ballotSets.mpr ⟨(ballot_ground_insert_iff hmax hb.1).mpr hb, hc⟩
    · by_cases hcap : 2 * (r + 1) ≤ U.card + 1
      · rw [ite_eq_left hcap] at ha
        obtain ⟨B, hb, rfl⟩ := Finset.mem_image.mp ha
        obtain ⟨hb, hc⟩ := mem_ballotSets.mp hb
        have hvB : v ∉ B := fun h => hv (hb.1 h)
        exact mem_ballotSets.mpr
          ⟨(ballot_insert_iff hmax hb.1 hv).mpr ⟨hb, by simpa only [hc] using hcap⟩,
            by rw [Finset.card_insert_of_notMem hvB, hc]⟩
      · simp only [ite_eq_right hcap, Finset.notMem_empty] at ha

theorem ballotSets_succ_insert_card {index : V → ℕ} {U : Finset V} {v : V}
    (hmax : ∀ u ∈ U, index u < index v) (hv : v ∉ U) (r : ℕ) :
    (ballotSets index (insert v U) (r + 1)).card = (ballotSets index U (r + 1)).card +
      if 2 * (r + 1) ≤ U.card + 1 then (ballotSets index U r).card else 0 := by
  classical
  rw [ballotSets_succ_insert hmax hv]
  by_cases hcap : 2 * (r + 1) ≤ U.card + 1
  · rw [ite_eq_left hcap, ite_eq_left hcap]
    have hd : Disjoint (ballotSets index U (r + 1)) ((ballotSets index U r).image (insert v)) := by
      apply Finset.disjoint_left.mpr
      intro A ha hA
      obtain ⟨B, _, rfl⟩ := Finset.mem_image.mp hA
      exact hv ((mem_ballotSets.mp ha).1.1 (Finset.mem_insert_self _ _))
    rw [Finset.card_union_of_disjoint hd]
    congr 1
    apply Finset.card_image_of_injOn
    intro A ha B hb he
    have hvA : v ∉ A := fun h => hv ((mem_ballotSets.mp ha).1.1 h)
    have hvB : v ∉ B := fun h => hv ((mem_ballotSets.mp hb).1.1 h)
    have h := congrArg (fun F => F.erase v) he
    simpa only [Finset.erase_insert hvA, Finset.erase_insert hvB] using h
  · simp only [ite_eq_right hcap, Finset.union_empty, Nat.add_zero]

end ResearchMain.PreorderGamma.Macaulay
