import MainTheorems.Chores.BalancedSplit

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

noncomputable def splitAllocation (f : E → A) (a b : A) (D F : Finset E) : E → A :=
  reassign f (bundle f a) (fun e => if e ∈ splitFirst D F then a else b)

theorem splitAllocation_high {f : E → A} {a b : A} (hab : a ≠ b) {D F : Finset E}
    (hB : bundle f a = D ∪ F) :
    bundle (splitAllocation f a b D F) a = splitFirst D F := by
  have hs : splitFirst D F ⊆ bundle f a := by rw [hB]; exact splitFirst_subset D F
  ext e
  rw [mem_bundle]
  by_cases he : e ∈ splitFirst D F
  · simp [splitAllocation, reassign, he, hs he]
  · by_cases hown : e ∈ bundle f a
    · simp [splitAllocation, reassign, he, hown, hab.symm]
    · have hne : f e ≠ a := by simpa only [mem_bundle] using hown
      simp [splitAllocation, reassign, he, hown, hne]

theorem splitAllocation_low {f : E → A} {a b : A} (hab : a ≠ b) {D F : Finset E}
    (hB : bundle f a = D ∪ F) (hb : bundle f b = ∅) :
    bundle (splitAllocation f a b D F) b = splitSecond D F := by
  have hne (e : E) : f e ≠ b := by
    intro h
    have he := (mem_bundle f b e).mpr h
    rw [hb] at he
    exact Finset.notMem_empty e he
  ext e
  rw [mem_bundle]
  by_cases he : e ∈ bundle f a
  · by_cases hx : e ∈ splitFirst D F
    · simp only [splitAllocation, reassign, ite_eq_left he, ite_eq_left hx]
      simp [splitSecond, hab, hx]
    · simp only [splitAllocation, reassign, ite_eq_left he, ite_eq_right hx]
      simp only [splitSecond, Finset.mem_sdiff, hx, not_false_eq_true, and_true, true_iff]
      rwa [← hB]
  · have hnot : e ∉ D ∪ F := by rwa [← hB]
    simp [splitAllocation, reassign, he, hne e, splitSecond, hnot]

theorem splitAllocation_other {f : E → A} {a b c : A} (hca : c ≠ a) (hcb : c ≠ b)
    (D F : Finset E) : bundle (splitAllocation f a b D F) c = bundle f c := by
  ext e
  simp only [mem_bundle]
  by_cases he : e ∈ bundle f a
  · have hown := (mem_bundle f a e).mp he
    by_cases hx : e ∈ splitFirst D F
    · simp [splitAllocation, reassign, he, hx, hown, hca.symm]
    · simp [splitAllocation, reassign, he, hx, hown, hca.symm, hcb.symm]
  · simp [splitAllocation, reassign, he]

end ResearchMain.Chores
