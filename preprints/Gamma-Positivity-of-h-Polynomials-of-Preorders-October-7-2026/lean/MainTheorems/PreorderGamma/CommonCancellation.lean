import MainTheorems.PreorderGamma.Matching

namespace ResearchMain.PreorderGamma

variable {E : Type*} [DecidableEq E] [Preorder E]

def HasOrderMatching (s t : Finset E) : Prop :=
  ∃ f : s ≃ t, ∀ a : s, (a : E) ≤ (f a : E)

omit [DecidableEq E] in
theorem HasOrderMatching.card_eq {s t : Finset E} (h : HasOrderMatching s t) :
    s.card = t.card := by
  obtain ⟨f, hf⟩ := h
  simpa using Fintype.card_congr f

theorem HasOrderMatching.erase_common {s t : Finset E} (h : HasOrderMatching s t)
    {c : E} (hs : c ∈ s) (ht : c ∈ t) :
    HasOrderMatching (s.erase c) (t.erase c) := by
  classical
  obtain ⟨f, hf⟩ := h
  let cs : s := ⟨c, hs⟩
  let ct : t := ⟨c, ht⟩
  let g : s ≃ t := f.trans (Equiv.swap ct (f cs))
  have hgc : g cs = ct := by simp [g]
  have horder : ∀ a : s, (a : E) ≤ (g a : E) := by
    intro a
    by_cases ha : f a = ct
    · have hg : g a = f cs := by simp [g, ha]
      rw [hg]
      have h1 := hf a
      have h2 := hf cs
      rw [ha] at h1
      exact le_trans h1 h2
    · by_cases hac : f a = f cs
      · have heq : a = cs := f.injective hac
        subst a
        rw [hgc]
      · have hg : g a = f a := by
          exact Equiv.swap_apply_of_ne_of_ne ha hac
        rw [hg]
        exact hf a
  let u : s.erase c → t.erase c := fun a =>
    ⟨(g ⟨a.val, (Finset.mem_erase.mp a.property).2⟩).val,
      Finset.mem_erase.mpr ⟨by
        intro heq
        have hg : g ⟨a.val, (Finset.mem_erase.mp a.property).2⟩ = ct :=
          Subtype.ext heq
        have hc : (⟨a.val, (Finset.mem_erase.mp a.property).2⟩ : s) = cs :=
          g.injective (hg.trans hgc.symm)
        exact (Finset.mem_erase.mp a.property).1 (congrArg Subtype.val hc),
        (g ⟨a.val, (Finset.mem_erase.mp a.property).2⟩).property⟩⟩
  have hu : Function.Injective u := by
    intro a b hab
    have hg : g ⟨a.val, (Finset.mem_erase.mp a.property).2⟩ =
        g ⟨b.val, (Finset.mem_erase.mp b.property).2⟩ :=
      Subtype.ext (congrArg (fun q : t.erase c => q.val) hab)
    apply Subtype.ext
    exact congrArg (fun q : s => q.val) (g.injective hg)
  have hcard : Fintype.card (s.erase c) = Fintype.card (t.erase c) := by
    have hst : s.card = t.card := by simpa using Fintype.card_congr f
    simp only [Fintype.card_coe, Finset.card_erase_of_mem hs, Finset.card_erase_of_mem ht]
    omega
  refine ⟨Equiv.ofBijective u ((Fintype.bijective_iff_injective_and_card u).mpr
    ⟨hu, hcard⟩), ?_⟩
  intro a
  exact horder ⟨a.val, (Finset.mem_erase.mp a.property).2⟩

theorem HasOrderMatching.sdiff_common {c s t : Finset E}
    (h : HasOrderMatching s t) (hc : c ⊆ s) (ht : c ⊆ t) :
    HasOrderMatching (s \ c) (t \ c) := by
  induction c using Finset.induction_on generalizing s t with
  | empty => simpa using h
  | @insert a c ha ih =>
    have has : a ∈ s := hc (Finset.mem_insert_self _ _)
    have hat : a ∈ t := ht (Finset.mem_insert_self _ _)
    have hcs : c ⊆ s.erase a := by
      intro b hb
      exact Finset.mem_erase.mpr
        ⟨fun hba => ha (hba ▸ hb), hc (Finset.mem_insert_of_mem hb)⟩
    have hct : c ⊆ t.erase a := by
      intro b hb
      exact Finset.mem_erase.mpr
        ⟨fun hba => ha (hba ▸ hb), ht (Finset.mem_insert_of_mem hb)⟩
    have h' := ih (h.erase_common has hat) hcs hct
    simpa only [Finset.erase_sdiff_comm, Finset.sdiff_insert] using h'

theorem HasOrderMatching.cancel_intersection {s t : Finset E} (h : HasOrderMatching s t) :
    HasOrderMatching (s \ t) (t \ s) := by
  have h' := h.sdiff_common (c := s ∩ t) Finset.inter_subset_left Finset.inter_subset_right
  simpa only [Finset.sdiff_inter_self_left, Finset.sdiff_inter_self_right] using h'

theorem HasOrderMatching.restore_intersection {s t : Finset E}
    (h : HasOrderMatching (s \ t) (t \ s)) : HasOrderMatching s t := by
  obtain ⟨f, hf⟩ := h
  let g : s → t := fun a =>
    if ha : a.val ∈ t then ⟨a.val, ha⟩
    else ⟨(f ⟨a.val, Finset.mem_sdiff.mpr ⟨a.property, ha⟩⟩).val,
      (Finset.mem_sdiff.mp (f ⟨a.val, Finset.mem_sdiff.mpr ⟨a.property, ha⟩⟩).property).1⟩
  have hg : Function.Injective g := by
    intro a b hab
    apply Subtype.ext
    by_cases ha : a.val ∈ t <;> by_cases hb : b.val ∈ t
    · simpa [g, ha, hb] using congrArg Subtype.val hab
    · have heq : a.val = (f ⟨b.val, Finset.mem_sdiff.mpr ⟨b.property, hb⟩⟩).val := by
        simpa [g, ha, hb] using congrArg Subtype.val hab
      have hn := (Finset.mem_sdiff.mp
        (f ⟨b.val, Finset.mem_sdiff.mpr ⟨b.property, hb⟩⟩).property).2
      exact False.elim (hn (heq ▸ a.property))
    · have heq : (f ⟨a.val, Finset.mem_sdiff.mpr ⟨a.property, ha⟩⟩).val = b.val := by
        simpa [g, ha, hb] using congrArg Subtype.val hab
      have hn := (Finset.mem_sdiff.mp
        (f ⟨a.val, Finset.mem_sdiff.mpr ⟨a.property, ha⟩⟩).property).2
      exact False.elim (hn (heq.symm ▸ b.property))
    · have heq : f ⟨a.val, Finset.mem_sdiff.mpr ⟨a.property, ha⟩⟩ =
          f ⟨b.val, Finset.mem_sdiff.mpr ⟨b.property, hb⟩⟩ := by
        apply Subtype.ext
        simpa only [g, dite_eq_right ha, dite_eq_right hb] using
          congrArg (fun q : t => q.val) hab
      exact congrArg (fun q : ↥(s \ t) => q.val) (f.injective heq)
  have hcard : Fintype.card s = Fintype.card t := by
    have hst : (s \ t).card = (t \ s).card := by simpa using Fintype.card_congr f
    have h1 := Finset.card_sdiff_add_card_inter s t
    have h2 := Finset.card_sdiff_add_card_inter t s
    rw [Finset.inter_comm t s] at h2
    simp only [Fintype.card_coe]
    omega
  refine ⟨Equiv.ofBijective g ((Fintype.bijective_iff_injective_and_card g).mpr
    ⟨hg, hcard⟩), ?_⟩
  intro a
  change a.val ≤ (g a).val
  by_cases ha : a.val ∈ t
  · simp [g, ha]
  · simpa [g, ha] using hf ⟨a.val, Finset.mem_sdiff.mpr ⟨a.property, ha⟩⟩

theorem hasOrderMatching_iff_cancel_intersection (s t : Finset E) :
    HasOrderMatching s t ↔ HasOrderMatching (s \ t) (t \ s) :=
  ⟨HasOrderMatching.cancel_intersection, HasOrderMatching.restore_intersection⟩

theorem hasOrderMatching_iff_matched_sdiff (s t : Finset E) :
    HasOrderMatching s t ↔ IsMatchedPair (s \ t) (t \ s) := by
  rw [hasOrderMatching_iff_cancel_intersection]
  exact ⟨fun h => ⟨by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1, h⟩,
    fun h => h.2⟩

end ResearchMain.PreorderGamma
