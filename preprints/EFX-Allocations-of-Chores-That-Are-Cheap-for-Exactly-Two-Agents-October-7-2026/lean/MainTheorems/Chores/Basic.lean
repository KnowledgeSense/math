import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace ResearchMain.Chores

structure TwoCheapModel (A E : Type*) where
  first : E → A
  second : E → A
  distinct : ∀ e, first e ≠ second e

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

def TwoCheapModel.Cheap (M : TwoCheapModel A E) (a : A) (e : E) : Prop :=
  a = M.first e ∨ a = M.second e

instance (M : TwoCheapModel A E) (a : A) (e : E) : Decidable (M.Cheap a e) :=
  inferInstanceAs (Decidable (a = M.first e ∨ a = M.second e))

noncomputable def itemCost (M : TwoCheapModel A E) (r : ℝ) (a : A) (e : E) : ℝ :=
  if M.Cheap a e then 1 else r

def bundle (f : E → A) (a : A) : Finset E := Finset.univ.filter (fun e => f e = a)

noncomputable def bundleCost (M : TwoCheapModel A E) (r : ℝ) (a : A) (s : Finset E) : ℝ :=
  ∑ e ∈ s, itemCost M r a e

def EFX (M : TwoCheapModel A E) (r : ℝ) (f : E → A) : Prop :=
  ∀ a b : A, a ≠ b → ∀ e ∈ bundle f a,
    bundleCost M r a ((bundle f a).erase e) ≤ bundleCost M r a (bundle f b)

def OwnCheap (M : TwoCheapModel A E) (f : E → A) (a : A) : Prop :=
  ∃ e ∈ bundle f a, M.Cheap a e

instance (M : TwoCheapModel A E) (f : E → A) (a : A) : Decidable (OwnCheap M f a) :=
  inferInstanceAs (Decidable (∃ e ∈ bundle f a, M.Cheap a e))

noncomputable def threshold (M : TwoCheapModel A E) (r : ℝ) (f : E → A) (a : A) : ℝ :=
  if (bundle f a).Nonempty then
    bundleCost M r a (bundle f a) - if OwnCheap M f a then 1 else r
  else 0

omit [DecidableEq E] in
theorem mem_bundle (f : E → A) (a : A) (e : E) : e ∈ bundle f a ↔ f e = a := by
  simp [bundle]

omit [Fintype E] [DecidableEq E] in
theorem itemCost_ge_one (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r) (a : A) (e : E) :
    1 ≤ itemCost M r a e := by
  unfold itemCost
  split_ifs <;> linarith

omit [Fintype E] [DecidableEq E] in
theorem bundleCost_nonnegative (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    (a : A) (s : Finset E) : 0 ≤ bundleCost M r a s :=
  Finset.sum_nonneg (fun e _ => (by linarith [itemCost_ge_one M hr a e]))

omit [Fintype E] in
theorem bundleCost_erase (M : TwoCheapModel A E) (r : ℝ) (a : A) {s : Finset E}
    {e : E} (he : e ∈ s) : bundleCost M r a (s.erase e) = bundleCost M r a s - itemCost M r a e := by
  have h := Finset.sum_erase_add (s := s) (fun e => itemCost M r a e) he
  unfold bundleCost
  linarith

theorem removed_cost_le_threshold (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    (f : E → A) (a : A) {e : E} (he : e ∈ bundle f a) :
    bundleCost M r a ((bundle f a).erase e) ≤ threshold M r f a := by
  rw [bundleCost_erase M r a he, threshold, ite_eq_left ⟨e, he⟩]
  by_cases hc : OwnCheap M f a
  · rw [ite_eq_left hc]
    linarith [itemCost_ge_one M hr a e]
  · rw [ite_eq_right hc]
    have hn : ¬M.Cheap a e := fun h => hc ⟨e, he, h⟩
    simp [itemCost, hn]

theorem threshold_attained (M : TwoCheapModel A E) (r : ℝ) (f : E → A) (a : A)
    (ha : (bundle f a).Nonempty) :
    ∃ e ∈ bundle f a, bundleCost M r a ((bundle f a).erase e) = threshold M r f a := by
  by_cases hc : OwnCheap M f a
  · have hc' := hc
    obtain ⟨e, he, hcheap⟩ := hc
    refine ⟨e, he, ?_⟩
    rw [bundleCost_erase M r a he, threshold, ite_eq_left ha, ite_eq_left hc']
    simp [itemCost, hcheap]
  · obtain ⟨e, he⟩ := ha
    refine ⟨e, he, ?_⟩
    rw [bundleCost_erase M r a he, threshold, ite_eq_left ⟨e, he⟩, ite_eq_right hc]
    have hn : ¬M.Cheap a e := fun h => hc ⟨e, he, h⟩
    simp [itemCost, hn]

theorem efx_iff_threshold (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r) (f : E → A) :
    EFX M r f ↔ ∀ a b : A, a ≠ b → threshold M r f a ≤ bundleCost M r a (bundle f b) := by
  constructor
  · intro h a b hab
    by_cases ha : (bundle f a).Nonempty
    · obtain ⟨e, he, heq⟩ := threshold_attained M r f a ha
      rw [← heq]
      exact h a b hab e he
    · rw [threshold, ite_eq_right ha]
      exact bundleCost_nonnegative M hr a _
  · intro h a b hab e he
    exact (removed_cost_le_threshold M hr f a he).trans (h a b hab)

theorem injective_allocation_efx (M : TwoCheapModel A E) {r : ℝ} (hr : 2 < r)
    {f : E → A} (hf : Function.Injective f) : EFX M r f := by
  intro a b _ e he
  have hb : bundle f a = {e} := by
    apply Finset.ext
    intro d
    simp only [mem_bundle, Finset.mem_singleton]
    constructor
    · intro hd
      exact hf (hd.trans ((mem_bundle f a e).mp he).symm)
    · intro hd
      rw [hd]
      exact (mem_bundle f a e).mp he
  rw [hb]
  simpa [bundleCost] using bundleCost_nonnegative M hr a (bundle f b)

end ResearchMain.Chores
