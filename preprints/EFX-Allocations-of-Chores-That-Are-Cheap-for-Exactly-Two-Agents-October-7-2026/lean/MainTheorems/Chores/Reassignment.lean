import MainTheorems.Chores.InitialAllocation

namespace ResearchMain.Chores

open scoped BigOperators

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

def reassign (f : E → A) (T : Finset E) (g : E → A) : E → A :=
  fun e => if e ∈ T then g e else f e

omit [Fintype E] [DecidableEq A] in
theorem reassign_selected (f : E → A) (T : Finset E) (g : E → A) {e : E} (he : e ∈ T) :
    reassign f T g e = g e := by simp [reassign, he]

omit [Fintype E] [DecidableEq A] in
theorem reassign_other (f : E → A) (T : Finset E) (g : E → A) {e : E} (he : e ∉ T) :
    reassign f T g e = f e := by simp [reassign, he]

theorem reassign_bundle (f : E → A) (T : Finset E) (g : E → A) (a : A) :
    bundle (reassign f T g) a = (bundle f a \ T) ∪ T.filter (fun e => g e = a) := by
  ext e
  simp only [mem_bundle, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter]
  by_cases he : e ∈ T <;> simp [reassign, he]

theorem bundle_partition (f : E → A) (T : Finset E) (a : A) :
    bundle f a = (bundle f a \ T) ∪ T.filter (fun e => f e = a) := by
  ext e
  simp only [mem_bundle, Finset.mem_union, Finset.mem_sdiff, Finset.mem_filter]
  tauto

theorem remaining_selected_disjoint (f : E → A) (T : Finset E) (g : E → A) (a : A) :
    Disjoint (bundle f a \ T) (T.filter (fun e => g e = a)) := by
  rw [Finset.disjoint_left]
  intro e he ht
  exact (Finset.mem_sdiff.mp he).2 (Finset.mem_filter.mp ht).1

theorem reassign_sum_balance {β : Type*} [AddCommMonoid β] (w : E → β)
    (f : E → A) (T : Finset E) (g : E → A) (a : A) :
    bundleSum w (reassign f T g) a + (∑ e ∈ T.filter (fun e => f e = a), w e) =
      bundleSum w f a + (∑ e ∈ T.filter (fun e => g e = a), w e) := by
  have hnew : bundleSum w (reassign f T g) a =
      (∑ e ∈ bundle f a \ T, w e) + ∑ e ∈ T.filter (fun e => g e = a), w e := by
    rw [bundleSum, reassign_bundle, Finset.sum_union (remaining_selected_disjoint f T g a)]
  have hold : bundleSum w f a =
      (∑ e ∈ bundle f a \ T, w e) + ∑ e ∈ T.filter (fun e => f e = a), w e := by
    unfold bundleSum
    conv_lhs => rw [bundle_partition f T a]
    rw [Finset.sum_union (remaining_selected_disjoint f T f a)]
  rw [hnew, hold]
  ac_rfl

theorem reassign_card_balance (f : E → A) (T : Finset E) (g : E → A) (a : A) :
    (bundle (reassign f T g) a).card + (T.filter (fun e => f e = a)).card =
      (bundle f a).card + (T.filter (fun e => g e = a)).card := by
  simpa [bundleSum] using reassign_sum_balance (fun _ : E => (1 : ℕ)) f T g a

def selectedCount (T : Finset E) (p : E → Prop) [DecidablePred p] (f : E → A) (a : A) : ℕ :=
  (T.filter (fun e => f e = a ∧ p e)).card

theorem reassign_expensive_balance (M : TwoCheapModel A E) (f : E → A) (T : Finset E)
    (g : E → A) (a b : A) :
    expensiveCount M (reassign f T g) a b + selectedCount T (fun e => ¬M.Cheap a e) f b =
      expensiveCount M f a b + selectedCount T (fun e => ¬M.Cheap a e) g b := by
  have h := reassign_sum_balance (fun e => if ¬M.Cheap a e then (1 : ℕ) else 0) f T g b
  simpa [bundleSum, Finset.sum_ite, expensiveCount, selectedCount, Finset.filter_filter] using h

theorem reassign_cost_balance (M : TwoCheapModel A E) (r : ℝ) (f : E → A) (T : Finset E)
    (g : E → A) (a b : A) :
    bundleCost M r a (bundle (reassign f T g) b) +
        (∑ e ∈ T.filter (fun e => f e = b), itemCost M r a e) =
      bundleCost M r a (bundle f b) +
        (∑ e ∈ T.filter (fun e => g e = b), itemCost M r a e) :=
  reassign_sum_balance (itemCost M r a) f T g b

end ResearchMain.Chores
