import MainTheorems.Chores.FrozenModels

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

def transfer (f : E → A) (e : E) (b : A) : E → A := reassign f {e} (fun _ => b)

omit [Fintype E] [DecidableEq A] in
theorem transfer_owner (f : E → A) (e : E) (b : A) : transfer f e b e = b := by
  simp [transfer, reassign]

omit [Fintype E] [DecidableEq A] in
theorem transfer_other (f : E → A) {e d : E} (b : A) (hd : d ≠ e) : transfer f e b d = f d := by
  simp [transfer, reassign, hd]

theorem transfer_source_card (f : E → A) (e : E) {b : A} (hb : f e ≠ b) :
    (bundle (transfer f e b) (f e)).card + 1 = (bundle f (f e)).card := by
  simpa [transfer, Finset.filter_singleton, Ne.symm hb] using reassign_card_balance f {e} (fun _ => b) (f e)

theorem transfer_target_card (f : E → A) (e : E) {b : A} (hb : f e ≠ b) :
    (bundle (transfer f e b) b).card = (bundle f b).card + 1 := by
  simpa [transfer, Finset.filter_singleton, hb] using reassign_card_balance f {e} (fun _ => b) b

theorem transfer_other_bundle (f : E → A) (e : E) {b c : A}
    (hce : c ≠ f e) (hcb : c ≠ b) : bundle (transfer f e b) c = bundle f c := by
  ext d
  simp only [mem_bundle]
  by_cases hd : d = e
  · subst d
    simp [transfer_owner, Ne.symm hce, Ne.symm hcb]
  · rw [transfer_other f b hd]

theorem transfer_source_bundle (f : E → A) (e : E) {b : A} (hb : f e ≠ b) :
    bundle (transfer f e b) (f e) = (bundle f (f e)).erase e := by
  ext d
  simp only [mem_bundle, Finset.mem_erase]
  by_cases hd : d = e
  · subst d
    simp [transfer_owner, Ne.symm hb]
  · rw [transfer_other f b hd]
    simp [hd]

theorem transfer_target_bundle (f : E → A) (e : E) (b : A) :
    bundle (transfer f e b) b = insert e (bundle f b) := by
  ext d
  simp only [mem_bundle, Finset.mem_insert]
  by_cases hd : d = e
  · subst d
    simp [transfer_owner]
  · rw [transfer_other f b hd]
    simp [hd]

theorem transfer_source_expensive (M : TwoCheapModel A E) (f : E → A) (e : E)
    {b : A} (hb : f e ≠ b) (c : A) :
    expensiveCount M (transfer f e b) c (f e) + (if M.Cheap c e then 0 else 1) =
      expensiveCount M f c (f e) := by
  have h := reassign_expensive_balance M f {e} (fun _ => b) c (f e)
  by_cases hc : M.Cheap c e <;> simpa [transfer, selectedCount, Finset.filter_singleton, hc, Ne.symm hb] using h

theorem transfer_target_expensive (M : TwoCheapModel A E) (f : E → A) (e : E)
    {b : A} (hb : f e ≠ b) (c : A) :
    expensiveCount M (transfer f e b) c b = expensiveCount M f c b +
      (if M.Cheap c e then 0 else 1) := by
  have h := reassign_expensive_balance M f {e} (fun _ => b) c b
  by_cases hc : M.Cheap c e <;> simpa [transfer, selectedCount, Finset.filter_singleton, hc, hb] using h

theorem transfer_other_expensive (M : TwoCheapModel A E) (f : E → A) (e : E) {b d : A}
    (hde : d ≠ f e) (hdb : d ≠ b) (c : A) :
    expensiveCount M (transfer f e b) c d = expensiveCount M f c d := by
  rw [expensiveCount, transfer_other_bundle f e hde hdb]
  rfl

theorem transfer_source_cost (M : TwoCheapModel A E) (r : ℝ) (f : E → A) (e : E)
    {b : A} (hb : f e ≠ b) (c : A) :
    bundleCost M r c (bundle (transfer f e b) (f e)) + itemCost M r c e =
      bundleCost M r c (bundle f (f e)) := by
  simpa [transfer, Finset.filter_singleton, Ne.symm hb] using reassign_cost_balance M r f {e} (fun _ => b) c (f e)

theorem transfer_target_cost (M : TwoCheapModel A E) (r : ℝ) (f : E → A) (e : E)
    {b : A} (hb : f e ≠ b) (c : A) :
    bundleCost M r c (bundle (transfer f e b) b) = bundleCost M r c (bundle f b) + itemCost M r c e := by
  simpa [transfer, Finset.filter_singleton, hb] using reassign_cost_balance M r f {e} (fun _ => b) c b

omit [Fintype E] in
theorem transfer_separated (M : TwoCheapModel A E) {S : Finset A} {f : E → A}
    (hf : Separated M S f) (e : E) {b : A} (hb : b ∈ S) (hc : M.Cheap b e) :
    Separated M S (transfer f e b) := by
  intro d
  by_cases hd : d = e
  · subst d
    rw [transfer_owner]
    have ht : M.first e ∈ S ∨ M.second e ∈ S := by
      rcases hc with h | h
      · exact Or.inl (h ▸ hb)
      · exact Or.inr (h ▸ hb)
    rw [separatedAllowed, ite_eq_left ht]
    exact Finset.mem_inter.mpr ⟨(mem_endpointAllowed M b e).mpr hc, hb⟩
  · rw [transfer_other f b hd]
    exact hf d

end ResearchMain.Chores
