import MainTheorems.Chores.BalancedAllocation

namespace ResearchMain.Chores

open scoped BigOperators

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

def exchange (f : E → A) (e d : E) : E → A := f ∘ Equiv.swap e d

omit [Fintype E] [DecidableEq A] in
theorem exchange_left (f : E → A) (e d : E) : exchange f e d e = f d := by
  simp [exchange]

omit [Fintype E] [DecidableEq A] in
theorem exchange_right (f : E → A) (e d : E) : exchange f e d d = f e := by
  simp [exchange]

omit [Fintype E] [DecidableEq A] in
theorem exchange_other (f : E → A) {e d c : E} (he : c ≠ e) (hd : c ≠ d) :
    exchange f e d c = f c := by
  simp [exchange, Equiv.swap_apply_of_ne_of_ne he hd]

omit [Fintype E] [DecidableEq A] in
theorem exchange_involution (f : E → A) (e d : E) :
    exchange (exchange f e d) e d = f := by
  funext c
  simp [exchange, Function.comp_def]

theorem exchange_bundle_left (f : E → A) {e d : E} (hed : e ≠ d) (howners : f e ≠ f d) :
    bundle (exchange f e d) (f e) = insert d ((bundle f (f e)).erase e) := by
  ext c
  simp only [mem_bundle, Finset.mem_insert, Finset.mem_erase]
  by_cases hce : c = e
  · subst c
    simp [exchange_left, hed, Ne.symm howners]
  · by_cases hcd : c = d
    · subst c
      simp [exchange_right]
    · rw [exchange_other f hce hcd]
      simp [hce, hcd]

theorem exchange_bundle_right (f : E → A) {e d : E} (hed : e ≠ d) (howners : f e ≠ f d) :
    bundle (exchange f e d) (f d) = insert e ((bundle f (f d)).erase d) := by
  have heq : exchange f e d = exchange f d e := by
    simp [exchange, Equiv.swap_comm]
  rw [heq]
  exact exchange_bundle_left f hed.symm howners.symm

theorem exchange_bundle_other (f : E → A) {e d : E} {a : A}
    (hae : a ≠ f e) (had : a ≠ f d) : bundle (exchange f e d) a = bundle f a := by
  ext c
  simp only [mem_bundle]
  by_cases hce : c = e
  · subst c
    simp [exchange_left, Ne.symm hae, Ne.symm had]
  · by_cases hcd : c = d
    · subst c
      simp [exchange_right, Ne.symm hae, Ne.symm had]
    · rw [exchange_other f hce hcd]

theorem exchange_bundle_card (f : E → A) (e d : E) (a : A) :
    (bundle (exchange f e d) a).card = (bundle f a).card := by
  apply Finset.card_bij (fun c _ => Equiv.swap e d c)
  · intro c hc
    exact (mem_bundle f a _).mpr ((mem_bundle (exchange f e d) a c).mp hc)
  · intro c _ c' _ heq
    exact (Equiv.swap e d).injective heq
  · intro c hc
    refine ⟨Equiv.swap e d c, ?_, ?_⟩
    · simpa [mem_bundle, exchange, Function.comp_def] using (mem_bundle f a c).mp hc
    · simp

def bundleSum {β : Type*} [AddCommMonoid β] (w : E → β) (f : E → A) (a : A) : β :=
  ∑ e ∈ bundle f a, w e

theorem exchange_sum_left {β : Type*} [AddCommGroup β] (w : E → β) (f : E → A)
    {e d : E} (hed : e ≠ d) (howners : f e ≠ f d) :
    bundleSum w (exchange f e d) (f e) = bundleSum w f (f e) - w e + w d := by
  have he : e ∈ bundle f (f e) := (mem_bundle f (f e) e).mpr rfl
  have hd : d ∉ (bundle f (f e)).erase e := by
    simp [mem_bundle, Ne.symm howners]
  rw [bundleSum, exchange_bundle_left f hed howners, Finset.sum_insert hd]
  have hs := Finset.sum_erase_add (s := bundle f (f e)) w he
  unfold bundleSum
  have hs' : (∑ c ∈ (bundle f (f e)).erase e, w c) =
      (∑ c ∈ bundle f (f e), w c) - w e := (eq_sub_iff_add_eq).mpr hs
  rw [hs']
  exact add_comm _ _

theorem exchange_sum_right {β : Type*} [AddCommGroup β] (w : E → β) (f : E → A)
    {e d : E} (hed : e ≠ d) (howners : f e ≠ f d) :
    bundleSum w (exchange f e d) (f d) = bundleSum w f (f d) - w d + w e := by
  have heq : exchange f e d = exchange f d e := by simp [exchange, Equiv.swap_comm]
  rw [heq]
  exact exchange_sum_left w f hed.symm howners.symm

omit [DecidableEq E] in
theorem expensiveCount_eq_sum (M : TwoCheapModel A E) (f : E → A) (a b : A) :
    (expensiveCount M f a b : ℤ) =
      bundleSum (fun e => if M.Cheap a e then (0 : ℤ) else 1) f b := by
  simp [expensiveCount, bundleSum, Finset.sum_ite]

end ResearchMain.Chores
