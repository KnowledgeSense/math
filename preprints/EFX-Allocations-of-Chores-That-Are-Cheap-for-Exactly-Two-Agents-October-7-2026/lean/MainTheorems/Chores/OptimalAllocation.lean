import MainTheorems.Chores.SeparatedSystems

namespace ResearchMain.Chores

open scoped BigOperators

variable {A E : Type*} [Fintype A] [Fintype E] [DecidableEq A] [DecidableEq E]

def energy (M : TwoCheapModel A E) (S : Finset A) (f : E → A) : ℕ :=
  ∑ a ∈ S, expensiveCount M f a a ^ 2

def Bad (M : TwoCheapModel A E) (f : E → A) (a b : A) : Prop :=
  a ≠ b ∧ OwnCheap M f a ∧ expensiveCount M f a b < expensiveCount M f a a

instance (M : TwoCheapModel A E) (f : E → A) (a b : A) : Decidable (Bad M f a b) :=
  inferInstanceAs (Decidable (a ≠ b ∧ OwnCheap M f a ∧
    expensiveCount M f a b < expensiveCount M f a a))

def badCount (M : TwoCheapModel A E) (S : Finset A) (f : E → A) : ℕ :=
  ((S ×ˢ S).filter (fun p => Bad M f p.1 p.2)).card

def EnergyMinimum (M : TwoCheapModel A E) (S : Finset A) (f₀ f : E → A) : Prop :=
  Feasible M S f₀ f ∧ ∀ g, Feasible M S f₀ g → energy M S f ≤ energy M S g

def Optimal (M : TwoCheapModel A E) (S : Finset A) (f₀ f : E → A) : Prop :=
  Feasible M S f₀ f ∧
    (∀ g, Feasible M S f₀ g → energy M S f ≤ energy M S g) ∧
    (∀ g, Feasible M S f₀ g → energy M S g = energy M S f →
      badCount M S f ≤ badCount M S g)

omit [Fintype A] [DecidableEq E] in
theorem Optimal.energyMinimum (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    (hf : Optimal M S f₀ f) : EnergyMinimum M S f₀ f := ⟨hf.1, hf.2.1⟩

omit [Fintype A] [DecidableEq E] in
theorem EnergyMinimum.of_same_energy (M : TwoCheapModel A E) {S : Finset A} {f₀ f g : E → A}
    (hf : EnergyMinimum M S f₀ f) (hg : Feasible M S f₀ g)
    (heq : energy M S g = energy M S f) : EnergyMinimum M S f₀ g := by
  refine ⟨hg, fun h hh => ?_⟩
  rw [heq]
  exact hf.2 h hh

omit [Fintype A] [DecidableEq E] in
theorem Optimal.of_badCount_le (M : TwoCheapModel A E) {S : Finset A} {f₀ f g : E → A}
    (hf : Optimal M S f₀ f) (hg : Feasible M S f₀ g)
    (heq : energy M S g = energy M S f) (hb : badCount M S g ≤ badCount M S f) :
    Optimal M S f₀ g := by
  have hmin := EnergyMinimum.of_same_energy M (hf.energyMinimum M) hg heq
  refine ⟨hg, hmin.2, ?_⟩
  intro h hh heh
  exact hb.trans (hf.2.2 h hh (heh.trans heq))

theorem exists_optimal (M : TwoCheapModel A E) (S : Finset A) (f₀ : E → A)
    (hf₀ : Separated M S f₀) : ∃ f, Optimal M S f₀ f := by
  classical
  let C := (Finset.univ : Finset (E → A)).filter (Feasible M S f₀)
  have hC : C.Nonempty := ⟨f₀, by simp [C, feasible_self M S f₀ hf₀]⟩
  obtain ⟨f₁, hf₁, hmin⟩ := Finset.exists_min_image C (energy M S) hC
  let D := C.filter (fun f => energy M S f = energy M S f₁)
  have hD : D.Nonempty := ⟨f₁, by simp [D, hf₁]⟩
  obtain ⟨f, hf, hbad⟩ := Finset.exists_min_image D (badCount M S) hD
  have hfD := Finset.mem_filter.mp hf
  have hfeas : Feasible M S f₀ f := (Finset.mem_filter.mp hfD.1).2
  refine ⟨f, hfeas, ?_, ?_⟩
  · intro g hg
    rw [hfD.2]
    exact hmin g (by simp [C, hg])
  · intro g hg hge
    apply hbad g
    simp only [D, Finset.mem_filter]
    exact ⟨by simp [C, hg], hge.trans hfD.2⟩

omit [Fintype A] [DecidableEq E] in
theorem ownCheap_expensive_lt_size (M : TwoCheapModel A E) {f : E → A} {a : A}
    (hc : OwnCheap M f a) : expensiveCount M f a a < (bundle f a).card := by
  have hpos := (ownCheap_iff_count M f a).mp hc
  have hsum := cheap_add_expensive M f a a
  omega

omit [Fintype A] [DecidableEq E] in
theorem bad_expensive_positive (M : TwoCheapModel A E) {f : E → A} {a b : A}
    (hb : Bad M f a b) : 0 < expensiveCount M f a a := by
  exact Nat.zero_lt_of_lt hb.2.2

omit [Fintype A] [DecidableEq E] in
theorem bad_target_cheap (M : TwoCheapModel A E) {f : E → A} {a b : A} {q : ℕ}
    (hb : Bad M f a b) (hs : ∀ v, q ≤ (bundle f v).card ∧ (bundle f v).card ≤ q + 1) :
    ∃ d ∈ bundle f b, M.Cheap a d := by
  have hsum := cheap_add_expensive M f a b
  have hlt := ownCheap_expensive_lt_size M hb.2.1
  have hposa : 0 < cheapCount M f a b := by
    have hsa := (hs a).2
    have hsb := (hs b).1
    have hbad := hb.2.2
    omega
  have hne : ((bundle f b).filter (M.Cheap a)).Nonempty := Finset.card_pos.mp hposa
  obtain ⟨d, hd⟩ := hne
  exact ⟨d, (Finset.mem_filter.mp hd).1, (Finset.mem_filter.mp hd).2⟩

omit [Fintype A] [DecidableEq E] in
theorem own_expensive_exists (M : TwoCheapModel A E) {f : E → A} {a : A}
    (ha : 0 < expensiveCount M f a a) : ∃ e ∈ bundle f a, ¬M.Cheap a e := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp ha
  exact ⟨e, (Finset.mem_filter.mp he).1, (Finset.mem_filter.mp he).2⟩

end ResearchMain.Chores
