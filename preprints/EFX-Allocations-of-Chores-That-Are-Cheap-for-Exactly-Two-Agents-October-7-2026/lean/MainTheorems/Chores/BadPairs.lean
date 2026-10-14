import MainTheorems.Chores.PairStructure
import MainTheorems.Chores.SpecialPair

namespace ResearchMain.Chores

variable {A E : Type*} [Fintype E] [DecidableEq A] [DecidableEq E]

def badPairs (M : TwoCheapModel A E) (S : Finset A) (f : E → A) : Finset (A × A) :=
  (S ×ˢ S).filter (fun p => Bad M f p.1 p.2)

abbrev PairIndex (M : TwoCheapModel A E) (S : Finset A) (f : E → A) :=
  ↥(badPairs M S f)

namespace PairIndex

def high {M : TwoCheapModel A E} {S : Finset A} {f : E → A}
    (i : PairIndex M S f) : A := i.val.1

def low {M : TwoCheapModel A E} {S : Finset A} {f : E → A}
    (i : PairIndex M S f) : A := i.val.2

omit [DecidableEq E] in
theorem members {M : TwoCheapModel A E} {S : Finset A} {f : E → A}
    (i : PairIndex M S f) : i.high ∈ S ∧ i.low ∈ S := by
  exact Finset.mem_product.mp (Finset.mem_filter.mp i.property).1

omit [DecidableEq E] in
theorem bad {M : TwoCheapModel A E} {S : Finset A} {f : E → A}
    (i : PairIndex M S f) : Bad M f i.high i.low :=
  (Finset.mem_filter.mp i.property).2

theorem high_injective (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) :
    Function.Injective (high (M := M) (S := S) (f := f)) := by
  intro i j hij
  have hbad : Bad M f i.high j.low := by simpa only [hij] using j.bad
  have hp := optimal_bad_source_pure M hf hs i.members.1 i.members.2 i.bad
  have hq := optimal_bad_source_pure M hf hs i.members.1 j.members.2 hbad
  have hl := pure_unique M i.bad.2.1 i.bad.1 hbad.1 hp hq
  apply Subtype.ext
  exact Prod.ext hij hl

theorem low_injective (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1) :
    Function.Injective (low (M := M) (S := S) (f := f)) := by
  intro i j hij
  have hbad : Bad M f j.high i.low := by simpa only [hij] using j.bad
  have hh := optimal_pair_low_incoming_unique M hf hs i.members.1 i.members.2
    j.members.1 i.bad hbad
  apply Subtype.ext
  exact Prod.ext hh.symm hij

theorem high_ne_low (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    (i j : PairIndex M S f) : i.high ≠ j.low := by
  intro hij
  have hbad : Bad M f j.low i.low := by simpa only [hij] using i.bad
  exact optimal_pair_low_no_outgoing M hf hs j.members.1 j.members.2
    i.members.2 j.bad hbad

omit [DecidableEq E] in
theorem of_bad {M : TwoCheapModel A E} {S : Finset A} {f : E → A}
    {a b : A} (ha : a ∈ S) (hb : b ∈ S) (hbad : Bad M f a b) :
    ∃ i : PairIndex M S f, i.high = a ∧ i.low = b := by
  exact ⟨⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hbad⟩⟩,
    rfl, rfl⟩

theorem endpoint_unique (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {i j : PairIndex M S f} {a : A} (hi : a = i.high ∨ a = i.low)
    (hj : a = j.high ∨ a = j.low) : i = j := by
  rcases hi with hi | hi <;> rcases hj with hj | hj
  · exact high_injective M hf hs (hi.symm.trans hj)
  · exact False.elim (high_ne_low M hf hs i j (hi.symm.trans hj))
  · exact False.elim (high_ne_low M hf hs j i (hj.symm.trans hi))
  · exact low_injective M hf hs (hi.symm.trans hj)

theorem endpoint_ne (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {i j : PairIndex M S f} (hij : i ≠ j) {v : A} (hv : v = i.high ∨ v = i.low) :
    v ≠ j.high ∧ v ≠ j.low :=
  ⟨fun ht => hij (endpoint_unique M hf hs hv (Or.inl ht)),
    fun ht => hij (endpoint_unique M hf hs hv (Or.inr ht))⟩

theorem outside_expensive (M : TwoCheapModel A E) {S : Finset A} {f₀ f : E → A}
    {q : ℕ} (hf : Optimal M S f₀ f)
    (hs : ∀ c, q ≤ (bundle f c).card ∧ (bundle f c).card ≤ q + 1)
    {i : PairIndex M S f} {v c : A} (hv : v ∈ S)
    (hvn : v ≠ i.high ∧ v ≠ i.low) (hc : c = i.high ∨ c = i.low) :
    expensiveCount M f v c = (bundle f c).card := by
  rcases hc with hc | hc <;> subst c
  · exact pure_outside_expensive M hf.1.1 i.bad.1
      (optimal_bad_source_pure M hf hs i.members.1 i.members.2 i.bad) hv hvn.1 hvn.2
  · exact pure_outside_expensive M hf.1.1 i.bad.1.symm
      (minimum_bad_target_pure M (hf.energyMinimum M) hs i.members.1 i.members.2 i.bad) hv hvn.2 hvn.1

end PairIndex

end ResearchMain.Chores
