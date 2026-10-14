import MainTheorems.AHOConstants.TraceWords
import Mathlib.Data.Nat.Find

namespace ResearchMain.AHOConstants

open scoped ComplexOrder MatrixOrder

inductive WordStep : TraceWord → TraceWord → Prop
  | zero (u v : TraceWord) (c : Bool) :
      WordStep (u ++ [(c, 0)] ++ v) (u ++ v)
  | merge (u v : TraceWord) (c : Bool) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
      WordStep (u ++ [(c, x), (c, y)] ++ v) (u ++ [(c, x + y)] ++ v)
  | rotate (u v : TraceWord) : WordStep (u ++ v) (v ++ u)

inductive WordReduction : TraceWord → TraceWord → Prop
  | refl (w : TraceWord) : WordReduction w w
  | step {u v : TraceWord} (h : WordStep u v) : WordReduction u v
  | trans {u v w : TraceWord} (h₁ : WordReduction u v) (h₂ : WordReduction v w) :
      WordReduction u w

def WordNonnegative (w : TraceWord) : Prop := ∀ x ∈ w, 0 ≤ x.2

def WordPositive (w : TraceWord) : Prop := ∀ x ∈ w, 0 < x.2

def AdjacentEqual (w : TraceWord) : Prop :=
  ∃ u v : TraceWord, ∃ c : Bool, ∃ x y : ℝ, w = u ++ [(c, x), (c, y)] ++ v

def CyclicEqual (w : TraceWord) : Prop :=
  ∃ u : TraceWord, ∃ c : Bool, ∃ x y : ℝ, w = [(c, x)] ++ u ++ [(c, y)]

def ReducedWord (w : TraceWord) : Prop :=
  WordPositive w ∧ ¬AdjacentEqual w ∧ ¬CyclicEqual w

theorem WordStep.trace {u v : TraceWord} (h : WordStep u v)
    {I : Type*} [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : wordTrace A B u = wordTrace A B v := by
  cases h with
  | zero u v c =>
    unfold wordTrace
    rw [matrixWord_delete_zero A B hA hB]
  | merge u v c x y hx hy =>
    unfold wordTrace
    rw [matrixWord_merge A B hA hB u v c hx hy]
  | rotate u v => exact wordTrace_rotate A B u v

theorem WordStep.mass {u v : TraceWord} (h : WordStep u v) (c : Bool) :
    exponentMass c u = exponentMass c v := by
  cases h with
  | zero u v d => exact exponentMass_delete_zero c d u v
  | merge u v d x y hx hy => exact exponentMass_merge c d u v x y
  | rotate u v => simp only [exponentMass_append, add_comm]

theorem WordStep.nonnegative {u v : TraceWord} (h : WordStep u v)
    (hu : WordNonnegative u) : WordNonnegative v := by
  cases h with
  | zero u v c =>
    intro x hx
    apply hu x
    simp only [List.mem_append, List.mem_singleton] at hx ⊢
    tauto
  | merge u v c x y hx hy =>
    intro z hz
    simp only [List.mem_append, List.mem_singleton] at hz
    rcases hz with (hz | rfl) | hz
    · exact hu z (by simp [hz])
    · exact add_nonneg hx hy
    · exact hu z (by simp [hz])
  | rotate u v =>
    intro x hx
    apply hu x
    simpa only [List.mem_append, or_comm] using hx

theorem WordReduction.trace {u v : TraceWord} (h : WordReduction u v)
    {I : Type*} [Fintype I] [DecidableEq I] (A B : Matrix I I ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) : wordTrace A B u = wordTrace A B v := by
  induction h with
  | refl w => rfl
  | step h => exact h.trace A B hA hB
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem WordReduction.mass {u v : TraceWord} (h : WordReduction u v) (c : Bool) :
    exponentMass c u = exponentMass c v := by
  induction h with
  | refl w => rfl
  | step h => exact h.mass c
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem WordReduction.nonnegative {u v : TraceWord} (h : WordReduction u v)
    (hu : WordNonnegative u) : WordNonnegative v := by
  revert hu
  induction h with
  | refl w => exact id
  | step h => exact h.nonnegative
  | trans h₁ h₂ ih₁ ih₂ => exact fun hu => ih₂ (ih₁ hu)

theorem exists_minimal_word (w : TraceWord) :
    ∃ v, WordReduction w v ∧
      ∀ u, WordReduction v u → v.length ≤ u.length := by
  classical
  let P : ℕ → Prop := fun n => ∃ v, WordReduction w v ∧ v.length = n
  have hp : ∃ n, P n := ⟨w.length, w, WordReduction.refl w, rfl⟩
  obtain ⟨v, hv, hlen⟩ := Nat.find_spec hp
  refine ⟨v, hv, fun u hu => ?_⟩
  rw [hlen]
  exact Nat.find_min' hp ⟨u, hv.trans hu, rfl⟩

theorem minimal_word_positive {w : TraceWord} (hw : WordNonnegative w)
    (hmin : ∀ v, WordReduction w v → w.length ≤ v.length) : WordPositive w := by
  intro cr hcr
  have hc := hw cr hcr
  by_contra h
  have hzero : cr.2 = 0 := by linarith
  obtain ⟨u, v, hword⟩ := List.mem_iff_append.mp hcr
  rcases cr with ⟨c, x⟩
  dsimp at hzero
  subst x
  have hstep : WordReduction w (u ++ v) := by
    rw [hword]
    simpa only [List.append_assoc, List.singleton_append] using
      WordReduction.step (WordStep.zero u v c)
  have hlen := hmin _ hstep
  simp only [hword, List.length_append, List.length_cons] at hlen
  omega

theorem minimal_word_no_adjacent {w : TraceWord} (hw : WordNonnegative w)
    (hmin : ∀ v, WordReduction w v → w.length ≤ v.length) : ¬AdjacentEqual w := by
  rintro ⟨u, v, c, x, y, rfl⟩
  have hx : 0 ≤ x := hw (c, x) (by simp)
  have hy : 0 ≤ y := hw (c, y) (by simp)
  have hlen := hmin _ (WordReduction.step (WordStep.merge u v c x y hx hy))
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  omega

theorem minimal_word_no_cyclic {w : TraceWord} (hw : WordNonnegative w)
    (hmin : ∀ v, WordReduction w v → w.length ≤ v.length) : ¬CyclicEqual w := by
  rintro ⟨u, c, x, y, rfl⟩
  have hx : 0 ≤ x := hw (c, x) (by simp)
  have hy : 0 ≤ y := hw (c, y) (by simp)
  have hr : WordReduction ([(c, x)] ++ u ++ [(c, y)])
      ([(c, y), (c, x)] ++ u) := by
    simpa only [List.singleton_append, List.append_assoc, List.cons_append,
      List.nil_append] using WordReduction.step (WordStep.rotate ([(c, x)] ++ u) [(c, y)])
  have hm : WordReduction ([(c, y), (c, x)] ++ u) ([(c, y + x)] ++ u) := by
    exact WordReduction.step (WordStep.merge [] u c y x hy hx)
  have hlen := hmin _ (hr.trans hm)
  simp only [List.length_append, List.length_cons, List.length_nil] at hlen
  omega

theorem exists_reduced_word {w : TraceWord} (hw : WordNonnegative w) :
    ∃ v, WordReduction w v ∧ ReducedWord v := by
  obtain ⟨v, hv, hmin⟩ := exists_minimal_word w
  have hn := hv.nonnegative hw
  exact ⟨v, hv, minimal_word_positive hn hmin,
    minimal_word_no_adjacent hn hmin, minimal_word_no_cyclic hn hmin⟩

end ResearchMain.AHOConstants
