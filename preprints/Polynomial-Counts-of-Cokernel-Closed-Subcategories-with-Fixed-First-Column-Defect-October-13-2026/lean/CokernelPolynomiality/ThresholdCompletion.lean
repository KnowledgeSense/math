import CokernelPolynomiality.TopTemplates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace CokernelPolynomiality
noncomputable section

/-- An order-faithful real placement of the finite code's vertices. -/
def realPosition {i m : ℕ} (d : Fin i → Fin (m+1)) : Vertex i m → ℝ
  | .root => 0
  | .exceptional j => (i+1 : ℝ)*(d j : ℝ)+(j : ℝ)+1
  | .regular t => (i+1 : ℝ)*((t : ℝ)+1)

def realCutoff {i m : ℕ} (y : Fin i → Fin (m+1)) : Vertex i m → ℝ
  | .exceptional j => (i+1 : ℝ)*(y j : ℝ)
  | _ => -1

 theorem realPosition_exceptional_pos {i m : ℕ} (d : Fin i → Fin (m+1)) (j : Fin i) :
    0 < realPosition d (.exceptional j) := by
  simp only [realPosition]
  positivity

 theorem realPosition_regular_pos {i m : ℕ} (d : Fin i → Fin (m+1)) (t : Fin m) :
    0 < realPosition d (.regular t) := by
  simp only [realPosition]
  positivity

 theorem realPosition_strictMono {i m : ℕ} (d : Fin i → Fin (m+1)) (hd : Monotone d) :
    let _ := codeOrder d
    StrictMono (realPosition d) := by
  let _ := codeOrder d
  change ∀ ⦃u v : Vertex i m⦄, u < v → realPosition d u < realPosition d v
  intro u v huv
  have hi : (0:ℝ) < i+1 := by positivity
  cases u with
  | root =>
    cases v with
    | root => exact False.elim ((lt_irrefl _) huv)
    | exceptional j => exact realPosition_exceptional_pos d j
    | regular t => exact realPosition_regular_pos d t
  | exceptional j =>
    cases v with
    | root => exact False.elim (not_lt_of_gt (root_lt_exceptional d j) huv)
    | exceptional k =>
      have hjk := (exceptional_lt_exceptional d hd j k).mp huv
      have hdjk : (d j : ℝ) ≤ (d k : ℝ) := by exact_mod_cast hd (le_of_lt hjk)
      have hjk' : (j : ℝ) < (k : ℝ) := by exact_mod_cast hjk
      simp only [realPosition]
      nlinarith
    | regular t =>
      have hjt := (exceptional_lt_regular d j t).mp huv
      have hdjt : (d j : ℝ) ≤ (t : ℝ) := by exact_mod_cast hjt
      have hj : (j : ℝ) < (i : ℝ) := by exact_mod_cast j.isLt
      simp only [realPosition]
      nlinarith
  | regular t =>
    cases v with
    | root => exact False.elim (not_lt_of_gt (root_lt_regular d t) huv)
    | exceptional j =>
      have htj := (regular_lt_exceptional d t j).mp huv
      have htdj : (t : ℝ)+1 ≤ (d j : ℝ) := by exact_mod_cast htj
      have hj : (0:ℝ) ≤ j := by positivity
      simp only [realPosition]
      nlinarith
    | regular u =>
      have htu := (regular_lt_regular d t u).mp huv
      have htu' : (t : ℝ) < (u : ℝ) := by exact_mod_cast htu
      simp only [realPosition]
      nlinarith

/-- The unique candidate exceptional-edge set at the highest template size. -/
def completion {i m : ℕ} (d y : Fin i → Fin (m+1)) : SimpleGraph (Fin i) where
  Adj j k := j ≠ k ∧ y j < d k ∧ y k < d j
  symm := ⟨by intro j k h; exact ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨by intro j; simp⟩

 theorem cutoff_lt_exceptional_iff {i m : ℕ} (d y : Fin i → Fin (m+1))
    (j k : Fin i) (hne : y j ≠ d k) :
    realCutoff y (.exceptional j) < realPosition d (.exceptional k) ↔ y j < d k := by
  have hi : (0:ℝ) < i+1 := by positivity
  have hk : (k : ℝ) < (i : ℝ) := by exact_mod_cast k.isLt
  have hk0 : (0:ℝ) ≤ k := by positivity
  simp only [realCutoff,realPosition]
  constructor
  · intro hlt
    by_contra hn
    have hle : d k < y j := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne)
    have hcast : (d k : ℝ)+1 ≤ (y j : ℝ) := by exact_mod_cast hle
    nlinarith
  · intro hlt
    have hcast : (y j : ℝ) < (d k : ℝ) := by exact_mod_cast hlt
    nlinarith

 theorem cutoff_lt_regular_iff {i m : ℕ} (y : Fin i → Fin (m+1))
    (j : Fin i) (t : Fin m) :
    realCutoff y (.exceptional j) < realPosition (fun _ => 0 : Fin i → Fin (m+1)) (.regular t) ↔
      (y j).val < t.val+1 := by
  have hi : (0:ℝ) < i+1 := by positivity
  simp only [realCutoff,realPosition,mul_lt_mul_iff_right₀ hi]
  exact_mod_cast (Iff.rfl : (y j).val < t.val+1 ↔ (y j).val < t.val+1)

 theorem codeGraph_completion_threshold {i m : ℕ} (d y : Fin i → Fin (m+1))
    (hne : ∀ j k, y j ≠ d k) :
    codeGraph y (completion d y) = thresholdGraph (realPosition d) (realCutoff y) := by
  ext u v
  cases u with
  | root =>
    cases v with
    | root => simp [codeGraph,thresholdGraph]
    | exceptional j =>
      have hy : (0:ℝ) ≤ realCutoff y (.exceptional j) := by simp [realCutoff]; positivity
      simp only [codeGraph,codeAdj,thresholdGraph,realPosition]
      simp_all
    | regular t =>
      have hp := realPosition_regular_pos d t
      simp only [codeGraph,codeAdj,thresholdGraph,realCutoff,realPosition] at hp ⊢
      simp only [ne_eq,reduceCtorEq,not_false_eq_true,true_and]
      constructor
      · intro _; constructor <;> linarith
      · intro _; trivial
  | exceptional j =>
    cases v with
    | root =>
      have hy : (0:ℝ) ≤ realCutoff y (.exceptional j) := by simp [realCutoff]; positivity
      simp only [codeGraph,codeAdj,thresholdGraph,realPosition]
      simp_all
    | exceptional k =>
      simp only [codeGraph,codeAdj,completion,thresholdGraph,
        ne_eq, Vertex.exceptional.injEq,cutoff_lt_exceptional_iff d y j k (hne j k),
        cutoff_lt_exceptional_iff d y k j (hne k j)]
    | regular t =>
      have hp := realPosition_exceptional_pos d j
      have he := cutoff_lt_regular_iff y j t
      simp only [realPosition] at he hp
      simp only [codeGraph,codeAdj,thresholdGraph,realCutoff,realPosition]
      simp only [ne_eq,reduceCtorEq,not_false_eq_true,true_and]
      rw [show (i+1 : ℝ)*(y j : ℝ) < (i+1 : ℝ)*((t : ℝ)+1) ↔ (y j).val < t.val+1 from he]
      constructor
      · intro h; exact ⟨h,by linarith⟩
      · exact And.left
  | regular t =>
    cases v with
    | root =>
      have hp := realPosition_regular_pos d t
      simp only [codeGraph,codeAdj,thresholdGraph,realCutoff,realPosition] at hp ⊢
      simp only [ne_eq,reduceCtorEq,not_false_eq_true,true_and]
      constructor
      · intro _; constructor <;> linarith
      · intro _; trivial
    | exceptional j =>
      have hp := realPosition_exceptional_pos d j
      have he := cutoff_lt_regular_iff y j t
      simp only [realPosition] at he hp
      simp only [codeGraph,codeAdj,thresholdGraph,realCutoff,realPosition]
      simp only [ne_eq,reduceCtorEq,not_false_eq_true,true_and]
      rw [show (i+1 : ℝ)*(y j : ℝ) < (i+1 : ℝ)*((t : ℝ)+1) ↔ (y j).val < t.val+1 from he]
      constructor
      · intro h; exact ⟨by linarith,h⟩
      · exact And.right
    | regular u =>
      have ht := realPosition_regular_pos d t
      have hu := realPosition_regular_pos d u
      simp only [codeGraph,codeAdj,thresholdGraph,realCutoff,realPosition] at ht hu ⊢
      simp only [ne_eq, Vertex.regular.injEq]
      constructor
      · intro h; exact ⟨h,by linarith,by linarith⟩
      · exact And.left

 theorem completion_admissible {i m : ℕ} (d y : Fin i → Fin (m+1)) (hd : Monotone d)
    (hne : ∀ j k, y j ≠ d k) :
    let _ := codeOrder d
    Admissible (codeGraph y (completion d y)) := by
  let _ := codeOrder d
  rw [codeGraph_completion_threshold d y hne]
  exact thresholdGraph_admissible _ _ (realPosition_strictMono d hd)

 theorem top_template_admissible_iff {i : ℕ} (c : Code i (2*i)) (hn : c.IsNormalized) :
    c.IsAdmissible ↔ c.epsilon = completion c.d c.y := by
  constructor
  · intro hc
    ext j k
    by_cases he : j = k
    · subst k
      simp
    · rcases lt_or_gt_of_ne he with hjk | hkj
      · change c.epsilon.Adj j k ↔ j ≠ k ∧ c.y j < c.d k ∧ c.y k < c.d j
        constructor
        · intro h; exact ⟨he,(normalized_top_forced_edge c hc hn j k hjk).mp h⟩
        · intro h; exact (normalized_top_forced_edge c hc hn j k hjk).mpr h.2
      · rw [SimpleGraph.adj_comm (V := Fin i) (G := c.epsilon) j k,
          SimpleGraph.adj_comm (V := Fin i) (G := completion c.d c.y) j k]
        change c.epsilon.Adj k j ↔ k ≠ j ∧ c.y k < c.d j ∧ c.y j < c.d k
        constructor
        · intro h; exact ⟨Ne.symm he,(normalized_top_forced_edge c hc hn k j hkj).mp h⟩
        · intro h; exact (normalized_top_forced_edge c hc hn k j hkj).mpr h.2
  · intro he
    have hi := (top_coordinates_bijective c hn).1
    have hne : ∀ j k, c.y j ≠ c.d k := by
      intro j k heq
      have hh := hi (show c.coordinate (Sum.inr j) = c.coordinate (Sum.inl k) from heq)
      cases hh
    change @Admissible (Vertex i (2*i)) (codeOrder c.d) (codeGraph c.y c.epsilon)
    rw [he]
    exact completion_admissible c.d c.y c.monotone_d hne

end
end CokernelPolynomiality
