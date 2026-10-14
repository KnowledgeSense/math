import R34.KernelBounds

namespace R34

structure Group where
  j : ℕ
  eta : ℝ

def Group.Admissible (G : Group) : Prop :=
  2 ≤ G.j ∧ ((G.j = 2 ∨ G.j = 3) → G.eta = 1) ∧
    (4 ≤ G.j → IsSign G.eta)

/-- Homogeneous form of the boundary ratio interval [-1,2]. -/
def Boundary (A H : ℝ) : Prop := 0 < A ∧ -A ≤ H ∧ H ≤ 2 * A

/-- Homogeneous form of the propagated ratio interval [-1/2,1]. -/
def ValidState (A H : ℝ) : Prop := 0 < A ∧ -(A / 2) ≤ H ∧ H ≤ A

theorem boundary_ratio {A H : ℝ} (h : Boundary A H) :
    -1 ≤ H / A ∧ H / A ≤ 2 := by
  rcases h with ⟨hA,hlo,hhi⟩
  constructor
  · exact (le_div_iff₀ hA).2 (by linarith)
  · exact (div_le_iff₀ hA).2 (by linarith)

theorem valid_ratio {A H : ℝ} (h : ValidState A H) :
    -(1/2 : ℝ) ≤ H / A ∧ H / A ≤ 1 := by
  rcases h with ⟨hA,hlo,hhi⟩
  constructor
  · exact (le_div_iff₀ hA).2 (by linarith)
  · exact (div_le_iff₀ hA).2 (by linarith)

theorem group_interval {G : Group} (hG : G.Admissible) {x : ℝ}
    (hx : -1 ≤ x ∧ x ≤ 2) : -(1/2 : ℝ) ≤ G.eta * x / G.j ∧
      G.eta * x / G.j ≤ 1 := by
  rcases hG with ⟨hj, he, hs⟩
  by_cases h2 : G.j = 2
  · rw [he (Or.inl h2), h2]
    norm_num
    constructor <;> linarith [hx.1,hx.2]
  · by_cases h3 : G.j = 3
    · rw [he (Or.inr h3), h3]
      norm_num
      constructor <;> linarith [hx.1,hx.2]
    · have h4 : 4 ≤ G.j := by omega
      have hj4 : (4 : ℝ) ≤ G.j := by exact_mod_cast h4
      have hjpos : (0 : ℝ) < G.j := by linarith
      rcases hs h4 with hm | hp
      · rw [hm]
        constructor
        · apply (le_div_iff₀ hjpos).2
          nlinarith [hx.1,hx.2]
        · apply (div_le_iff₀ hjpos).2
          nlinarith [hx.1,hx.2]
      · rw [hp]
        constructor
        · apply (le_div_iff₀ hjpos).2
          nlinarith [hx.1,hx.2]
        · apply (div_le_iff₀ hjpos).2
          nlinarith [hx.1,hx.2]

theorem group_initial {G : Group} (hG : G.Admissible) {A H : ℝ}
    (h : Boundary A H) : ValidState (G.j * A) (G.eta * H) := by
  rcases h with ⟨hA,hlo,hhi⟩
  rcases hG with ⟨hj, he, hs⟩
  have hjpos : (0 : ℝ) < G.j := by exact_mod_cast (by omega : 0 < G.j)
  refine ⟨mul_pos hjpos hA, ?_, ?_⟩
  by_cases h2 : G.j = 2
  · rw [he (Or.inl h2),h2]
    norm_num
    linarith
  · by_cases h3 : G.j = 3
    · rw [he (Or.inr h3),h3]
      norm_num
      linarith
    · have h4 : 4 ≤ G.j := by omega
      have hj4 : (4 : ℝ) ≤ G.j := by exact_mod_cast h4
      have hprod := mul_le_mul_of_nonneg_right hj4 hA.le
      rcases hs h4 with hm | hp
      · rw [hm]; nlinarith
      · rw [hp]; nlinarith
  by_cases h2 : G.j = 2
  · rw [he (Or.inl h2),h2]
    norm_num
    linarith
  · by_cases h3 : G.j = 3
    · rw [he (Or.inr h3),h3]
      norm_num
      linarith
    · have h4 : 4 ≤ G.j := by omega
      have hj4 : (4 : ℝ) ≤ G.j := by exact_mod_cast h4
      have hprod := mul_le_mul_of_nonneg_right hj4 hA.le
      rcases hs h4 with hm | hp
      · rw [hm]; nlinarith
      · rw [hp]; nlinarith

theorem kernel_transfer {K : Kernel} {ε A H : ℝ} (hk : KernelIneq K ε)
    (h : ValidState A H) :
    0 < A * K.d + H * K.q ∧
      0 ≤ A * K.p + H * theta K ε ∧
      A * K.p + H * theta K ε ≤ 2 * (A * K.d + H * K.q) := by
  rcases h with ⟨hA,hlo,hhi⟩
  have hden : 0 < A * K.d + H * K.q := by
    have hpos := mul_pos hA (show 0 < K.d - K.q / 2 by linarith [hk.q_lt])
    have hn := mul_nonneg (show 0 ≤ H + A/2 by linarith) hk.q_pos.le
    nlinarith
  have hnum : 0 ≤ A * K.p + H * theta K ε := by
    have h1 := mul_nonneg (show 0 ≤ H + A/2 by linarith) hk.theta_nonneg
    have h2 := mul_nonneg hA.le (show 0 ≤ K.p - theta K ε / 2 by linarith [hk.theta_p])
    nlinarith
  have hupper : A * K.p + H * theta K ε ≤ 2 * (A * K.d + H * K.q) := by
    have h1 := mul_nonneg (show 0 ≤ H + A/2 by linarith)
      (show 0 ≤ 2 * K.q - theta K ε by linarith [hk.theta_q])
    have h2 := mul_nonneg hA.le hk.four
    nlinarith
  exact ⟨hden,hnum,hupper⟩

theorem kernel_step_ratio {r K} (hK : Contracted r K) {ε ζ : ℝ}
    (hε : IsSign ε) (hζ : -(1/2 : ℝ) ≤ ζ ∧ ζ ≤ 1) :
    0 < K.d + K.q * ζ ∧
      0 ≤ (K.p + theta K ε * ζ) / (K.d + K.q * ζ) ∧
      (K.p + theta K ε * ζ) / (K.d + K.q * ζ) ≤ 2 := by
  have hi := kernel_transfer (hK.inequalities hε)
    (show ValidState 1 ζ by exact ⟨by norm_num,hζ.1,hζ.2⟩)
  simp only [one_mul] at hi
  have hd : 0 < K.d + K.q * ζ := by nlinarith [hi.1]
  refine ⟨hd, div_nonneg (by nlinarith [hi.2.1]) hd.le, ?_⟩
  apply (div_le_iff₀ hd).2
  nlinarith [hi.2.2]

theorem group_step {G : Group} (hG : G.Admissible) {K : Kernel} {ε A H : ℝ}
    (hk : KernelIneq K ε) (h : ValidState A H) :
    ValidState (G.j * (A * K.d + H * K.q))
      (G.eta * (A * K.p + H * theta K ε)) := by
  rcases kernel_transfer hk h with ⟨hd,hn,hu⟩
  apply group_initial hG
  exact ⟨hd, by linarith, hu⟩

theorem final_pair_nonnegative {A H P Q : ℝ} (h : ValidState A H)
    (hb : Boundary P Q) : 0 ≤ A * P + H * Q := by
  rcases h with ⟨hA,hlo,hhi⟩
  rcases hb with ⟨hP,hQlo,hQhi⟩
  by_cases hH : 0 ≤ H
  · have h1 := mul_nonneg hH (show 0 ≤ Q + P by linarith)
    have h2 := mul_nonneg (show 0 ≤ A - H by linarith) hP.le
    nlinarith
  · have hHn : H ≤ 0 := le_of_not_ge hH
    have h1 := mul_nonneg (neg_nonneg.mpr hHn) (show 0 ≤ 2 * P - Q by linarith)
    have h2 := mul_nonneg (show 0 ≤ A + 2 * H by linarith) hP.le
    nlinarith

structure RunStep where
  group : Group
  kernel : Kernel
  sign : ℝ

def RunStep.Admissible (s : RunStep) : Prop :=
  s.group.Admissible ∧ (∃ r, Contracted r s.kernel) ∧ IsSign s.sign

def runState (state : ℝ × ℝ) : List RunStep → ℝ × ℝ
  | [] => state
  | s :: ss => runState
      (s.group.j * (state.1 * s.kernel.d + state.2 * s.kernel.q),
       s.group.eta * (state.1 * s.kernel.p + state.2 * theta s.kernel s.sign)) ss

theorem runState_valid (steps : List RunStep) (hs : ∀ s ∈ steps, s.Admissible)
    {state : ℝ × ℝ} (h : ValidState state.1 state.2) :
    ValidState (runState state steps).1 (runState state steps).2 := by
  induction steps generalizing state with
  | nil => exact h
  | cons s ss ih =>
    rcases hs s (by simp) with ⟨hg, ⟨r,hk⟩,hε⟩
    apply ih (fun t ht => hs t (by simp [ht]))
    exact group_step hg (hk.inequalities hε) h

def runValue (first : Group) (left right : ℝ × ℝ) (steps : List RunStep) : ℝ :=
  let state := runState (first.j * left.1, first.eta * left.2) steps
  state.1 * right.1 + state.2 * right.2

theorem run_nonnegative (first : Group) (hg : first.Admissible)
    (left right : ℝ × ℝ) (hl : Boundary left.1 left.2)
    (hr : Boundary right.1 right.2) (steps : List RunStep)
    (hs : ∀ s ∈ steps, s.Admissible) : 0 ≤ runValue first left right steps := by
  exact final_pair_nonnegative (runState_valid steps hs (group_initial hg hl)) hr

theorem free_boundary_valid {v : ℝ × ℝ} (h : Free v) : Boundary v.1 v.2 :=
  free_boundary h

theorem junction_left_boundary {r K} (hK : Contracted r K) {ε : ℝ}
    (hε : IsSign ε) : Boundary K.q (thetaPrime K ε) := by
  have hk := hK.inequalities hε
  exact ⟨hk.q_pos,hk.prime_q_lower,hk.prime_q_upper⟩

theorem junction_right_boundary {r K} (hK : Contracted r K) {ε : ℝ}
    (hε : IsSign ε) : Boundary K.p (thetaPrime K ε) := by
  have hk := hK.inequalities hε
  exact ⟨hk.p_pos,hk.prime_p_lower,hk.prime_p_upper⟩

/-- The closed homogeneous cone also contains a vanishing partial sum. -/
def WeakState (A H : ℝ) : Prop := 0 ≤ A ∧ -(A / 2) ≤ H ∧ H ≤ A

theorem weak_state_cases {A H : ℝ} (h : WeakState A H) :
    ValidState A H ∨ (A = 0 ∧ H = 0) := by
  rcases h with ⟨hA,hlo,hhi⟩
  by_cases hp : 0 < A
  · exact Or.inl ⟨hp,hlo,hhi⟩
  · right; constructor <;> linarith

theorem valid_weak {A H : ℝ} (h : ValidState A H) : WeakState A H :=
  ⟨h.1.le,h.2.1,h.2.2⟩

theorem weak_group_step {G : Group} (hg : G.Admissible) {K : Kernel}
    {ε A H : ℝ} (hk : KernelIneq K ε) (h : WeakState A H) :
    WeakState (G.j * (A * K.d + H * K.q))
      (G.eta * (A * K.p + H * theta K ε)) := by
  rcases weak_state_cases h with hv | ⟨rfl,rfl⟩
  · exact valid_weak (group_step hg hk hv)
  · norm_num [WeakState]

theorem weak_pair_nonnegative {A H P Q : ℝ} (h : WeakState A H)
    (hb : Boundary P Q) : 0 ≤ A * P + H * Q := by
  rcases weak_state_cases h with hv | ⟨rfl,rfl⟩
  · exact final_pair_nonnegative hv hb
  · norm_num

theorem point_to_group {G : Group} (hg : G.Admissible) {K : Kernel}
    {ε H : ℝ} (hk : KernelIneq K ε) (hH : 0 ≤ H) :
    WeakState (G.j * (H * K.q)) (G.eta * (H * thetaPrime K ε)) := by
  by_cases hHp : 0 < H
  · apply valid_weak
    apply group_initial hg
    refine ⟨mul_pos hHp hk.q_pos, ?_, ?_⟩
    · have hm := mul_le_mul_of_nonneg_left hk.prime_q_lower hH
      nlinarith
    · have hm := mul_le_mul_of_nonneg_left hk.prime_q_upper hH
      nlinarith
  · have hz : H = 0 := by linarith
    rw [hz]
    norm_num [WeakState]

inductive Site where
  | point
  | group (G : Group)

def Site.Admissible : Site → Prop
  | .point => True
  | .group G => G.Admissible

def SiteInvariant : Site → ℝ × ℝ → Prop
  | .point, state => state.1 = 0 ∧ 0 ≤ state.2
  | .group _, state => WeakState state.1 state.2

def junction (source target : Site) (K : Kernel) (ε : ℝ) : ℝ :=
  match source, target with
  | .point, .point => theta K ε
  | .group _, .group _ => theta K ε
  | _, _ => thetaPrime K ε

def optionStep (source target : Site) (K : Kernel) (ε : ℝ)
    (state : ℝ × ℝ) : ℝ × ℝ :=
  let vacant := state.1 * K.d + state.2 * K.q
  let occupied := state.1 * K.p + state.2 * junction source target K ε
  match target with
  | .point => (0, occupied)
  | .group G => (G.j * vacant, G.eta * occupied)

theorem optionStep_invariant {source target : Site} (ht : target.Admissible)
    {r K} (hK : Contracted r K) {ε : ℝ} (hε : IsSign ε)
    {state : ℝ × ℝ} (hs : SiteInvariant source state) :
    SiteInvariant target (optionStep source target K ε state) := by
  have hk := hK.inequalities hε
  cases source with
  | point =>
    rcases hs with ⟨hzero,hpos⟩
    cases target with
    | point =>
      simp only [SiteInvariant, optionStep, junction, hzero, zero_mul, zero_add]
      exact ⟨trivial,mul_nonneg hpos hk.theta_nonneg⟩
    | group G =>
      simp only [SiteInvariant, optionStep, junction, hzero, zero_mul, zero_add]
      exact point_to_group ht hk hpos
  | group G =>
    cases target with
    | point =>
      simp only [SiteInvariant, optionStep, junction]
      exact ⟨trivial,weak_pair_nonnegative hs
        ⟨hk.p_pos,hk.prime_p_lower,hk.prime_p_upper⟩⟩
    | group G' =>
      exact weak_group_step ht hk hs

def initialOptions (site : Site) (free : ℝ × ℝ) : ℝ × ℝ :=
  match site with
  | .point => (0,free.2)
  | .group G => (G.j * free.1, G.eta * free.2)

theorem initialOptions_invariant {site : Site} (hs : site.Admissible)
    {free : ℝ × ℝ} (hf : Free free) : SiteInvariant site (initialOptions site free) := by
  cases site with
  | point => exact ⟨rfl,hf.bounds.2.le⟩
  | group G => exact valid_weak (group_initial hs (free_boundary_valid hf))

structure OptionEdge where
  target : Site
  kernel : Kernel
  sign : ℝ

def OptionEdge.Admissible (e : OptionEdge) : Prop :=
  e.target.Admissible ∧ (∃ r, Contracted r e.kernel) ∧ IsSign e.sign

def optionFold (source : Site) (state : ℝ × ℝ) : List OptionEdge → Site × (ℝ × ℝ)
  | [] => (source,state)
  | e :: es => optionFold e.target
      (optionStep source e.target e.kernel e.sign state) es

theorem optionFold_invariant (edges : List OptionEdge)
    (he : ∀ e ∈ edges, e.Admissible) {source : Site} {state : ℝ × ℝ}
    (hs : SiteInvariant source state) :
    SiteInvariant (optionFold source state edges).1 (optionFold source state edges).2 := by
  induction edges generalizing source state with
  | nil => exact hs
  | cons e es ih =>
    rcases he e (by simp) with ⟨ht,⟨r,hk⟩,hε⟩
    apply ih (fun t ht => he t (by simp [ht]))
    exact optionStep_invariant ht hk hε hs

def optionValue (first : Site) (left right : ℝ × ℝ) (edges : List OptionEdge) : ℝ :=
  let result := optionFold first (initialOptions first left) edges
  result.2.1 * right.1 + result.2.2 * right.2

theorem options_nonnegative (first : Site) (hfirst : first.Admissible)
    (left right : ℝ × ℝ) (hl : Free left) (hr : Free right)
    (edges : List OptionEdge) (he : ∀ e ∈ edges, e.Admissible) :
    0 ≤ optionValue first left right edges := by
  have hi := optionFold_invariant edges he (initialOptions_invariant hfirst hl)
  unfold optionValue
  generalize hx : optionFold first (initialOptions first left) edges = result at hi ⊢
  change 0 ≤ result.2.1 * right.1 + result.2.2 * right.2
  cases hkind : result.1 with
  | point =>
    rw [hkind] at hi
    rcases hi with ⟨hz,hpos⟩
    rw [hz]
    simpa using mul_nonneg hpos hr.bounds.2.le
  | group G =>
    rw [hkind] at hi
    exact weak_pair_nonnegative hi (free_boundary_valid hr)

end R34
