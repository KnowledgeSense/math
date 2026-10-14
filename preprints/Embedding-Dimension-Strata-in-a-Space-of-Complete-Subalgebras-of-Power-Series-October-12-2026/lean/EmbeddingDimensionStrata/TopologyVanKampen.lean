import EmbeddingDimensionStrata.TopologyObstructionBasics

noncomputable section
namespace EmbeddingDimensionStrata
namespace TopologyObstructions
open scoped unitInterval
open Set

/-- Straight paths inside the unit interval. -/
def intervalSegment (a b : I) : Path a b where
  toFun t := ⟨(1 - t.val) * a.val + t.val * b.val, by
    constructor
    · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) a.property.1)
        (mul_nonneg t.property.1 b.property.1)
    · calc
        _ ≤ (1 - t.val) * 1 + t.val * 1 := add_le_add
          (mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr t.property.2))
          (mul_le_mul_of_nonneg_left b.property.2 t.property.1)
        _ = 1 := by ring⟩
  continuous_toFun := by fun_prop
  source' := by ext; simp
  target' := by ext; simp

lemma intervalSegment_mem {a b : I} (hab : a ≤ b) (t : I) :
    intervalSegment a b t ∈ Icc a b := by
  change a.val ≤ (1 - t.val) * a.val + t.val * b.val ∧
    (1 - t.val) * a.val + t.val * b.val ≤ b.val
  have hh : a.val ≤ b.val := hab
  constructor
  · nlinarith only [mul_nonneg (sub_nonneg.mpr hh) t.property.1]
  · nlinarith only [mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr t.property.2)]

instance intervalContractible : ContractibleSpace I :=
  (convex_Icc (0 : ℝ) 1).contractibleSpace ⟨0, by norm_num⟩

variable {X : Type*} [TopologicalSpace X] {x y : X}

def pathPart (p : Path x y) (a b : I) : Path (p a) (p b) :=
  (intervalSegment a b).map p.continuous

lemma pathPart_mem (p : Path x y) {a b : I} (hab : a ≤ b)
    {S : Set X} (hS : Icc a b ⊆ p ⁻¹' S) (t : I) : pathPart p a b t ∈ S :=
  hS (intervalSegment_mem hab t)

lemma pathPart_same (p : Path x y) (a : I) : pathPart p a a = Path.refl (p a) := by
  ext t
  change p (intervalSegment a a t) = p a
  congr 1
  apply Subtype.ext
  dsimp [intervalSegment]
  ring

lemma pathPart_trans (p : Path x y) (a b c : I) :
    ((pathPart p a b).trans (pathPart p b c)).Homotopic (pathPart p a c) := by
  have h := (SimplyConnectedSpace.paths_homotopic
    ((intervalSegment a b).trans (intervalSegment b c)) (intervalSegment a c)).map
      p.toContinuousMap
  simpa only [pathPart, Path.map_trans] using h

lemma pathPart_zero_one (p : Path x y) :
    (pathPart p 0 1).cast p.source.symm p.target.symm = p := by
  ext t
  change p (intervalSegment 0 1 t) = p t
  congr 1
  apply Subtype.ext
  simp [intervalSegment]

/-- Paths in a simply connected subspace are homotopic also in the ambient space. -/
theorem homotopic_in_simply_connected_set {S : Set X} (hS : IsSimplyConnected S)
    (p q : Path x y) (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) : p.Homotopic q := by
  have hx : x ∈ S := p.source ▸ hp 0
  have hy : y ∈ S := p.target ▸ hp 1
  let p' : Path (⟨x, hx⟩ : S) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨p t, hp t⟩
      continuous_toFun := p.continuous.subtype_mk _
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let q' : Path (⟨x, hx⟩ : S) ⟨y, hy⟩ :=
    { toFun := fun t => ⟨q t, hq t⟩
      continuous_toFun := q.continuous.subtype_mk _
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  have : SimplyConnectedSpace S := hS
  exact (SimplyConnectedSpace.paths_homotopic p' q').map
    ⟨Subtype.val, continuous_subtype_val⟩

lemma trans_mem_set {a b c : X} {S : Set X} (p : Path a b) (q : Path b c)
    (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) (t : I) : p.trans q t ∈ S := by
  have h : Set.range (p.trans q) ⊆ S := by
    rw [Path.trans_range]
    exact Set.union_subset (Set.range_subset_iff.mpr hp) (Set.range_subset_iff.mpr hq)
  exact h (Set.mem_range_self t)

/-- A pathwise version of the two-open van Kampen argument. Paths from a fixed
basepoint which lie in every cover member containing their endpoint give normal
forms for all path homotopy classes. -/
theorem connector_normal_form {ι : Type*} (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hsimple : ∀ i, IsSimplyConnected (U i)) (a : X) (c : ∀ x, Path a x)
    (hc : ∀ i x, x ∈ U i → ∀ t, c x t ∈ U i) (p : Path x y) :
    (c x |>.trans p).Homotopic (c y) := by
  obtain ⟨t, ht0, hmono, ⟨N, hN⟩, hsub⟩ :=
    exists_monotone_Icc_subset_open_cover_unitInterval
      (fun i => (hopen i).preimage p.continuous)
      (fun u _ => Set.mem_iUnion.mpr (hcover (p u)))
  have hind : ∀ n,
      Path.Homotopic.Quotient.trans (.mk (c (p 0))) (.mk (pathPart p 0 (t n))) =
        .mk (c (p (t n))) := by
    intro n
    induction n with
    | zero =>
      rw [ht0, pathPart_same]
      exact Path.Homotopic.Quotient.trans_refl _
    | succ n ih =>
      obtain ⟨i, hi⟩ := hsub n
      have hl : p (t n) ∈ U i := hi ⟨le_rfl, hmono (Nat.le_succ n)⟩
      have hr : p (t (n + 1)) ∈ U i := hi ⟨hmono (Nat.le_succ n), le_rfl⟩
      have hs := homotopic_in_simply_connected_set (hsimple i)
        ((c (p (t n))).trans (pathPart p (t n) (t (n + 1)))) (c (p (t (n + 1))))
        (trans_mem_set _ _ (hc i _ hl) (pathPart_mem p (hmono (Nat.le_succ n)) hi))
        (hc i _ hr)
      have he := Path.Homotopic.Quotient.eq.mpr (pathPart_trans p 0 (t n) (t (n + 1)))
      rw [← he, Path.Homotopic.Quotient.mk_trans,
        ← Path.Homotopic.Quotient.trans_assoc, ih]
      exact Path.Homotopic.Quotient.eq.mpr hs
  have hh := Path.Homotopic.Quotient.eq.mp (hind N)
  rw [hN N le_rfl] at hh
  have hh' := hh.pathCast rfl p.target.symm
  have hc0 : (c (p 0)).cast rfl p.source.symm = c x := by
    apply Path.ext
    funext u
    exact congrArg (fun q => c q u) p.source
  have hc1 : (c (p 1)).cast rfl p.target.symm = c y := by
    apply Path.ext
    funext u
    exact congrArg (fun q => c q u) p.target
  rw [Path.cast_trans _ _ rfl p.source.symm p.target.symm,
    pathPart_zero_one, hc0, hc1] at hh'
  exact hh'

theorem simplyConnected_of_cover_connector {ι : Type*} (U : ι → Set X)
    (hopen : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i)
    (hsimple : ∀ i, IsSimplyConnected (U i)) (a : X) (c : ∀ x, Path a x)
    (hc : ∀ i x, x ∈ U i → ∀ t, c x t ∈ U i) : SimplyConnectedSpace X := by
  have hpc : PathConnectedSpace X :=
    { nonempty := ⟨a⟩
      joined := fun x y => ⟨(c x).symm.trans (c y)⟩ }
  apply simply_connected_iff_paths_homotopic'.mpr
  refine ⟨hpc, fun {x y} p q => ?_⟩
  have hp := connector_normal_form U hopen hcover hsimple a c hc p
  have hq := connector_normal_form U hopen hcover hsimple a c hc q
  have he := congrArg
    (fun z => Path.Homotopic.Quotient.trans (.mk (c x).symm) z)
    (Path.Homotopic.Quotient.eq.mpr (hp.trans hq.symm))
  apply Path.Homotopic.Quotient.eq.mp
  simpa only [Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
    ← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans] using he

/-- The simply-connected special case of the topological van Kampen theorem.
No local simple-connectivity or covering-space assumptions are required. -/
theorem simplyConnected_of_two_open_cover (U V : Set X)
    (hUo : IsOpen U) (hVo : IsOpen V) (hU : IsSimplyConnected U) (hV : IsSimplyConnected V)
    (hI : IsPathConnected (U ∩ V)) (hcover : U ∪ V = Set.univ) : SimplyConnectedSpace X := by
  classical
  obtain ⟨a, ha⟩ := hI.nonempty
  have hpaths : ∀ x : X, ∃ c : Path a x,
      (x ∈ U → ∀ t, c t ∈ U) ∧ (x ∈ V → ∀ t, c t ∈ V) := by
    intro x
    by_cases hxU : x ∈ U
    · by_cases hxV : x ∈ V
      · let h := hI.joinedIn a ha x ⟨hxU, hxV⟩
        exact ⟨h.somePath, fun _ t => (h.somePath_mem t).1,
          fun _ t => (h.somePath_mem t).2⟩
      · let h := hU.isPathConnected.joinedIn a ha.1 x hxU
        exact ⟨h.somePath, fun _ t => h.somePath_mem t, fun hx => (hxV hx).elim⟩
    · have hxV : x ∈ V := (show x ∈ U ∪ V from hcover.symm ▸ Set.mem_univ x).resolve_left hxU
      let h := hV.isPathConnected.joinedIn a ha.2 x hxV
      exact ⟨h.somePath, fun hx => (hxU hx).elim, fun _ t => h.somePath_mem t⟩
  choose c hcU hcV using hpaths
  apply simplyConnected_of_cover_connector (fun b : Bool => if b then V else U)
    (fun b => by cases b <;> assumption) (fun x => ?_)
    (fun b => by cases b <;> assumption) a c
  · intro b x hx t
    cases b
    · exact hcU x hx t
    · exact hcV x hx t
  · obtain hx | hx := (show x ∈ U ∪ V from hcover.symm ▸ Set.mem_univ x)
    · exact ⟨false, hx⟩
    · exact ⟨true, hx⟩

end TopologyObstructions
end EmbeddingDimensionStrata
