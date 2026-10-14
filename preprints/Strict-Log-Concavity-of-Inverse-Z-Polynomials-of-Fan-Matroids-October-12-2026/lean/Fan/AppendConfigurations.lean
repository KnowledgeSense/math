import Fan.AppendSets

namespace Fan
set_option maxHeartbeats 400000

/-- The last triangular face imposes exactly these two closure rules. -/
def Allowed {n : ℕ} (p : Pair (n+1)) (b c : Bool) : Prop :=
  (c=true → (Fin.last n∈p.1 ↔ b=true)) ∧
  (Fin.last n∈p.1 → b=true → c=true)

@[simp] theorem allowed_false_false {n : ℕ} (p : Pair (n+1)) : Allowed p false false := by
  simp [Allowed]
@[simp] theorem allowed_true_false {n : ℕ} (p : Pair (n+1)) :
    Allowed p true false ↔ Fin.last n∉p.1 := by simp [Allowed]
@[simp] theorem allowed_false_true {n : ℕ} (p : Pair (n+1)) :
    Allowed p false true ↔ Fin.last n∉p.1 := by simp [Allowed]
@[simp] theorem allowed_true_true {n : ℕ} (p : Pair (n+1)) :
    Allowed p true true ↔ Fin.last n∈p.1 := by simp [Allowed]

theorem valid_appendPair {n : ℕ} {p : Pair (n+1)} (b c : Bool)
    (hp : Valid p) (ha : Allowed p b c) : Valid (appendPair p b c) := by
  constructor
  · intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · intro _
      change 0<n+1
      omega
    · intro hi
      exact hp.1 i ((mem_append_cast p.2 c i).mp hi)
  · intro i j
    refine Fin.lastCases ?_ (fun a => ?_) i
    · refine Fin.lastCases ?_ (fun d => ?_) j
      · intro h
        change n+1+1=n+1 at h
        omega
      · intro h
        change n+1+1=d.val at h
        have := d.isLt
        omega
    · refine Fin.lastCases ?_ (fun d => ?_) j
      · intro h
        have he : a=Fin.last n := Fin.ext (by change a.val+1=n+1 at h; change a.val=n; omega)
        subst a
        simpa only [Allowed,appendPair,mem_append_cast,mem_append_last] using ha
      · intro h
        have he : a.val+1=d.val := h
        simpa only [appendPair,mem_append_cast] using hp.2 a d he

theorem valid_appendPair_iff {n : ℕ} (p : Pair (n+1)) (b c : Bool) :
    Valid (appendPair p b c) ↔ Valid p ∧ Allowed p b c := by
  constructor
  · intro h
    constructor
    · simpa only [leftPair_append] using h.left_valid (n:=1)
    · have hb := h.2 (Fin.last n).castSucc (Fin.last (n+1)) rfl
      simpa only [Allowed,appendPair,mem_append_cast,mem_append_last] using hb
  · rintro ⟨hp,ha⟩
    exact valid_appendPair b c hp ha

noncomputable def appendConfiguration {n : ℕ} (p : Configuration (n+1)) (b c : Bool)
    (ha : Allowed p.val b c) : Configuration (n+2) :=
  ⟨appendPair p.val b c,valid_appendPair b c p.property ha⟩

theorem appendConfiguration_rank {n : ℕ} (p : Configuration (n+1)) (b c : Bool)
    (ha : Allowed p.val b c) : configurationRank (appendConfiguration p b c ha)=
      configurationRank p+if b||c then 1 else 0 := by
  change (appendSet p.val.1 b ∪ appendSet p.val.2 c).card=_
  rw [appendSet_union,appendSet_card]
  rfl

abbrev Extension (n : ℕ) :=
  Σ p : Configuration (n+1), {bc : Bool × Bool // Allowed p.val bc.1 bc.2}

/-- Complete last-vertex classification of actual fan flats, including all
four allowed extension patterns and their precise boundary condition. -/
noncomputable def extensionEquiv (n : ℕ) : Extension n ≃ Configuration (n+2) :=
  Equiv.ofBijective
    (fun x => appendConfiguration x.1 x.2.val.1 x.2.val.2 x.2.property) (by
      constructor
      · rintro ⟨p,⟨⟨b,c⟩,ha⟩⟩ ⟨q,⟨⟨d,e⟩,hb⟩⟩ he
        have hev : appendPair p.val b c=appendPair q.val d e := congrArg Subtype.val he
        have hpq : p=q := by
          apply Subtype.ext
          have h := congrArg (leftPair (m:=n+1) (n:=1)) hev
          simpa only [leftPair_append] using h
        have hbd : b=d := by
          have h := congrArg (fun t : Pair (n+2) => lastBit (n:=n+1) t.1) hev
          simpa only [appendPair,lastBit_append] using h
        have hce : c=e := by
          have h := congrArg (fun t : Pair (n+2) => lastBit (n:=n+1) t.2) hev
          simpa only [appendPair,lastBit_append] using h
        subst q
        subst d
        subst e
        rfl
      · intro p
        let q : Configuration (n+1) := ⟨leftPair (m:=n+1) (n:=1) p.val,
          p.property.left_valid (m:=n+1) (n:=1)⟩
        let b := lastBit (n:=n+1) p.val.1
        let c := lastBit (n:=n+1) p.val.2
        have he : appendPair q.val b c=p.val := appendPair_left_last p.val
        have ha : Allowed q.val b c := (valid_appendPair_iff q.val b c).mp
          (he.symm ▸ p.property) |>.2
        exact ⟨⟨q,⟨(b,c),ha⟩⟩,Subtype.ext he⟩)

end Fan
