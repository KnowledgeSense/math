import Dowling.PartitionDrop
import Dowling.PartitionUpperEquiv

noncomputable section
namespace Dowling.GainPartition
open scoped Classical
variable {G : Type*} [Group G] {n : ℕ}

omit [Group G] in
theorem oldCode_map_injective : Function.Injective
    (Option.map (fun v : Fin n × G => (v.1.castSucc,v.2))) := by
  intro a b h
  cases a with
  | none => cases b <;> simp_all
  | some a =>
    cases b with
    | none => simp_all
    | some b =>
      simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq] at h
      exact congrArg some (Prod.ext (Fin.castSucc_injective n h.1) h.2)

theorem drop_append (p : GainPartition G n) (c : p.LastChoice) : (p.append c).drop = p := by
  apply code_injective
  funext i
  apply oldCode_map_injective
  simpa only [append,appendCode_old] using (p.append c).drop_code_map i

theorem lastCode_injective (p : GainPartition G n) : Function.Injective p.lastCode := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b =>
      cases b with
      | none => cases h
      | some b =>
        have he := congrArg (fun v => v.map (fun w => w.1.val)) h
        simp only [lastCode,Option.map_some,Option.some.injEq,Fin.val_last,Fin.val_castSucc] at he
        exact False.elim (by have := b.1.val.isLt; omega)
  | some a =>
    cases b with
    | none =>
      cases a with
      | none => cases h
      | some a =>
        have he := congrArg (fun v => v.map (fun w => w.1.val)) h
        simp only [lastCode,Option.map_some,Option.some.injEq,Fin.val_last,Fin.val_castSucc] at he
        exact False.elim (by have := a.1.val.isLt; omega)
    | some b =>
      cases a with
      | none => cases b <;> simp_all [lastCode]
      | some a =>
        cases b with
        | none => cases h
        | some b =>
          change some (a.1.val.castSucc,a.2) = some (b.1.val.castSucc,b.2) at h
          have he := Prod.mk.inj (Option.some.inj h)
          have hr : a.1 = b.1 := Subtype.ext (Fin.castSucc_injective n he.1)
          exact congrArg (fun x => some (some x)) (Prod.ext hr he.2)

theorem append_sigma_injective : Function.Injective
    (fun pc : Σ p : GainPartition G n, p.LastChoice => pc.1.append pc.2) := by
  rintro ⟨p,c⟩ ⟨q,d⟩ h
  have hpq := congrArg drop h
  rw [drop_append,drop_append] at hpq
  change p = q at hpq
  subst q
  change p.append c = p.append d at h
  have hc : c = d := p.lastCode_injective (by
    simpa only [append,appendCode_last] using
      congrArg (fun r : GainPartition G (n+1) => r.code (Fin.last n)) h)
  subst d
  rfl

theorem exists_append (p : GainPartition G (n+1)) : ∃ c : p.drop.LastChoice, p.drop.append c = p := by
  have hext (c : p.drop.LastChoice) (hc : p.drop.lastCode c = p.code (Fin.last n)) :
      p.drop.append c = p := by
    apply code_injective
    funext i
    induction i using Fin.lastCases with
    | last => simpa only [append,appendCode_last] using hc
    | cast i => simpa only [append,appendCode_old] using p.drop_code_map i
  cases hl : p.code (Fin.last n) with
  | none => exact ⟨some none,hext (some none) hl.symm⟩
  | some v =>
    rcases v with ⟨r,g⟩
    by_cases hr : r = Fin.last n
    · subst r
      have hg : g = 1 := congrArg Prod.snd (Option.some.inj (hl.symm.trans (p.rooted _ _ _ hl)))
      subst g
      exact ⟨none,hext none hl.symm⟩
    · have hlt : r.val < n := by
        have hbound := r.isLt
        have hne : r.val ≠ n := by simpa [Fin.ext_iff] using hr
        omega
      let s : Fin n := ⟨r.val,hlt⟩
      have hsr : s.castSucc = r := Fin.ext rfl
      have hroot : p.drop.IsRoot s := by
        have hp : p.code s.castSucc = some (r,1) := by rw [hsr]; exact p.rooted _ _ _ hl
        exact p.dropCode_some s r 1 hp
      refine ⟨some (some (⟨s,hroot⟩,g)),hext _ ?_⟩
      change some (s.castSucc,g) = p.code (Fin.last n)
      rw [hsr,hl]

/-- Literal last-vertex decomposition, retaining all group labels and all
possible zero-block choices. -/
def appendEquiv : (Σ p : GainPartition G n, p.LastChoice) ≃ GainPartition G (n+1) :=
  Equiv.ofBijective (fun pc => pc.1.append pc.2)
    ⟨append_sigma_injective,fun p => by obtain ⟨c,hc⟩ := exists_append p; exact ⟨⟨p.drop,c⟩,hc⟩⟩

end Dowling.GainPartition
