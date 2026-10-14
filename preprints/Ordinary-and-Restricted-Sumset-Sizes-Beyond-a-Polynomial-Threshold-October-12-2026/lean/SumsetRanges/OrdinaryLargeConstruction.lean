import SumsetRanges.OrdinarySparseSet
import SumsetRanges.OrdinaryDenseBounds

open Finset
namespace SumsetRanges

abbrev OrdinaryLargeSpace (ι τ : Type*) := (ι→ℕ) × ℕ × (τ⊕Fin 1→ℤ)

def ordinaryDenseJoinHom (ι τ : Type*) : OrdinarySpace ι τ × (ℕ×ℤ) →+ OrdinaryLargeSpace ι τ where
  toFun a := (a.1.1,a.2.1,Sum.elim a.1.2 (fun _ => a.2.2))
  map_zero' := by apply Prod.ext; rfl; apply Prod.ext; rfl; funext i; cases i <;> rfl
  map_add' a b := by apply Prod.ext; rfl; apply Prod.ext; rfl; funext i; cases i <;> rfl

theorem ordinaryDenseJoinHom_injective (ι τ : Type*) : Function.Injective (ordinaryDenseJoinHom ι τ) := by
  intro a b he
  apply Prod.ext <;> apply Prod.ext
  · exact congrArg (fun v : OrdinaryLargeSpace ι τ => v.1) he
  · funext t; exact congrFun (congrArg (fun v : OrdinaryLargeSpace ι τ => v.2.2) he) (Sum.inl t)
  · exact congrArg (fun v : OrdinaryLargeSpace ι τ => v.2.1) he
  · exact congrFun (congrArg (fun v : OrdinaryLargeSpace ι τ => v.2.2) he) (Sum.inr 0)

noncomputable def ordinaryLargeSet (h c b x : ℕ) (r u : ℕ → ℕ) :
    Finset (OrdinaryLargeSpace (OrdinarySparseAtom h c r u) (OrdinarySparseTag h)) := by
  classical
  exact (separatedUnion (ordinarySparseSet h c r u) (homogenized (denseSet (b-1) x))).image
    (ordinaryDenseJoinHom _ _)

noncomputable def ordinaryValue (h c b : ℕ) (r u : ℕ → ℕ) (x : ℕ) : ℤ :=
  PowerSeries.coeff h (ordinarySparseSeries h c r u*ordinarySeries (denseSet (b-1) x))

theorem card_ordinaryLargeSet (h c b x : ℕ) (r u : ℕ → ℕ) (hh : 2≤h) (hb : 1≤b)
    (hc : ordinaryNonfreeSize h r u≤c) (hx : b-1≤x) :
    (ordinaryLargeSet h c b x r u).card=c+b := by
  classical
  rw [ordinaryLargeSet,Finset.card_image_of_injective _ (ordinaryDenseJoinHom_injective _ _),
    card_separatedUnion _ _ (mixedDegree _ _) (fun a ha => (ordinarySparseSet_bound h c r u hh a ha).2.2),
    card_ordinarySparseSet h c r u hh hc,card_homogenized,card_denseSet _ _ hx]
  omega

theorem ordinaryValue_actual (h c b x : ℕ) (r u : ℕ → ℕ) (hh : 2≤h) :
    ((ordinarySums (ordinaryLargeSet h c b x r u) h).card : ℤ)=ordinaryValue h c b r u x := by
  classical
  rw [←coeff_ordinarySeries,ordinaryLargeSet,ordinarySeries_image_injective _ _ (ordinaryDenseJoinHom_injective _ _),
    ordinarySeries_separatedUnion _ _ (mixedDegree _ _) (fun a ha => (ordinarySparseSet_bound h c r u hh a ha).2.2),
    ordinarySeries_sparseSet h c r u hh,ordinarySeries_homogenized]
  rfl

theorem ordinaryLargeSet_bounds (h c b x : ℕ) (r u : ℕ → ℕ) (hh : 2≤h) (hb : 2≤b)
    (hxb : x≤h*(b-2)+1) : ∀a∈ordinaryLargeSet h c b x r u,
      (∑i,a.1 i)≤h ∧ a.2.1≤h*(c+b) ∧ (∀t,a.2.2 t=0 ∨ a.2.2 t=1) := by
  classical
  intro a ha
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
  rcases (mem_separatedUnion _ _ p).mp hp with ⟨ha,hz⟩ | ⟨hz,hbmem⟩
  · have hA := ordinarySparseSet_bound h c r u hh p.1 ha
    rcases p with ⟨a,b⟩
    dsimp at hz
    subst b
    refine ⟨hA.1,Nat.zero_le _,?_⟩
    intro t
    cases t with
    | inl t => exact hA.2.1 t
    | inr t => exact Or.inl rfl
  · rcases p with ⟨a,b'⟩
    dsimp at hz
    subst a
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hbmem
    have hw' : w=x ∨ w<b-1 := by simpa [denseSet] using hw
    refine ⟨by simp [ordinaryDenseJoinHom],?_,?_⟩
    · change w≤h*(c+b)
      have hbound : h*(b-2)+1≤h*(c+b) := by
        have hb' : b-2+2=b := by omega
        nlinarith
      rcases hw' with rfl | hw'
      · exact hxb.trans hbound
      · have hbig : b≤h*(c+b) := (Nat.le_add_left b c).trans (Nat.le_mul_of_pos_left _ (by omega))
        omega
    · intro t
      cases t with
      | inl t => exact Or.inl rfl
      | inr t => exact Or.inr rfl

end SumsetRanges
