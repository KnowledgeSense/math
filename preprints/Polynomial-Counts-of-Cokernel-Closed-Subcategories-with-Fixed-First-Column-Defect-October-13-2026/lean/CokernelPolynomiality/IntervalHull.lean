import CokernelPolynomiality.IntervalDecomposition
import CokernelPolynomiality.IntervalHomOrder

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace CokernelPolynomiality

inductive IntervalHull (n : ℕ) (Y : Finset (ℕ × ℕ)) : ChainRep n → Prop
  | zero (V : ChainRep n) (hV : IsZero V) : IntervalHull n Y V
  | interval (a b : ℕ) (hab : a ≤ b) (hbn : b ≤ n) (hY : (a,b) ∈ Y) :
      IntervalHull n Y (intervalRep n a b)
  | biprod (V W : ChainRep n) (hV : IntervalHull n Y V) (hW : IntervalHull n Y W) :
      IntervalHull n Y (biprod V W)
  | iso {V W : ChainRep n} (e : V ≅ W) (hV : IntervalHull n Y V) : IntervalHull n Y W

theorem interval_identity_ne_zero (n a b : ℕ) (hab : a ≤ b) (hbn : b ≤ n) :
    𝟙 (intervalRep n a b) ≠ 0 := by
  intro he
  let i : (Fin (n+1))ᵒᵈ := OrderDual.toDual ⟨b,by omega⟩
  let x : intervalSpace a b b := ⟨1,by simp [intervalSpace,intervalActive,hab]⟩
  have hh := congrArg (fun f : intervalRep n a b ⟶ intervalRep n a b => (intervalApp f i x).val) he
  exact one_ne_zero hh

/-- A nonzero interval endomorphism factoring through an additive hull must
use one of that hull's listed interval classes. -/
theorem IntervalHull.factor_nonzero {n : ℕ} {Y : Finset (ℕ × ℕ)} {V : ChainRep n}
    (hV : IntervalHull n Y V) (a b : ℕ) (_hab : a ≤ b) (hbn : b ≤ n)
    (f : intervalRep n a b ⟶ V) (g : V ⟶ intervalRep n a b) (hfg : f ≫ g ≠ 0) :
    (a,b) ∈ Y := by
  induction hV with
  | zero V hV => exact False.elim (hfg (by rw [hV.eq_of_src g 0,comp_zero]))
  | interval c d hcd hdn hY =>
    have hf : f ≠ 0 := by intro h; apply hfg; rw [h,zero_comp]
    have hg : g ≠ 0 := by intro h; apply hfg; rw [h,comp_zero]
    have h1 := intervalHom_order_of_ne_zero f hf hbn
    have h2 := intervalHom_order_of_ne_zero g hg hdn
    have ha : a=c := by omega
    have hb : b=d := by omega
    simpa only [ha,hb] using hY
  | biprod V W hV hW ihV ihW =>
    have he : f ≫ g = (f ≫ biprod.fst) ≫ (biprod.inl ≫ g)+
        (f ≫ biprod.snd) ≫ (biprod.inr ≫ g) := by
      calc
        f ≫ g = f ≫ (𝟙 (CategoryTheory.Limits.biprod V W : ChainRep n)) ≫ g := by simp
        _ = _ := by rw [← biprod.total]; simp only [Preadditive.comp_add,Preadditive.add_comp,Category.assoc]
    by_cases hl : (f ≫ biprod.fst) ≫ (biprod.inl ≫ g) = 0
    · have hr : (f ≫ biprod.snd) ≫ (biprod.inr ≫ g) ≠ 0 := by
        intro hr
        apply hfg
        rw [he,hl,hr,add_zero]
      exact ihW (f ≫ biprod.snd) (biprod.inr ≫ g) hr
    · exact ihV (f ≫ biprod.fst) (biprod.inl ≫ g) hl
  | iso e hV ih =>
    apply ih (f ≫ e.inv) (e.hom ≫ g)
    simpa only [Category.assoc,e.inv_hom_id_assoc] using hfg

theorem retract_composite {n : ℕ} {X Y Z : ChainRep n}
    (i : X ⟶ Y) (p : Y ⟶ X) (j : Y ⟶ Z) (q : Z ⟶ Y)
    (hip : i ≫ p=𝟙 X) (hjq : j ≫ q=𝟙 Y) :
    (i ≫ j) ≫ (q ≫ p)=𝟙 X := by
  calc
    _ = i ≫ (j ≫ q) ≫ p := by simp only [Category.assoc]
    _ = _ := by rw [hjq,Category.id_comp,hip]

/-- The additive hull of a set of intervals is closed under genuine retracts. -/
theorem IntervalHull.retract_mem {n : ℕ} {Y : Finset (ℕ × ℕ)} {V W : ChainRep n}
    (hW : IntervalHull n Y W) (inj : V ⟶ W) (ret : W ⟶ V) (hret : inj ≫ ret=𝟙 V) :
    IntervalHull n Y V := by
  induction interval_decomposition V generalizing W with
  | zero V hV => exact .zero V hV
  | cons V K a b hab hbn _ e ih =>
    let ik : K ⟶ V := biprod.inl ≫ e.inv
    let pk : V ⟶ K := e.hom ≫ biprod.fst
    let ii : intervalRep n a b ⟶ V := biprod.inr ≫ e.inv
    let pi : V ⟶ intervalRep n a b := e.hom ≫ biprod.snd
    have hik : ik ≫ pk=𝟙 K := by simp [ik,pk,Category.assoc]
    have hii : ii ≫ pi=𝟙 (intervalRep n a b) := by simp [ii,pi,Category.assoc]
    have hK := ih hW (ik ≫ inj) (ret ≫ pk) (retract_composite ik pk inj ret hik hret)
    have hI : (a,b) ∈ Y := hW.factor_nonzero a b hab hbn (ii ≫ inj) (ret ≫ pi) (by
      rw [retract_composite ii pi inj ret hii hret]
      exact interval_identity_ne_zero n a b hab hbn)
    exact .iso e.symm (.biprod K (intervalRep n a b) hK (.interval a b hab hbn hI))

theorem IntervalHull.interval_iff {n a b : ℕ} {Y : Finset (ℕ × ℕ)}
    (hab : a ≤ b) (hbn : b ≤ n) :
    IntervalHull n Y (intervalRep n a b) ↔ (a,b) ∈ Y := by
  constructor
  · intro h
    exact h.factor_nonzero a b hab hbn (𝟙 _) (𝟙 _) (by
      rw [Category.id_comp]
      exact interval_identity_ne_zero n a b hab hbn)
  · exact IntervalHull.interval a b hab hbn

end CokernelPolynomiality
