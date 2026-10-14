import CokernelPolynomiality.RepresentationSubcategories

noncomputable section
open CategoryTheory CategoryTheory.Limits
universe u
namespace CokernelPolynomiality

def directPair {n : ℕ} (V W : ChainRep.{u} n) : ChainRep.{u} n where
  obj i := FGModuleCat.of ℂ (V.obj i × W.obj i)
  map f := FGModuleCat.ofHom ((V.map f).hom.hom.prodMap (W.map f).hom.hom)
  map_id i := by
    apply FGModuleCat.hom_ext
    change ((V.map (𝟙 i)).hom.hom.prodMap (W.map (𝟙 i)).hom.hom)=LinearMap.id
    rw [V.map_id,W.map_id]
    rfl
  map_comp f g := by
    apply FGModuleCat.hom_ext
    change ((V.map (f ≫ g)).hom.hom.prodMap (W.map (f ≫ g)).hom.hom)=_
    rw [V.map_comp,W.map_comp]
    rfl

def directPairFst {n : ℕ} (V W : ChainRep.{u} n) : directPair V W ⟶ V where
  app i := FGModuleCat.ofHom (LinearMap.fst ℂ (V.obj i) (W.obj i))
  naturality {_i _j} _f := rfl

def directPairSnd {n : ℕ} (V W : ChainRep.{u} n) : directPair V W ⟶ W where
  app i := FGModuleCat.ofHom (LinearMap.snd ℂ (V.obj i) (W.obj i))
  naturality {_i _j} _f := rfl

def directPairInl {n : ℕ} (V W : ChainRep.{u} n) : V ⟶ directPair V W where
  app i := FGModuleCat.ofHom (LinearMap.inl ℂ (V.obj i) (W.obj i))
  naturality {_i _j} f := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ((V.map f).hom.hom x,0)=((V.map f).hom.hom x,(W.map f).hom.hom 0)
    rw [map_zero]

def directPairInr {n : ℕ} (V W : ChainRep.{u} n) : W ⟶ directPair V W where
  app i := FGModuleCat.ofHom (LinearMap.inr ℂ (V.obj i) (W.obj i))
  naturality {_i _j} f := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (0,(W.map f).hom.hom x)=((V.map f).hom.hom 0,(W.map f).hom.hom x)
    rw [map_zero]

@[simp] theorem directPair_inl_fst {n : ℕ} (V W : ChainRep.{u} n) :
    directPairInl V W ≫ directPairFst V W=𝟙 V := rfl
@[simp] theorem directPair_inl_snd {n : ℕ} (V W : ChainRep.{u} n) :
    directPairInl V W ≫ directPairSnd V W=0 := rfl
@[simp] theorem directPair_inr_fst {n : ℕ} (V W : ChainRep.{u} n) :
    directPairInr V W ≫ directPairFst V W=0 := rfl
@[simp] theorem directPair_inr_snd {n : ℕ} (V W : ChainRep.{u} n) :
    directPairInr V W ≫ directPairSnd V W=𝟙 W := rfl

theorem directPair_total {n : ℕ} (V W : ChainRep.{u} n) :
    directPairFst V W ≫ directPairInl V W+directPairSnd V W ≫ directPairInr V W=
      𝟙 (directPair V W) := by
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (x.1,0)+(0,x.2)=x
  exact Prod.ext (add_zero _) (zero_add _)

def directPairIsoBiprod {n : ℕ} (V W : ChainRep.{u} n) : directPair V W ≅ biprod V W where
  hom := biprod.lift (directPairFst V W) (directPairSnd V W)
  inv := biprod.desc (directPairInl V W) (directPairInr V W)
  hom_inv_id := by simp [directPair_total]
  inv_hom_id := by
    apply biprod.hom_ext <;> apply biprod.hom_ext' <;> simp

def directPairLift {n : ℕ} {X V W : ChainRep.{u} n} (f : X ⟶ V) (g : X ⟶ W) :
    X ⟶ directPair V W where
  app i := FGModuleCat.ofHom ((f.app i).hom.hom.prod (g.app i).hom.hom)
  naturality {i j} h := by
    apply FGModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Prod.ext
    · exact congrArg (fun k => k.hom.hom x) (f.naturality h)
    · exact congrArg (fun k => k.hom.hom x) (g.naturality h)

end CokernelPolynomiality
