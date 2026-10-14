import CokernelPolynomiality.ChainLinearMaps

noncomputable section
open CategoryTheory
namespace CokernelPolynomiality

/-- A normalized vector at the last nonzero vertex and a detecting functional
at its first nonzero image. These data will construct an actual split interval. -/
structure IntervalSeed {n : ℕ} (V : ChainRep n) where
  a : (Fin (n+1))ᵒᵈ
  b : (Fin (n+1))ᵒᵈ
  hab : a.ofDual.val ≤ b.ofDual.val
  vector : V.obj b
  functional : V.obj a →ₗ[ℂ] ℂ
  normalized : functional (chainMap V a b hab vector)=1
  below_zero : ∀ (i : (Fin (n+1))ᵒᵈ) (hi : i.ofDual.val < a.ofDual.val),
    chainMap V i b (le_trans (le_of_lt hi) hab) vector=0
  above_zero : ∀ (i : (Fin (n+1))ᵒᵈ), b.ofDual.val < i.ofDual.val → ∀ y : V.obj i, y=0

def IntervalSeed.inclusionApp {n : ℕ} {V : ChainRep n} (s : IntervalSeed V) (i : (Fin (n+1))ᵒᵈ) :
    intervalSpace s.a.ofDual.val s.b.ofDual.val i.ofDual.val →ₗ[ℂ] V.obj i :=
  if hi : i.ofDual.val ≤ s.b.ofDual.val then
    (Submodule.subtype (intervalSpace s.a.ofDual.val s.b.ofDual.val i.ofDual.val)).smulRight
      (chainMap V i s.b hi s.vector)
  else 0

@[simp] theorem IntervalSeed.inclusionApp_apply {n : ℕ} {V : ChainRep n} (s : IntervalSeed V)
    (i : (Fin (n+1))ᵒᵈ) (x : intervalSpace s.a.ofDual.val s.b.ofDual.val i.ofDual.val) :
    s.inclusionApp i x=if hi : i.ofDual.val ≤ s.b.ofDual.val then x.val • chainMap V i s.b hi s.vector else 0 := by
  unfold inclusionApp
  split <;> rfl

theorem IntervalSeed.inclusion_naturality {n : ℕ} {V : ChainRep n} (s : IntervalSeed V)
    (i j : (Fin (n+1))ᵒᵈ) (hij : i.ofDual.val ≤ j.ofDual.val) :
    (chainMap V i j hij).comp (s.inclusionApp j)=
      (s.inclusionApp i).comp (intervalMap s.a.ofDual.val s.b.ofDual.val i.ofDual.val j.ofDual.val) := by
  ext x
  simp only [LinearMap.comp_apply,inclusionApp_apply,intervalMap_val]
  by_cases hj : j.ofDual.val ≤ s.b.ofDual.val
  · have hi : i.ofDual.val ≤ s.b.ofDual.val := hij.trans hj
    rw [dite_eq_left hj,dite_eq_left hi,map_smul]
    have hc := congrArg (fun f : V.obj s.b →ₗ[ℂ] V.obj i => f s.vector)
      (chainMap_comp V i j s.b hij hj)
    simp only [LinearMap.comp_apply] at hc
    rw [hc]
    by_cases ha : s.a.ofDual.val ≤ i.ofDual.val
    · rw [ite_eq_left (show intervalActive s.a.ofDual.val s.b.ofDual.val i.ofDual.val from ⟨ha,hi⟩)]
    · have hia : i.ofDual.val < s.a.ofDual.val := lt_of_not_ge ha
      rw [s.below_zero i hia]
      simp
  · rw [dite_eq_right hj,map_zero]
    by_cases hi : i.ofDual.val ≤ s.b.ofDual.val
    · rw [dite_eq_left hi]
      have hx : x.val=0 := intervalSpace_val_zero (by unfold intervalActive; omega) x
      simp [hx]
    · rw [dite_eq_right hi]

def IntervalSeed.inclusion {n : ℕ} {V : ChainRep n} (s : IntervalSeed V) :
    intervalRep n s.a.ofDual.val s.b.ofDual.val ⟶ V where
  app i := FGModuleCat.ofHom (s.inclusionApp i)
  naturality {i j} f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact (congrArg (fun g : intervalSpace s.a.ofDual.val s.b.ofDual.val i.ofDual.val →ₗ[ℂ] V.obj j => g x)
      (s.inclusion_naturality j i (leOfHom f))).symm

def IntervalSeed.retractionApp {n : ℕ} {V : ChainRep n} (s : IntervalSeed V) (i : (Fin (n+1))ᵒᵈ) :
    V.obj i →ₗ[ℂ] intervalSpace s.a.ofDual.val s.b.ofDual.val i.ofDual.val :=
  if hi : intervalActive s.a.ofDual.val s.b.ofDual.val i.ofDual.val then
    LinearMap.codRestrict (intervalSpace s.a.ofDual.val s.b.ofDual.val i.ofDual.val)
      (s.functional.comp (chainMap V s.a i hi.1)) (by intro x; simp [intervalSpace,hi])
  else 0

@[simp] theorem IntervalSeed.retractionApp_val {n : ℕ} {V : ChainRep n} (s : IntervalSeed V)
    (i : (Fin (n+1))ᵒᵈ) (x : V.obj i) :
    (s.retractionApp i x).val=if hi : intervalActive s.a.ofDual.val s.b.ofDual.val i.ofDual.val then
      s.functional (chainMap V s.a i hi.1 x) else 0 := by
  unfold retractionApp
  split <;> rfl

theorem IntervalSeed.retraction_naturality {n : ℕ} {V : ChainRep n} (s : IntervalSeed V)
    (i j : (Fin (n+1))ᵒᵈ) (hij : i.ofDual.val ≤ j.ofDual.val) :
    (s.retractionApp i).comp (chainMap V i j hij)=
      (intervalMap s.a.ofDual.val s.b.ofDual.val i.ofDual.val j.ofDual.val).comp (s.retractionApp j) := by
  ext x
  simp only [LinearMap.comp_apply,retractionApp_val,intervalMap_val]
  by_cases hi : intervalActive s.a.ofDual.val s.b.ofDual.val i.ofDual.val
  · rw [dite_eq_left hi,ite_eq_left hi]
    by_cases hj : intervalActive s.a.ofDual.val s.b.ofDual.val j.ofDual.val
    · rw [dite_eq_left hj]
      have hc := congrArg (fun f : V.obj j →ₗ[ℂ] V.obj s.a => f x)
        (chainMap_comp V s.a i j hi.1 hij)
      exact congrArg s.functional hc
    · rw [dite_eq_right hj]
      have hb : s.b.ofDual.val < j.ofDual.val := by unfold intervalActive at *; omega
      rw [s.above_zero j hb x]
      simp only [map_zero]
  · rw [dite_eq_right hi,ite_eq_right hi]

def IntervalSeed.retraction {n : ℕ} {V : ChainRep n} (s : IntervalSeed V) :
    V ⟶ intervalRep n s.a.ofDual.val s.b.ofDual.val where
  app i := FGModuleCat.ofHom (s.retractionApp i)
  naturality {i j} f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg (fun g : V.obj i →ₗ[ℂ] intervalSpace s.a.ofDual.val s.b.ofDual.val j.ofDual.val => g x)
      (s.retraction_naturality j i (leOfHom f))

theorem IntervalSeed.retractionApp_inclusionApp {n : ℕ} {V : ChainRep n} (s : IntervalSeed V)
    (i : (Fin (n+1))ᵒᵈ) : (s.retractionApp i).comp (s.inclusionApp i)=LinearMap.id := by
  ext x
  simp only [LinearMap.comp_apply,retractionApp_val,inclusionApp_apply,LinearMap.id_coe,id_eq]
  by_cases hi : intervalActive s.a.ofDual.val s.b.ofDual.val i.ofDual.val
  · rw [dite_eq_left hi,dite_eq_left hi.2,map_smul,map_smul]
    have hc := congrArg (fun f : V.obj s.b →ₗ[ℂ] V.obj s.a => f s.vector)
      (chainMap_comp V s.a i s.b hi.1 hi.2)
    simp only [LinearMap.comp_apply] at hc
    rw [hc,s.normalized,smul_eq_mul,mul_one]
  · rw [dite_eq_right hi]
    exact (intervalSpace_val_zero hi x).symm

theorem IntervalSeed.splitting {n : ℕ} {V : ChainRep n} (s : IntervalSeed V) :
    s.inclusion ≫ s.retraction=𝟙 (intervalRep n s.a.ofDual.val s.b.ofDual.val) := by
  apply NatTrans.ext
  funext i
  apply FGModuleCat.hom_ext
  exact s.retractionApp_inclusionApp i

def IntervalSeed.toSplitInterval {n : ℕ} {V : ChainRep n} (s : IntervalSeed V) : SplitInterval V where
  a := s.a.ofDual.val
  b := s.b.ofDual.val
  hab := s.hab
  hbn := by have := s.b.ofDual.isLt; omega
  inclusion := s.inclusion
  retraction := s.retraction
  splitting := s.splitting

end CokernelPolynomiality
