import R34.KernelRun
import R34.SignExpansion
import R34.ChargePath
import R34.ChargeSites

/-! Schur positivity of charged chains with contracted neutral gaps. -/

namespace R34.ReducedCharge

open MvPolynomial
open ChargeSites
open scoped BigOperators Classical
noncomputable section

inductive Chain where
  | last (site : ChargedSite)
  | cons (site : ChargedSite) (kernel : Kernel) (tail : Chain)

@[reducible] def Chain.first : Chain → ChargedSite
  | .last c => c
  | .cons c _ _ => c

@[reducible] def Chain.sizes : Chain → List ℕ
  | .last c => [c.size]
  | .cons c _ tail => c.size :: tail.sizes

theorem Chain.sizes_pos (ch : Chain) : ∀ a ∈ ch.sizes, 0 < a := by
  induction ch with
  | last c => simpa [Chain.sizes] using c.size_pos
  | cons c K tail ih =>
    intro a ha
    simp only [Chain.sizes, List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact c.size_pos
    · exact ih a ha

def Chain.Admissible : Chain → Prop
  | .last _ => True
  | .cons _ K tail => (∃ r, Contracted r K) ∧ tail.Admissible

@[reducible] def Options : Chain → Type
  | .last _ => Bool
  | .cons _ _ tail => Bool × Options tail

instance optionsFintype (ch : Chain) : Fintype (Options ch) := by
  induction ch with
  | last c => exact inferInstanceAs (Fintype Bool)
  | cons c K tail ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Bool × Options tail))

def firstOption : (ch : Chain) → Options ch → Bool
  | .last _, o => o
  | .cons _ _ _, o => o.1

def lastOption : (ch : Chain) → Options ch → Bool
  | .last _, o => o
  | .cons _ _ tail, o => lastOption tail o.2

def optionBoundary (v : ℝ × ℝ) (o : Bool) : ℝ := if o then v.2 else v.1

def siteCoefficient : ChargedSite → Bool → ℝ
  | .point, o => if o then 1 else 0
  | .group a, o => if o then 1 else (a + 2 : ℕ)

def siteCoefficients : (ch : Chain) → Options ch → ℝ
  | .last c, o => siteCoefficient c o
  | .cons c _ tail, o => siteCoefficient c o.1 * siteCoefficients tail o.2

def optionCoefficient (ch : Chain) (left right : ℝ × ℝ) (o : Options ch) : ℝ :=
  optionBoundary left (firstOption ch o) * siteCoefficients ch o *
    optionBoundary right (lastOption ch o)

def internalAffine (c : ChargedSite) (o : Bool) (_ : Fin (c.size - 1)) : ℝ × ℝ :=
  match c with
  | .point => (1, 0)
  | .group a => if a = 1 then (1, 1) else if o then (0, 1) else (1, 0)

def sameKind : ChargedSite → ChargedSite → Bool
  | .point, .point => true
  | .group _, .group _ => true
  | _, _ => false

def junctionAffine (c d : ChargedSite) (K : Kernel) (o p : Bool) : ℝ × ℝ :=
  if o then
    if p then if sameKind c d then (K.b, K.g) else (K.a, -K.g)
    else (K.q, 0)
  else if p then (K.p, 0) else (K.d, 0)

def edgeAffine : (ch : Chain) → Options ch → ChargeEdges ch.sizes → ℝ × ℝ
  | .last c, o, e => internalAffine c o e
  | .cons c K (.last d), o, e =>
    match e with
    | .inl i => internalAffine c o.1 i
    | .inr (.inl _) => junctionAffine c d K o.1 o.2
    | .inr (.inr e) => internalAffine d o.2 e
  | .cons c K (.cons d L tail), o, e =>
    match e with
    | .inl i => internalAffine c o.1 i
    | .inr (.inl _) => junctionAffine c d K o.1 o.2.1
    | .inr (.inr e) => edgeAffine (.cons d L tail) o.2 e

def affineModel (ch : Chain) (left right : ℝ × ℝ)
    (z : ChargeEdges ch.sizes → ℝ) : ℝ :=
  SignExpansion.affineSum (optionCoefficient ch left right)
    (fun o e => (edgeAffine ch o e).1) (fun o e => (edgeAffine ch o e).2) z

def equalZ (ch : Chain) (χ : ChargeColorings ch.sizes) (e : ChargeEdges ch.sizes) : ℝ :=
  if (chargeEndpoints ch.sizes ch.sizes_pos χ e).1 =
      (chargeEndpoints ch.sizes ch.sizes_pos χ e).2 then 1 else 0

def reducedPolynomial (ch : Chain) (left right : ℝ × ℝ) : Poly :=
  ∑ χ : ChargeColorings ch.sizes, chargeWeight ch.sizes χ *
    C (affineModel ch left right (equalZ ch χ))

def Chain.matrix : Chain → Transfer.Mat
  | .last c => c.matrix
  | .cons c K tail => c.matrix * liftRealMatrix K.entry * tail.matrix

def matrixValue (ch : Chain) (left right : ℝ × ℝ) : Poly :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    C (Kernel.embed left i) * ch.matrix i j * C (Kernel.embed right j)

def Chain.ofFirstRest (first : ChargedSite) : List (Kernel × ChargedSite) → Chain
  | [] => .last first
  | (K, c) :: rest => .cons first K (Chain.ofFirstRest c rest)

def internalEta (c : ChargedSite) (z : Fin (c.size - 1) → ℝ) : ℝ :=
  match c with
  | .point => 1
  | .group a => if a = 1 then 1 else ∏ e, z e

def goodFactor (c : ChargedSite) (z : Fin (c.size - 1) → ℝ) : ℝ :=
  match c with
  | .point => 1
  | .group a => if a = 1 then ∏ e, (1 + z e) else 1

def cornerSite (c : ChargedSite) (z : Fin (c.size - 1) → ℝ) : Site :=
  match c with
  | .point => .point
  | .group a => .group ⟨a + 2, internalEta (.group a) z⟩

theorem internal_product (c : ChargedSite) (o : Bool)
    (z : Fin (c.size - 1) → ℝ) :
    (Finset.univ.prod (fun e : Fin (c.size - 1) =>
      (internalAffine c o e).1 + (internalAffine c o e).2 * z e)) =
      goodFactor c z * (if o then internalEta c z else 1) := by
  cases c with
  | point => cases o <;> simp [internalAffine, ChargedSite.size, goodFactor, internalEta]
  | group a =>
    by_cases ha : a = 1
    · cases o <;> simp [internalAffine, goodFactor, internalEta, ha]
    · cases o <;> simp [internalAffine, goodFactor, internalEta, ha]

theorem sign_isSign (b : Bool) : IsSign (SignExpansion.sign b) := by
  cases b <;> simp [SignExpansion.sign, IsSign]

theorem prod_isSign {ι : Type*} [Fintype ι] (z : ι → ℝ)
    (hz : ∀ i, IsSign (z i)) : IsSign (∏ i, z i) := by
  classical
  have hmul : ∀ a b : ℝ, IsSign a → IsSign b → IsSign (a * b) := by
    intro a b ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num [IsSign]
  apply Finset.prod_induction
  · exact hmul
  · norm_num [IsSign]
  · intro i hi
    exact hz i

theorem cornerSite_admissible (c : ChargedSite) (z : Fin (c.size - 1) → ℝ)
    (hz : ∀ e, IsSign (z e)) : (cornerSite c z).Admissible := by
  cases c with
  | point => trivial
  | group a =>
    change Group.Admissible ⟨a + 2, internalEta (.group a) z⟩
    dsimp only [Group.Admissible]
    refine ⟨by omega, ?_, ?_⟩
    · intro ha
      rcases ha with ha | ha
      · have hzero : a = 0 := by omega
        subst a
        simp [internalEta, ChargedSite.size]
      · have hone : a = 1 := by omega
        simp [internalEta, hone]
    · intro ha
      have hne : a ≠ 1 := by omega
      simp only [internalEta, hne, ite_false]
      exact prod_isSign z hz

theorem goodFactor_nonnegative (c : ChargedSite) (z : Fin (c.size - 1) → ℝ)
    (hz : ∀ e, IsSign (z e)) : 0 ≤ goodFactor c z := by
  cases c with
  | point => norm_num [goodFactor]
  | group a =>
    simp only [goodFactor]
    split_ifs
    · apply Finset.prod_nonneg
      intro e he
      rcases hz e with h | h <;> rw [h] <;> norm_num
    · norm_num

end
end R34.ReducedCharge
