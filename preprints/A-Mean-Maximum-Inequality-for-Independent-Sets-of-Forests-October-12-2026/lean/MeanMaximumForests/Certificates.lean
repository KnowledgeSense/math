import MeanMaximumForests.Cones
import Mathlib.Tactic.NormNum

namespace MeanMaximumForests

@[ext] structure IntegerVector where
  p : ℤ
  q : ℤ
  x : ℤ
  y : ℤ
  deriving DecidableEq

def IntegerVector.toReal (v : IntegerVector) : ConeVector := ⟨v.p, v.q, v.x, v.y⟩
def IntegerVector.zero : IntegerVector := ⟨0, 0, 0, 0⟩
def IntegerVector.add (v w : IntegerVector) : IntegerVector :=
  ⟨v.p + w.p, v.q + w.q, v.x + w.x, v.y + w.y⟩
def IntegerVector.scale (n : ℕ) (v : IntegerVector) : IntegerVector :=
  ⟨n * v.p, n * v.q, n * v.x, n * v.y⟩
def IntegerVector.product (v w : IntegerVector) : IntegerVector :=
  ⟨v.p * w.p, v.q * w.q, v.x * w.p + v.p * w.x, v.y * w.q + v.q * w.y⟩
def IntegerVector.root100 (f : Bool) (v : IntegerVector) : IntegerVector :=
  let b : ℤ := if f then 0 else 1
  ⟨100 * (v.p + v.q), 100 * v.p,
    100 * v.x + 100 * v.y + (100 - 47 * b) * v.q - 47 * b * v.p,
    100 * v.x - 47 * b * v.p⟩

theorem IntegerVector.toReal_zero : IntegerVector.zero.toReal = zeroVector := by
  ext <;> simp [IntegerVector.zero, IntegerVector.toReal, zeroVector]
theorem IntegerVector.toReal_add (v w : IntegerVector) :
    (v.add w).toReal = MeanMaximumForests.add v.toReal w.toReal := by
  ext <;> simp [IntegerVector.add, IntegerVector.toReal, MeanMaximumForests.add]
theorem IntegerVector.toReal_scale (n : ℕ) (v : IntegerVector) :
    (v.scale n).toReal = MeanMaximumForests.scale n v.toReal := by
  ext <;> simp [IntegerVector.scale, IntegerVector.toReal, MeanMaximumForests.scale]
theorem IntegerVector.toReal_product (v w : IntegerVector) :
    (v.product w).toReal = MeanMaximumForests.product v.toReal w.toReal := by
  ext <;> simp [IntegerVector.product, IntegerVector.toReal, MeanMaximumForests.product]
theorem IntegerVector.toReal_root100 (f : Bool) (v : IntegerVector) :
    (v.root100 f).toReal = MeanMaximumForests.scale 100 (plant (47 / 100) f v.toReal) := by
  cases f <;> ext <;>
    simp [IntegerVector.root100, IntegerVector.toReal, MeanMaximumForests.scale, plant] <;> ring

def integerSum {n : ℕ} (g : Fin n → IntegerVector) : List (Fin n × ℕ) → IntegerVector
  | [] => .zero
  | (i, a) :: rest => (g i).scale a |>.add (integerSum g rest)
def generatorSet {n : ℕ} (g : Fin n → IntegerVector) : Set ConeVector :=
  Set.range (fun i => (g i).toReal)

theorem integerSum_mem {n : ℕ} (g : Fin n → IntegerVector) (l : List (Fin n × ℕ)) :
    GeneratedCone (generatorSet g) (integerSum g l).toReal := by
  induction l with
  | nil =>
    simp only [integerSum, IntegerVector.toReal_zero]
    exact .zero
  | cons head tail ih =>
    obtain ⟨i, a⟩ := head
    simp only [integerSum, IntegerVector.toReal_add, IntegerVector.toReal_scale]
    exact .add (.scale a (Nat.cast_nonneg a) (.generator ⟨i, rfl⟩)) ih

theorem scale_unscale (d : ℝ) (hd : d ≠ 0) (v : ConeVector) :
    scale d⁻¹ (scale d v) = v := by
  ext <;> simp [scale, hd]

/-- Exact integer reconstruction with a positive denominator proves real cone membership. -/
theorem certificate_sound {n : ℕ} (g : Fin n → IntegerVector) (v : IntegerVector)
    (d : ℕ) (hd : 0 < d) (terms : List (Fin n × ℕ))
    (h : v.scale d = integerSum g terms) : GeneratedCone (generatorSet g) v.toReal := by
  have hm := integerSum_mem g terms
  rw [← h, IntegerVector.toReal_scale] at hm
  have hpos : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hs := GeneratedCone.scale (d : ℝ)⁻¹ (inv_nonneg.mpr hpos.le) hm
  rw [scale_unscale _ (ne_of_gt hpos)] at hs
  exact hs

structure CertificateData (n : ℕ) where
  denominator : ℕ
  terms : List (Fin n × ℕ)
def CertificateData.Valid {n : ℕ} (g : Fin n → IntegerVector)
    (v : IntegerVector) (cert : CertificateData n) : Prop :=
  0 < cert.denominator ∧ v.scale cert.denominator = integerSum g cert.terms
instance {n : ℕ} (g : Fin n → IntegerVector) (v : IntegerVector) (cert : CertificateData n) :
    Decidable (cert.Valid g v) := inferInstanceAs (Decidable (_ ∧ _))
theorem CertificateData.sound {n : ℕ} (g : Fin n → IntegerVector)
    (v : IntegerVector) (cert : CertificateData n) (h : cert.Valid g v) :
    GeneratedCone (generatorSet g) v.toReal :=
  certificate_sound g v cert.denominator h.1 cert.terms h.2

def IntegerVector.dot (u v : IntegerVector) : ℤ :=
  u.p * v.p + u.q * v.q + u.x * v.x + u.y * v.y
structure BasisData (n : ℕ) where
  denominator : ℕ
  rows : List (Fin n × IntegerVector)
inductive OperationRecord (n : ℕ) where
  | multiple (index : Fin n)
  | recession (index : Fin n)
  | basis (index : ℕ)
  | zero

def decodeCertificateUsing {n : ℕ} (g : Fin n → IntegerVector)
    (bases : ℕ → BasisData n) (rayX rayY : Fin n)
    (v : IntegerVector) : OperationRecord n → CertificateData n
  | .zero => ⟨1, []⟩
  | .multiple i =>
    ⟨1, [(i, v.p.natAbs.gcd (v.q.natAbs.gcd (v.x.natAbs.gcd v.y.natAbs)))]⟩
  | .recession i =>
    ⟨(g i).p.toNat, [(i, v.p.toNat),
      (rayX, (v.x * (g i).p - v.p * (g i).x).toNat),
      (rayY, (v.y * (g i).p - v.p * (g i).y).toNat)]⟩
  | .basis i =>
    let b := bases i
    ⟨b.denominator, b.rows.map (fun (j, w) => (j, (w.dot v).toNat))⟩

def decodeCertificate {n : ℕ} (g : Fin n → IntegerVector)
    (bases : Array (BasisData n)) (rayX rayY : Fin n)
    (v : IntegerVector) (r : OperationRecord n) : CertificateData n :=
  decodeCertificateUsing g (fun i => bases[i]?.getD ⟨1, []⟩) rayX rayY v r

end MeanMaximumForests
