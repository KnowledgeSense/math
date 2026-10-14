import Std

/-!
Finite binary vectors are encoded by natural numbers less than `2 ^ r`.
Vector addition is bitwise XOR; bit `j` is coordinate `j`.

A Hadamard row is encoded similarly, with a set bit representing `+1`.
The coordinate witnesses describe a basis of the dephased binary row space.
-/

namespace FugledeCertificates

def bit (word index : Nat) : Bool := Nat.testBit word index

def sign (word index : Nat) : Int := if bit word index then 1 else -1

def entry (rows : List Nat) (i j : Nat) : Int := sign (rows.getD i 0) j

def innerProduct (n : Nat) (rows : List Nat) (i j : Nat) : Int :=
  ((List.range n).map fun k => entry rows i k * entry rows j k).sum

def WithinBounds (r : Nat) (values : List Nat) : Prop :=
  ∀ i : Fin values.length, values.getD i.val 0 < 2 ^ r

instance (r : Nat) (values : List Nat) : Decidable (WithinBounds r values) :=
  inferInstanceAs (Decidable (∀ i : Fin values.length, values.getD i.val 0 < 2 ^ r))

/-- An `n × n` sign matrix with pairwise orthogonal rows. -/
def IsHadamard (n : Nat) (rows : List Nat) : Prop :=
  rows.length = n ∧ WithinBounds n rows ∧
  ∀ i : Fin n, ∀ j : Fin n,
    innerProduct n rows i.val j.val = if i = j then (n : Int) else 0

instance (n : Nat) (rows : List Nat) : Decidable (IsHadamard n rows) := by
  unfold IsHadamard
  infer_instance

def transposedRows (n : Nat) (rows : List Nat) : List Nat :=
  (List.range n).map fun j =>
    (List.range n).foldl
      (fun word i => word + if bit (rows.getD i 0) j then 2 ^ i else 0) 0

def orientedRows (n : Nat) (rows : List Nat) (transpose : Bool) : List Nat :=
  if transpose then transposedRows n rows else rows

/-- Normalize the first row and column to zero in the binary encoding. -/
def dephasedRows (n : Nat) (rows : List Nat) : List Nat :=
  rows.map fun word =>
    Nat.xor (Nat.xor word (rows.getD 0 0))
      (if bit word 0 != bit (rows.getD 0 0) 0 then 2 ^ n - 1 else 0)

def coordinateRows (n r : Nat) (points : List Nat) : List Nat :=
  (List.range r).map fun k =>
    (List.range n).foldl
      (fun word j => word + if bit (points.getD j 0) k then 2 ^ j else 0) 0

def linearCombination (rows : List Nat) (coefficients : Nat) : Nat :=
  (List.range rows.length).foldl
    (fun word i => if bit coefficients i then Nat.xor word (rows.getD i 0) else word) 0

/-- The zero vector has only the trivial binary linear combination. -/
def IndependentRows (r : Nat) (rows : List Nat) : Prop :=
  rows.length = r ∧
  ∀ coefficients : Fin (2 ^ r),
    linearCombination rows coefficients.val = 0 ↔ coefficients.val = 0

instance (r : Nat) (rows : List Nat) : Decidable (IndependentRows r rows) := by
  unfold IndependentRows
  infer_instance

def translationSums (points complement : List Nat) : List Nat :=
  points.flatMap fun point => complement.map fun shift => Nat.xor point shift

/-- Every vector occurs exactly once among the pairwise sums. -/
def Tiles (r : Nat) (points complement : List Nat) : Prop :=
  WithinBounds r points ∧ WithinBounds r complement ∧
  points.Nodup ∧ complement.Nodup ∧
  WithinBounds r (translationSums points complement) ∧
  ∀ x : Fin (2 ^ r), (translationSums points complement).count x.val = 1

instance (r : Nat) (points complement : List Nat) : Decidable (Tiles r points complement) := by
  unfold Tiles
  infer_instance

structure Certificate where
  rank : Nat
  points : List Nat
  complement : List Nat
  rowCoordinates : List Nat
  basisSourceMasks : List Nat

/-- An independent coordinate basis spanning exactly the dephased row space. -/
def CanonicalCoordinates (n : Nat) (rows : List Nat) (certificate : Certificate) : Prop :=
  let logarithmicRows := dephasedRows n rows
  let basis := coordinateRows n certificate.rank certificate.points
  certificate.points.length = n ∧
  certificate.rowCoordinates.length = n ∧
  certificate.basisSourceMasks.length = certificate.rank ∧
  WithinBounds certificate.rank certificate.rowCoordinates ∧
  WithinBounds n certificate.basisSourceMasks ∧
  IndependentRows certificate.rank basis ∧
  (∀ i : Fin n,
    linearCombination basis (certificate.rowCoordinates.getD i.val 0) =
      logarithmicRows.getD i.val 0) ∧
  (∀ k : Fin certificate.rank,
    linearCombination logarithmicRows (certificate.basisSourceMasks.getD k.val 0) =
      basis.getD k.val 0)

instance (n : Nat) (rows : List Nat) (certificate : Certificate) :
    Decidable (CanonicalCoordinates n rows certificate) := by
  unfold CanonicalCoordinates
  infer_instance

def ValidCertificate (n : Nat) (source : List Nat) (transpose : Bool)
    (certificate : Certificate) : Prop :=
  let rows := orientedRows n source transpose
  IsHadamard n rows ∧
  certificate.rank ≤ 7 ∧
  certificate.complement.length * n = 2 ^ certificate.rank ∧
  CanonicalCoordinates n rows certificate ∧
  Tiles certificate.rank certificate.points certificate.complement

instance (n : Nat) (source : List Nat) (transpose : Bool) (certificate : Certificate) :
    Decidable (ValidCertificate n source transpose certificate) := by
  unfold ValidCertificate
  infer_instance

theorem ValidCertificate.tiling {n : Nat} {source : List Nat} {transpose : Bool}
    {certificate : Certificate} (h : ValidCertificate n source transpose certificate) :
    Tiles certificate.rank certificate.points certificate.complement := by
  obtain ⟨_, _, _, _, tiling⟩ := h
  exact tiling

/-- A certificate together with its source representative and orientation. -/
structure HadamardCase where
  order : Nat
  classIndex : Nat
  transposed : Bool
  source : List Nat
  certificate : Certificate

def HadamardCase.Valid (c : HadamardCase) : Prop :=
  ValidCertificate c.order c.source c.transposed c.certificate

instance (c : HadamardCase) : Decidable c.Valid := by
  unfold HadamardCase.Valid
  infer_instance

end FugledeCertificates
