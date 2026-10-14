import FugledeCertificates.Definitions

namespace FugledeCertificates

/-- The binary character `(-1)^(frequency · point)`. -/
def character (r frequency point : Nat) : Int :=
  if ((List.range r).filter fun k => bit (Nat.land frequency point) k).length % 2 = 0
  then 1 else -1

def walsh (r : Nat) (points : List Nat) (frequency : Nat) : Int :=
  (points.map fun point => character r frequency point).sum

/-- A character basis: equal cardinalities and pairwise Walsh orthogonality. -/
def IsSpectrum (r : Nat) (points frequencies : List Nat) : Prop :=
  WithinBounds r points ∧ WithinBounds r frequencies ∧
  points.Nodup ∧ frequencies.Nodup ∧ frequencies.length = points.length ∧
  ∀ i : Fin frequencies.length, ∀ j : Fin frequencies.length,
    i ≠ j → walsh r points
      (Nat.xor (frequencies.getD i.val 0) (frequencies.getD j.val 0)) = 0

instance (r : Nat) (points frequencies : List Nat) :
    Decidable (IsSpectrum r points frequencies) := by
  unfold IsSpectrum
  infer_instance

/-- Frequencies with nonzero Walsh sums at all pairwise differences. -/
def UniversalCandidate (r : Nat) (points frequencies : List Nat) : Prop :=
  WithinBounds r frequencies ∧ frequencies.Nodup ∧
  frequencies.length * points.length = 2 ^ r ∧
  ∀ i : Fin frequencies.length, ∀ j : Fin frequencies.length,
    i ≠ j → walsh r points
      (Nat.xor (frequencies.getD i.val 0) (frequencies.getD j.val 0)) ≠ 0

instance (r : Nat) (points frequencies : List Nat) :
    Decidable (UniversalCandidate r points frequencies) := by
  unfold UniversalCandidate
  infer_instance

structure EightCertificate where
  rank : Nat
  points : List Nat
  complement : List Nat
  spectrum : List Nat
  universalFrequencies : List Nat

def ValidEightCertificate (certificate : EightCertificate) : Prop :=
  certificate.points.length = 8 ∧ certificate.rank ≤ 7 ∧
  Tiles certificate.rank certificate.points certificate.complement ∧
  IsSpectrum certificate.rank certificate.points certificate.spectrum ∧
  UniversalCandidate certificate.rank certificate.points certificate.universalFrequencies

instance (certificate : EightCertificate) : Decidable (ValidEightCertificate certificate) := by
  unfold ValidEightCertificate
  infer_instance

theorem ValidEightCertificate.tiling {c : EightCertificate} (h : ValidEightCertificate c) :
    Tiles c.rank c.points c.complement := by
  obtain ⟨_, _, tiling, _, _⟩ := h
  exact tiling

theorem ValidEightCertificate.spectral {c : EightCertificate} (h : ValidEightCertificate c) :
    IsSpectrum c.rank c.points c.spectrum := by
  obtain ⟨_, _, _, spectral, _⟩ := h
  exact spectral

end FugledeCertificates

