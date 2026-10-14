import FugledeCertificates

open FugledeCertificates FugledeCertificates.Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

-- Duplicate elements violate the tiling condition.
example : ¬ ValidCertificate 16 source16_1 false
    { order16_1 with complement := [0, 0] } := by decide

example : ¬ ValidCertificate 16 source16_1 false
    { order16_1 with points := 0 :: 0 :: order16_1.points.drop 2 } := by decide

-- An incorrect coordinate witness fails the row-space check.
example : ¬ ValidCertificate 16 source16_1 false
    { order16_1 with rowCoordinates := 1 :: order16_1.rowCoordinates.tail } := by decide

-- Flipping one matrix entry destroys Hadamard orthogonality.
example : ¬ ValidCertificate 16
    (Nat.xor (source16_1.getD 0 0) 1 :: source16_1.tail) false order16_1 := by decide
