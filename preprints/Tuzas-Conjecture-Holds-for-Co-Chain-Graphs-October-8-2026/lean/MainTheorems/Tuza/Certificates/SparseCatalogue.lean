import MainTheorems.Tuza.SparseCertificates
import MainTheorems.Tuza.Certificates.Sparse
import MainTheorems.Tuza.Certificates.Additional

namespace ResearchMain.Tuza.Certificates

def sparseCertificates : (a b : ℕ) → List (SparseCertificate a b)
  | 3, 8 => [
      {
        x := 0
        y := 3
        profile := canonical_sparse_3_8_0_3_profile
        rows := by decide
        size := 10
        packed := by
          have h := packing_le_number canonical_sparse_3_8_0_3_verified.1
          rwa [canonical_sparse_3_8_0_3_verified.2] at h
      },
      {
        x := 1
        y := 2
        profile := canonical_sparse_3_8_1_2_profile
        rows := by decide
        size := 10
        packed := by
          have h := packing_le_number canonical_sparse_3_8_1_2_verified.1
          rwa [canonical_sparse_3_8_1_2_verified.2] at h
      }]
  | 5, 6 => [
      {
        x := 0
        y := 2
        profile := canonical_sparse_5_6_0_2_profile
        rows := by decide
        size := 8
        packed := by
          have h := packing_le_number canonical_sparse_5_6_0_2_verified.1
          rwa [canonical_sparse_5_6_0_2_verified.2] at h
      },
      {
        x := 1
        y := 1
        profile := canonical_sparse_5_6_1_1_profile
        rows := by decide
        size := 8
        packed := by
          have h := packing_le_number canonical_sparse_5_6_1_1_verified.1
          rwa [canonical_sparse_5_6_1_1_verified.2] at h
      },
      {
        x := 1
        y := 2
        profile := canonical_sparse_5_6_1_2_profile
        rows := by decide
        size := 9
        packed := by
          have h := packing_le_number canonical_sparse_5_6_1_2_verified.1
          rwa [canonical_sparse_5_6_1_2_verified.2] at h
      },
      {
        x := 2
        y := 0
        profile := canonical_sparse_5_6_2_0_profile
        rows := by decide
        size := 8
        packed := by
          have h := packing_le_number canonical_sparse_5_6_2_0_verified.1
          rwa [canonical_sparse_5_6_2_0_verified.2] at h
      },
      {
        x := 2
        y := 1
        profile := canonical_sparse_5_6_2_1_profile
        rows := by decide
        size := 9
        packed := by
          have h := packing_le_number canonical_sparse_5_6_2_1_verified.1
          rwa [canonical_sparse_5_6_2_1_verified.2] at h
      },
      {
        x := 2
        y := 2
        profile := canonical_sparse_5_6_2_2_profile
        rows := by decide
        size := 9
        packed := by
          have h := packing_le_number canonical_sparse_5_6_2_2_verified.1
          rwa [canonical_sparse_5_6_2_2_verified.2] at h
      }]
  | 5, 7 => [
      {
        x := 1
        y := 2
        profile := canonical_sparse_5_7_1_2_profile
        rows := by decide
        size := 11
        packed := by
          have h := packing_le_number canonical_sparse_5_7_1_2_verified.1
          rwa [canonical_sparse_5_7_1_2_verified.2] at h
      },
      {
        x := 1
        y := 3
        profile := canonical_sparse_5_7_1_3_profile
        rows := by decide
        size := 12
        packed := by
          have h := packing_le_number canonical_sparse_5_7_1_3_verified.1
          rwa [canonical_sparse_5_7_1_3_verified.2] at h
      },
      {
        x := 2
        y := 0
        profile := canonical_sparse_5_7_2_0_profile
        rows := by decide
        size := 11
        packed := by
          have h := packing_le_number canonical_sparse_5_7_2_0_verified.1
          rwa [canonical_sparse_5_7_2_0_verified.2] at h
      },
      {
        x := 2
        y := 1
        profile := canonical_sparse_5_7_2_1_profile
        rows := by decide
        size := 11
        packed := by
          have h := packing_le_number canonical_sparse_5_7_2_1_verified.1
          rwa [canonical_sparse_5_7_2_1_verified.2] at h
      },
      {
        x := 2
        y := 2
        profile := canonical_sparse_5_7_2_2_profile
        rows := by decide
        size := 12
        packed := by
          have h := packing_le_number canonical_sparse_5_7_2_2_verified.1
          rwa [canonical_sparse_5_7_2_2_verified.2] at h
      },
      {
        x := 2
        y := 3
        profile := canonical_sparse_5_7_2_3_profile
        rows := by decide
        size := 12
        packed := by
          have h := packing_le_number canonical_sparse_5_7_2_3_verified.1
          rwa [canonical_sparse_5_7_2_3_verified.2] at h
      }]
  | 5, 8 => [
      {
        x := 0
        y := 3
        profile := canonical_sparse_5_8_0_3_profile
        rows := by decide
        size := 13
        packed := by
          have h := packing_le_number canonical_sparse_5_8_0_3_verified.1
          rwa [canonical_sparse_5_8_0_3_verified.2] at h
      },
      {
        x := 1
        y := 2
        profile := canonical_sparse_5_8_1_2_profile
        rows := by decide
        size := 12
        packed := by
          have h := packing_le_number canonical_sparse_5_8_1_2_verified.1
          rwa [canonical_sparse_5_8_1_2_verified.2] at h
      },
      {
        x := 2
        y := 1
        profile := canonical_sparse_5_8_2_1_profile
        rows := by decide
        size := 13
        packed := by
          have h := packing_le_number canonical_sparse_5_8_2_1_verified.1
          rwa [canonical_sparse_5_8_2_1_verified.2] at h
      },
      {
        x := 2
        y := 3
        profile := canonical_sparse_5_8_2_3_profile
        rows := by decide
        size := 14
        packed := by
          have h := packing_le_number canonical_sparse_5_8_2_3_verified.1
          rwa [canonical_sparse_5_8_2_3_verified.2] at h
      },
      {
        x := 1
        y := 3
        profile := sparse_5_8_1_3_profile
        rows := by decide
        size := 13
        packed := by
          have h := packing_le_number sparse_5_8_1_3_verified.1
          rwa [sparse_5_8_1_3_verified.2] at h
      },
      {
        x := 2
        y := 2
        profile := sparse_5_8_2_2_profile
        rows := by decide
        size := 13
        packed := by
          have h := packing_le_number sparse_5_8_2_2_verified.1
          rwa [sparse_5_8_2_2_verified.2] at h
      }]
  | 5, 9 => [
      {
        x := 1
        y := 4
        profile := canonical_sparse_5_9_1_4_profile
        rows := by decide
        size := 17
        packed := by
          have h := packing_le_number canonical_sparse_5_9_1_4_verified.1
          rwa [canonical_sparse_5_9_1_4_verified.2] at h
      },
      {
        x := 2
        y := 1
        profile := canonical_sparse_5_9_2_1_profile
        rows := by decide
        size := 16
        packed := by
          have h := packing_le_number canonical_sparse_5_9_2_1_verified.1
          rwa [canonical_sparse_5_9_2_1_verified.2] at h
      },
      {
        x := 2
        y := 2
        profile := canonical_sparse_5_9_2_2_profile
        rows := by decide
        size := 16
        packed := by
          have h := packing_le_number canonical_sparse_5_9_2_2_verified.1
          rwa [canonical_sparse_5_9_2_2_verified.2] at h
      },
      {
        x := 2
        y := 3
        profile := canonical_sparse_5_9_2_3_profile
        rows := by decide
        size := 17
        packed := by
          have h := packing_le_number canonical_sparse_5_9_2_3_verified.1
          rwa [canonical_sparse_5_9_2_3_verified.2] at h
      },
      {
        x := 2
        y := 4
        profile := canonical_sparse_5_9_2_4_profile
        rows := by decide
        size := 17
        packed := by
          have h := packing_le_number canonical_sparse_5_9_2_4_verified.1
          rwa [canonical_sparse_5_9_2_4_verified.2] at h
      }]
  | 5, 10 => [
      {
        x := 1
        y := 2
        profile := canonical_sparse_5_10_1_2_profile
        rows := by decide
        size := 17
        packed := by
          have h := packing_le_number canonical_sparse_5_10_1_2_verified.1
          rwa [canonical_sparse_5_10_1_2_verified.2] at h
      },
      {
        x := 1
        y := 3
        profile := canonical_sparse_5_10_1_3_profile
        rows := by decide
        size := 18
        packed := by
          have h := packing_le_number canonical_sparse_5_10_1_3_verified.1
          rwa [canonical_sparse_5_10_1_3_verified.2] at h
      }]
  | 5, 11 => [
      {
        x := 1
        y := 4
        profile := canonical_sparse_5_11_1_4_profile
        rows := by decide
        size := 22
        packed := by
          have h := packing_le_number canonical_sparse_5_11_1_4_verified.1
          rwa [canonical_sparse_5_11_1_4_verified.2] at h
      }]
  | 5, 12 => [
      {
        x := 0
        y := 5
        profile := sparse_5_12_0_5_profile
        rows := by decide
        size := 25
        packed := by
          have h := packing_le_number sparse_5_12_0_5_verified.1
          rwa [sparse_5_12_0_5_verified.2] at h
      },
      {
        x := 1
        y := 5
        profile := sparse_5_12_1_5_profile
        rows := by decide
        size := 25
        packed := by
          have h := packing_le_number sparse_5_12_1_5_verified.1
          rwa [sparse_5_12_1_5_verified.2] at h
      },
      {
        x := 2
        y := 5
        profile := sparse_5_12_2_5_profile
        rows := by decide
        size := 26
        packed := by
          have h := packing_le_number sparse_5_12_2_5_verified.1
          rwa [sparse_5_12_2_5_verified.2] at h
      }]
  | 6, 7 => [
      {
        x := 2
        y := 2
        profile := canonical_sparse_6_7_2_2_profile
        rows := by decide
        size := 13
        packed := by
          have h := packing_le_number canonical_sparse_6_7_2_2_verified.1
          rwa [canonical_sparse_6_7_2_2_verified.2] at h
      }]
  | 6, 8 => [
      {
        x := 2
        y := 3
        profile := sparse_6_8_2_3_profile
        rows := by decide
        size := 15
        packed := by
          have h := packing_le_number sparse_6_8_2_3_verified.1
          rwa [sparse_6_8_2_3_verified.2] at h
      }]
  | 7, 7 => [
      {
        x := 3
        y := 3
        profile := canonical_sparse_7_7_3_3_profile
        rows := by decide
        size := 17
        packed := by
          have h := packing_le_number canonical_sparse_7_7_3_3_verified.1
          rwa [canonical_sparse_7_7_3_3_verified.2] at h
      }]
  | 7, 8 => [
      {
        x := 2
        y := 3
        profile := canonical_sparse_7_8_2_3_profile
        rows := by decide
        size := 18
        packed := by
          have h := packing_le_number canonical_sparse_7_8_2_3_verified.1
          rwa [canonical_sparse_7_8_2_3_verified.2] at h
      }]
  | 7, 9 => [
      {
        x := 2
        y := 4
        profile := canonical_sparse_7_9_2_4_profile
        rows := by decide
        size := 22
        packed := by
          have h := packing_le_number canonical_sparse_7_9_2_4_verified.1
          rwa [canonical_sparse_7_9_2_4_verified.2] at h
      },
      {
        x := 3
        y := 3
        profile := canonical_sparse_7_9_3_3_profile
        rows := by decide
        size := 22
        packed := by
          have h := packing_le_number canonical_sparse_7_9_3_3_verified.1
          rwa [canonical_sparse_7_9_3_3_verified.2] at h
      },
      {
        x := 3
        y := 4
        profile := canonical_sparse_7_9_3_4_profile
        rows := by decide
        size := 22
        packed := by
          have h := packing_le_number canonical_sparse_7_9_3_4_verified.1
          rwa [canonical_sparse_7_9_3_4_verified.2] at h
      }]
  | 7, 11 => [
      {
        x := 2
        y := 4
        profile := canonical_sparse_7_11_2_4_profile
        rows := by decide
        size := 27
        packed := by
          have h := packing_le_number canonical_sparse_7_11_2_4_verified.1
          rwa [canonical_sparse_7_11_2_4_verified.2] at h
      }]
  | 7, 12 => [
      {
        x := 2
        y := 5
        profile := canonical_sparse_7_12_2_5_profile
        rows := by decide
        size := 31
        packed := by
          have h := packing_le_number canonical_sparse_7_12_2_5_verified.1
          rwa [canonical_sparse_7_12_2_5_verified.2] at h
      },
      {
        x := 2
        y := 4
        profile := sparse_7_12_2_4_profile
        rows := by decide
        size := 30
        packed := by
          have h := packing_le_number sparse_7_12_2_4_verified.1
          rwa [sparse_7_12_2_4_verified.2] at h
      }]
  | 7, 14 => [
      {
        x := 2
        y := 5
        profile := canonical_sparse_7_14_2_5_profile
        rows := by decide
        size := 38
        packed := by
          have h := packing_le_number canonical_sparse_7_14_2_5_verified.1
          rwa [canonical_sparse_7_14_2_5_verified.2] at h
      }]
  | 8, 9 => [
      {
        x := 3
        y := 2
        profile := canonical_sparse_8_9_3_2_profile
        rows := by decide
        size := 23
        packed := by
          have h := packing_le_number canonical_sparse_8_9_3_2_verified.1
          rwa [canonical_sparse_8_9_3_2_verified.2] at h
      }]
  | 8, 11 => [
      {
        x := 3
        y := 4
        profile := canonical_sparse_8_11_3_4_profile
        rows := by decide
        size := 30
        packed := by
          have h := packing_le_number canonical_sparse_8_11_3_4_verified.1
          rwa [canonical_sparse_8_11_3_4_verified.2] at h
      }]
  | 9, 9 => [
      {
        x := 1
        y := 4
        profile := canonical_sparse_9_9_1_4_profile
        rows := by decide
        size := 27
        packed := by
          have h := packing_le_number canonical_sparse_9_9_1_4_verified.1
          rwa [canonical_sparse_9_9_1_4_verified.2] at h
      },
      {
        x := 2
        y := 4
        profile := canonical_sparse_9_9_2_4_profile
        rows := by decide
        size := 27
        packed := by
          have h := packing_le_number canonical_sparse_9_9_2_4_verified.1
          rwa [canonical_sparse_9_9_2_4_verified.2] at h
      },
      {
        x := 3
        y := 3
        profile := canonical_sparse_9_9_3_3_profile
        rows := by decide
        size := 27
        packed := by
          have h := packing_le_number canonical_sparse_9_9_3_3_verified.1
          rwa [canonical_sparse_9_9_3_3_verified.2] at h
      },
      {
        x := 3
        y := 4
        profile := canonical_sparse_9_9_3_4_profile
        rows := by decide
        size := 28
        packed := by
          have h := packing_le_number canonical_sparse_9_9_3_4_verified.1
          rwa [canonical_sparse_9_9_3_4_verified.2] at h
      },
      {
        x := 4
        y := 1
        profile := canonical_sparse_9_9_4_1_profile
        rows := by decide
        size := 27
        packed := by
          have h := packing_le_number canonical_sparse_9_9_4_1_verified.1
          rwa [canonical_sparse_9_9_4_1_verified.2] at h
      },
      {
        x := 4
        y := 2
        profile := canonical_sparse_9_9_4_2_profile
        rows := by decide
        size := 27
        packed := by
          have h := packing_le_number canonical_sparse_9_9_4_2_verified.1
          rwa [canonical_sparse_9_9_4_2_verified.2] at h
      },
      {
        x := 4
        y := 3
        profile := canonical_sparse_9_9_4_3_profile
        rows := by decide
        size := 28
        packed := by
          have h := packing_le_number canonical_sparse_9_9_4_3_verified.1
          rwa [canonical_sparse_9_9_4_3_verified.2] at h
      },
      {
        x := 4
        y := 4
        profile := canonical_sparse_9_9_4_4_profile
        rows := by decide
        size := 28
        packed := by
          have h := packing_le_number canonical_sparse_9_9_4_4_verified.1
          rwa [canonical_sparse_9_9_4_4_verified.2] at h
      }]
  | 9, 11 => [
      {
        x := 1
        y := 4
        profile := canonical_sparse_9_11_1_4_profile
        rows := by decide
        size := 32
        packed := by
          have h := packing_le_number canonical_sparse_9_11_1_4_verified.1
          rwa [canonical_sparse_9_11_1_4_verified.2] at h
      },
      {
        x := 2
        y := 4
        profile := canonical_sparse_9_11_2_4_profile
        rows := by decide
        size := 33
        packed := by
          have h := packing_le_number canonical_sparse_9_11_2_4_verified.1
          rwa [canonical_sparse_9_11_2_4_verified.2] at h
      },
      {
        x := 3
        y := 4
        profile := canonical_sparse_9_11_3_4_profile
        rows := by decide
        size := 34
        packed := by
          have h := packing_le_number canonical_sparse_9_11_3_4_verified.1
          rwa [canonical_sparse_9_11_3_4_verified.2] at h
      }]
  | 9, 12 => [
      {
        x := 2
        y := 4
        profile := sparse_9_12_2_4_profile
        rows := by decide
        size := 35
        packed := by
          have h := packing_le_number sparse_9_12_2_4_verified.1
          rwa [sparse_9_12_2_4_verified.2] at h
      }]
  | 9, 13 => [
      {
        x := 3
        y := 4
        profile := canonical_sparse_9_13_3_4_profile
        rows := by decide
        size := 41
        packed := by
          have h := packing_le_number canonical_sparse_9_13_3_4_verified.1
          rwa [canonical_sparse_9_13_3_4_verified.2] at h
      },
      {
        x := 4
        y := 5
        profile := canonical_sparse_9_13_4_5_profile
        rows := by decide
        size := 43
        packed := by
          have h := packing_le_number canonical_sparse_9_13_4_5_verified.1
          rwa [canonical_sparse_9_13_4_5_verified.2] at h
      }]
  | 10, 11 => [
      {
        x := 3
        y := 4
        profile := canonical_sparse_10_11_3_4_profile
        rows := by decide
        size := 36
        packed := by
          have h := packing_le_number canonical_sparse_10_11_3_4_verified.1
          rwa [canonical_sparse_10_11_3_4_verified.2] at h
      }]
  | 11, 11 => [
      {
        x := 3
        y := 3
        profile := canonical_sparse_11_11_3_3_profile
        rows := by decide
        size := 39
        packed := by
          have h := packing_le_number canonical_sparse_11_11_3_3_verified.1
          rwa [canonical_sparse_11_11_3_3_verified.2] at h
      },
      {
        x := 4
        y := 4
        profile := canonical_sparse_11_11_4_4_profile
        rows := by decide
        size := 41
        packed := by
          have h := packing_le_number canonical_sparse_11_11_4_4_verified.1
          rwa [canonical_sparse_11_11_4_4_verified.2] at h
      },
      {
        x := 5
        y := 5
        profile := canonical_sparse_11_11_5_5_profile
        rows := by decide
        size := 43
        packed := by
          have h := packing_le_number canonical_sparse_11_11_5_5_verified.1
          rwa [canonical_sparse_11_11_5_5_verified.2] at h
      }]
  | 11, 13 => [
      {
        x := 4
        y := 3
        profile := canonical_sparse_11_13_4_3_profile
        rows := by decide
        size := 48
        packed := by
          have h := packing_le_number canonical_sparse_11_13_4_3_verified.1
          rwa [canonical_sparse_11_13_4_3_verified.2] at h
      }]
  | 11, 16 => [
      {
        x := 4
        y := 6
        profile := canonical_sparse_11_16_4_6_profile
        rows := by decide
        size := 63
        packed := by
          have h := packing_le_number canonical_sparse_11_16_4_6_verified.1
          rwa [canonical_sparse_11_16_4_6_verified.2] at h
      }]
  | 13, 13 => [
      {
        x := 5
        y := 6
        profile := canonical_sparse_13_13_5_6_profile
        rows := by decide
        size := 60
        packed := by
          have h := packing_le_number canonical_sparse_13_13_5_6_verified.1
          rwa [canonical_sparse_13_13_5_6_verified.2] at h
      },
      {
        x := 6
        y := 5
        profile := canonical_sparse_13_13_6_5_profile
        rows := by decide
        size := 60
        packed := by
          have h := packing_le_number canonical_sparse_13_13_6_5_verified.1
          rwa [canonical_sparse_13_13_6_5_verified.2] at h
      },
      {
        x := 6
        y := 6
        profile := canonical_sparse_13_13_6_6_profile
        rows := by decide
        size := 60
        packed := by
          have h := packing_le_number canonical_sparse_13_13_6_6_verified.1
          rwa [canonical_sparse_13_13_6_6_verified.2] at h
      }]
  | 13, 17 => [
      {
        x := 5
        y := 6
        profile := canonical_sparse_13_17_5_6_profile
        rows := by decide
        size := 79
        packed := by
          have h := packing_le_number canonical_sparse_13_17_5_6_verified.1
          rwa [canonical_sparse_13_17_5_6_verified.2] at h
      }]
  | 17, 17 => [
      {
        x := 5
        y := 5
        profile := canonical_sparse_17_17_5_5_profile
        rows := by decide
        size := 97
        packed := by
          have h := packing_le_number canonical_sparse_17_17_5_5_verified.1
          rwa [canonical_sparse_17_17_5_5_verified.2] at h
      }]
  | _, _ => []

end ResearchMain.Tuza.Certificates
