import MainTheorems.Tuza.DenseCertificates
import MainTheorems.Tuza.Certificates.Dense
import MainTheorems.Tuza.Certificates.Additional

namespace ResearchMain.Tuza.Certificates

def denseRecord_5_9_3_5_0 : DenseCertificate 5 9 where
  x := 3
  y := 5
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 3 5 hx hy he canonical_dense_5_9_3_5_0_profile (by decide) 18
    · have hp := packing_le_number canonical_dense_5_9_3_5_0_verified.1
      rwa [canonical_dense_5_9_3_5_0_verified.2] at hp
    · exact (show denseCoverBase 5 9 ≤ 2 * 18 from by decide)

def denseRecord_5_9_3_6_0 : DenseCertificate 5 9 where
  x := 3
  y := 6
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 3 6 hx hy he canonical_dense_5_9_3_6_0_profile (by decide) 18
    · have hp := packing_le_number canonical_dense_5_9_3_6_0_verified.1
      rwa [canonical_dense_5_9_3_6_0_verified.2] at hp
    · exact (show denseCoverBase 5 9 ≤ 2 * 18 from by decide)

def denseRecord_5_9_3_7_0 : DenseCertificate 5 9 where
  x := 3
  y := 7
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 3 7 hx hy he canonical_dense_5_9_3_7_0_profile (by decide) 18
    · have hp := packing_le_number canonical_dense_5_9_3_7_0_verified.1
      rwa [canonical_dense_5_9_3_7_0_verified.2] at hp
    · exact (show denseCoverBase 5 9 ≤ 2 * 18 from by decide)

def denseRecord_5_9_4_7_2 : DenseCertificate 5 9 where
  x := 4
  y := 7
  e := 2
  correct := by
    intro d ha hd hx hy he
    apply d.dense_full_certificate ha hd 4 7 hx hy he canonical_dense_5_9_4_7_2_7_profile (by decide) 19
    · have hp := packing_le_number canonical_dense_5_9_4_7_2_7_verified.1
      rwa [canonical_dense_5_9_4_7_2_7_verified.2] at hp
    · exact (show denseCoverBase 5 9 + (4 - halfUp 5) * (7 - halfUp 9) ≤ 2 * 19 from by decide)

def denseRecord_6_7_3_4_0 : DenseCertificate 6 7 where
  x := 3
  y := 4
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 3 4 hx hy he canonical_dense_6_7_3_4_0_profile (by decide) 14
    · have hp := packing_le_number canonical_dense_6_7_3_4_0_verified.1
      rwa [canonical_dense_6_7_3_4_0_verified.2] at hp
    · exact (show denseCoverBase 6 7 ≤ 2 * 14 from by decide)

def denseRecord_6_7_3_5_0 : DenseCertificate 6 7 where
  x := 3
  y := 5
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 3 5 hx hy he canonical_dense_6_7_3_5_0_profile (by decide) 14
    · have hp := packing_le_number canonical_dense_6_7_3_5_0_verified.1
      rwa [canonical_dense_6_7_3_5_0_verified.2] at hp
    · exact (show denseCoverBase 6 7 ≤ 2 * 14 from by decide)

def denseRecord_6_9_3_5_0 : DenseCertificate 6 9 where
  x := 3
  y := 5
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 3 5 hx hy he canonical_dense_6_9_3_5_0_profile (by decide) 19
    · have hp := packing_le_number canonical_dense_6_9_3_5_0_verified.1
      rwa [canonical_dense_6_9_3_5_0_verified.2] at hp
    · exact (show denseCoverBase 6 9 ≤ 2 * 19 from by decide)

def denseRecord_6_9_3_6_0 : DenseCertificate 6 9 where
  x := 3
  y := 6
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 3 6 hx hy he canonical_dense_6_9_3_6_0_profile (by decide) 19
    · have hp := packing_le_number canonical_dense_6_9_3_6_0_verified.1
      rwa [canonical_dense_6_9_3_6_0_verified.2] at hp
    · exact (show denseCoverBase 6 9 ≤ 2 * 19 from by decide)

def denseRecord_6_9_3_7_0 : DenseCertificate 6 9 where
  x := 3
  y := 7
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 3 7 hx hy he canonical_dense_6_9_3_7_0_profile (by decide) 19
    · have hp := packing_le_number canonical_dense_6_9_3_7_0_verified.1
      rwa [canonical_dense_6_9_3_7_0_verified.2] at hp
    · exact (show denseCoverBase 6 9 ≤ 2 * 19 from by decide)

def denseRecord_6_9_4_7_2 : DenseCertificate 6 9 where
  x := 4
  y := 7
  e := 2
  correct := by
    intro d ha hd hx hy he
    apply d.dense_full_certificate ha hd 4 7 hx hy he canonical_dense_6_9_4_7_2_7_profile (by decide) 20
    · have hp := packing_le_number canonical_dense_6_9_4_7_2_7_verified.1
      rwa [canonical_dense_6_9_4_7_2_7_verified.2] at hp
    · exact (show denseCoverBase 6 9 + (4 - halfUp 6) * (7 - halfUp 9) ≤ 2 * 20 from by decide)

def denseRecord_7_7_4_4_0 : DenseCertificate 7 7 where
  x := 4
  y := 4
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 4 4 hx hy he canonical_dense_7_7_4_4_0_profile (by decide) 17
    · have hp := packing_le_number canonical_dense_7_7_4_4_0_verified.1
      rwa [canonical_dense_7_7_4_4_0_verified.2] at hp
    · exact (show denseCoverBase 7 7 ≤ 2 * 17 from by decide)

def denseRecord_7_7_4_5_0 : DenseCertificate 7 7 where
  x := 4
  y := 5
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 4 5 hx hy he canonical_dense_7_7_4_5_0_profile (by decide) 17
    · have hp := packing_le_number canonical_dense_7_7_4_5_0_verified.1
      rwa [canonical_dense_7_7_4_5_0_verified.2] at hp
    · exact (show denseCoverBase 7 7 ≤ 2 * 17 from by decide)

def denseRecord_7_7_5_4_0 : DenseCertificate 7 7 where
  x := 5
  y := 4
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 5 4 hx hy he canonical_dense_7_7_5_4_0_4_profile (by decide) 17
    · have hp := packing_le_number canonical_dense_7_7_5_4_0_4_verified.1
      rwa [canonical_dense_7_7_5_4_0_4_verified.2] at hp
    · exact (show denseCoverBase 7 7 ≤ 2 * 17 from by decide)

def denseRecord_7_7_5_5_0 : DenseCertificate 7 7 where
  x := 5
  y := 5
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 5 5 hx hy he canonical_dense_7_7_5_5_0_4_profile (by decide) 17
    · have hp := packing_le_number canonical_dense_7_7_5_5_0_4_verified.1
      rwa [canonical_dense_7_7_5_5_0_4_verified.2] at hp
    · exact (show denseCoverBase 7 7 ≤ 2 * 17 from by decide)

def denseRecord_7_7_5_5_1 : DenseCertificate 7 7 where
  x := 5
  y := 5
  e := 1
  correct := by
    intro d ha hd hx hy he
    apply d.dense_full_certificate ha hd 5 5 hx hy he canonical_dense_7_7_5_5_1_5_profile (by decide) 18
    · have hp := packing_le_number canonical_dense_7_7_5_5_1_5_verified.1
      rwa [canonical_dense_7_7_5_5_1_5_verified.2] at hp
    · exact (show denseCoverBase 7 7 + (5 - halfUp 7) * (5 - halfUp 7) ≤ 2 * 18 from by decide)

def denseRecord_7_9_4_5_0 : DenseCertificate 7 9 where
  x := 4
  y := 5
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 4 5 hx hy he canonical_dense_7_9_4_5_0_profile (by decide) 23
    · have hp := packing_le_number canonical_dense_7_9_4_5_0_verified.1
      rwa [canonical_dense_7_9_4_5_0_verified.2] at hp
    · exact (show denseCoverBase 7 9 ≤ 2 * 23 from by decide)

def denseRecord_7_9_4_6_0 : DenseCertificate 7 9 where
  x := 4
  y := 6
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 4 6 hx hy he canonical_dense_7_9_4_6_0_profile (by decide) 23
    · have hp := packing_le_number canonical_dense_7_9_4_6_0_verified.1
      rwa [canonical_dense_7_9_4_6_0_verified.2] at hp
    · exact (show denseCoverBase 7 9 ≤ 2 * 23 from by decide)

def denseRecord_7_9_4_7_0 : DenseCertificate 7 9 where
  x := 4
  y := 7
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 4 7 hx hy he canonical_dense_7_9_4_7_0_profile (by decide) 23
    · have hp := packing_le_number canonical_dense_7_9_4_7_0_verified.1
      rwa [canonical_dense_7_9_4_7_0_verified.2] at hp
    · exact (show denseCoverBase 7 9 ≤ 2 * 23 from by decide)

def denseRecord_7_9_5_7_2 : DenseCertificate 7 9 where
  x := 5
  y := 7
  e := 2
  correct := by
    intro d ha hd hx hy he
    apply d.dense_full_certificate ha hd 5 7 hx hy he canonical_dense_7_9_5_7_2_7_profile (by decide) 24
    · have hp := packing_le_number canonical_dense_7_9_5_7_2_7_verified.1
      rwa [canonical_dense_7_9_5_7_2_7_verified.2] at hp
    · exact (show denseCoverBase 7 9 + (5 - halfUp 7) * (7 - halfUp 9) ≤ 2 * 24 from by decide)

def denseRecord_9_9_5_5_0 : DenseCertificate 9 9 where
  x := 5
  y := 5
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 5 5 hx hy he canonical_dense_9_9_5_5_0_profile (by decide) 29
    · have hp := packing_le_number canonical_dense_9_9_5_5_0_verified.1
      rwa [canonical_dense_9_9_5_5_0_verified.2] at hp
    · exact (show denseCoverBase 9 9 ≤ 2 * 29 from by decide)

def denseRecord_9_9_7_7_4 : DenseCertificate 9 9 where
  x := 7
  y := 7
  e := 4
  correct := by
    intro d ha hd hx hy he
    apply d.dense_full_certificate ha hd 7 7 hx hy he canonical_dense_9_9_7_7_4_7_7_profile (by decide) 31
    · have hp := packing_le_number canonical_dense_9_9_7_7_4_7_7_verified.1
      rwa [canonical_dense_9_9_7_7_4_7_7_verified.2] at hp
    · exact (show denseCoverBase 9 9 + (7 - halfUp 9) * (7 - halfUp 9) ≤ 2 * 31 from by decide)

def denseRecord_9_11_7_9_4 : DenseCertificate 9 11 where
  x := 7
  y := 9
  e := 4
  correct := by
    intro d ha hd hx hy he
    have hw : d.height (halfUp 11) - halfUp 9 = 2 := by rw [hx]; rfl
    have hz : d.medianDegree ha - halfUp 11 = 3 := by rw [hy]; rfl
    have hsum := (d.lowerShape_sum ha hd).trans he
    rcases shape_two_three_cases (d.lowerShape ha hd) hw hz hsum with hs | hs
    · have hg : dense_9_11_7_9_4_3_1_profile.graph ≤ d.graph := by
        apply d.dense_pattern_graph_le_of_shape ha hd dense_9_11_7_9_4_3_1_profile (fun k => if k = 0 then 3 else 1) hs
        · intro i hi
          rw [hy]
          exact (show ∀ i : Fin 9, i.val < halfUp 9 → dense_9_11_7_9_4_3_1_profile.degree i ≤ 9
            from by decide) i hi
        · intro i hi
          rw [hx] at hi
          exact (show ∀ i : Fin 9, 7 ≤ i.val → dense_9_11_7_9_4_3_1_profile.degree i = 0
            from by decide) i hi
        · intro i hir hix
          rw [hx] at hix
          exact (show ∀ i : Fin 9, halfUp 9 ≤ i.val → i.val < 7 →
              dense_9_11_7_9_4_3_1_profile.degree i ≤ halfUp 11 + (fun k => if k = 0 then 3 else 1) (i.val - halfUp 9)
            from by decide) i hir hix
      have hp := packing_le_number dense_9_11_7_9_4_3_1_verified.1
      rw [dense_9_11_7_9_4_3_1_verified.2] at hp
      have hc := d.dense_cover_base_bound hd
      rw [he] at hc
      have hf : denseCoverBase 9 11 + 4 ≤ 2 * 38 := by decide
      exact hc.trans (hf.trans (Nat.mul_le_mul_left 2 (hp.trans (packingNumber_mono hg))))
    · have hg : dense_9_11_7_9_4_2_2_profile.graph ≤ d.graph := by
        apply d.dense_pattern_graph_le_of_shape ha hd dense_9_11_7_9_4_2_2_profile (fun _ => 2) hs
        · intro i hi
          rw [hy]
          exact (show ∀ i : Fin 9, i.val < halfUp 9 → dense_9_11_7_9_4_2_2_profile.degree i ≤ 9
            from by decide) i hi
        · intro i hi
          rw [hx] at hi
          exact (show ∀ i : Fin 9, 7 ≤ i.val → dense_9_11_7_9_4_2_2_profile.degree i = 0
            from by decide) i hi
        · intro i hir hix
          rw [hx] at hix
          exact (show ∀ i : Fin 9, halfUp 9 ≤ i.val → i.val < 7 →
              dense_9_11_7_9_4_2_2_profile.degree i ≤ halfUp 11 + (fun _ => 2) (i.val - halfUp 9)
            from by decide) i hir hix
      have hp := packing_le_number dense_9_11_7_9_4_2_2_verified.1
      rw [dense_9_11_7_9_4_2_2_verified.2] at hp
      have hc := d.dense_cover_base_bound hd
      rw [he] at hc
      have hf : denseCoverBase 9 11 + 4 ≤ 2 * 38 := by decide
      exact hc.trans (hf.trans (Nat.mul_le_mul_left 2 (hp.trans (packingNumber_mono hg))))

def denseRecord_10_10_7_7_4 : DenseCertificate 10 10 where
  x := 7
  y := 7
  e := 4
  correct := by
    intro d ha hd hx hy he
    apply d.dense_full_certificate ha hd 7 7 hx hy he dense_10_10_7_7_4_2_2_profile (by decide) 35
    · have hp := packing_le_number dense_10_10_7_7_4_2_2_verified.1
      rwa [dense_10_10_7_7_4_2_2_verified.2] at hp
    · exact (show denseCoverBase 10 10 + (7 - halfUp 10) * (7 - halfUp 10) ≤ 2 * 35 from by decide)

def denseRecord_11_11_6_6_0 : DenseCertificate 11 11 where
  x := 6
  y := 6
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 6 6 hx hy he canonical_dense_11_11_6_6_0_profile (by decide) 43
    · have hp := packing_le_number canonical_dense_11_11_6_6_0_verified.1
      rwa [canonical_dense_11_11_6_6_0_verified.2] at hp
    · exact (show denseCoverBase 11 11 ≤ 2 * 43 from by decide)

def denseRecord_11_11_6_7_0 : DenseCertificate 11 11 where
  x := 6
  y := 7
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 6 7 hx hy he canonical_dense_11_11_6_7_0_profile (by decide) 43
    · have hp := packing_le_number canonical_dense_11_11_6_7_0_verified.1
      rwa [canonical_dense_11_11_6_7_0_verified.2] at hp
    · exact (show denseCoverBase 11 11 ≤ 2 * 43 from by decide)

def denseRecord_11_11_7_6_0 : DenseCertificate 11 11 where
  x := 7
  y := 6
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 7 6 hx hy he canonical_dense_11_11_7_6_0_6_profile (by decide) 43
    · have hp := packing_le_number canonical_dense_11_11_7_6_0_6_verified.1
      rwa [canonical_dense_11_11_7_6_0_6_verified.2] at hp
    · exact (show denseCoverBase 11 11 ≤ 2 * 43 from by decide)

def denseRecord_11_11_7_7_0 : DenseCertificate 11 11 where
  x := 7
  y := 7
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 7 7 hx hy he canonical_dense_11_11_7_7_0_6_profile (by decide) 43
    · have hp := packing_le_number canonical_dense_11_11_7_7_0_6_verified.1
      rwa [canonical_dense_11_11_7_7_0_6_verified.2] at hp
    · exact (show denseCoverBase 11 11 ≤ 2 * 43 from by decide)

def denseRecord_11_11_7_7_1 : DenseCertificate 11 11 where
  x := 7
  y := 7
  e := 1
  correct := by
    intro d ha hd hx hy he
    apply d.dense_full_certificate ha hd 7 7 hx hy he canonical_dense_11_11_7_7_1_7_profile (by decide) 44
    · have hp := packing_le_number canonical_dense_11_11_7_7_1_7_verified.1
      rwa [canonical_dense_11_11_7_7_1_7_verified.2] at hp
    · exact (show denseCoverBase 11 11 + (7 - halfUp 11) * (7 - halfUp 11) ≤ 2 * 44 from by decide)

def denseRecord_11_11_8_8_3 : DenseCertificate 11 11 where
  x := 8
  y := 8
  e := 3
  correct := by
    intro d ha hd hx hy he
    have hw : d.height (halfUp 11) - halfUp 11 = 2 := by rw [hx]; rfl
    have hz : d.medianDegree ha - halfUp 11 = 2 := by rw [hy]; rfl
    have hsum := (d.lowerShape_sum ha hd).trans he
    have hs := shape_two_two_cases (d.lowerShape ha hd) hw hz hsum
    have hg : dense_11_11_8_8_3_2_1_profile.graph ≤ d.graph := by
      apply d.dense_pattern_graph_le_of_shape ha hd dense_11_11_8_8_3_2_1_profile (fun k => if k = 0 then 2 else 1) hs
      · intro i hi
        rw [hy]
        exact (show ∀ i : Fin 11, i.val < halfUp 11 → dense_11_11_8_8_3_2_1_profile.degree i ≤ 8
          from by decide) i hi
      · intro i hi
        rw [hx] at hi
        exact (show ∀ i : Fin 11, 8 ≤ i.val → dense_11_11_8_8_3_2_1_profile.degree i = 0
          from by decide) i hi
      · intro i hir hix
        rw [hx] at hix
        exact (show ∀ i : Fin 11, halfUp 11 ≤ i.val → i.val < 8 →
            dense_11_11_8_8_3_2_1_profile.degree i ≤ halfUp 11 + (fun k => if k = 0 then 2 else 1) (i.val - halfUp 11)
          from by decide) i hir hix
    have hp := packing_le_number dense_11_11_8_8_3_2_1_verified.1
    rw [dense_11_11_8_8_3_2_1_verified.2] at hp
    have hc := d.dense_cover_base_bound hd
    rw [he] at hc
    have hf : denseCoverBase 11 11 + 3 ≤ 2 * 45 := by decide
    exact hc.trans (hf.trans (Nat.mul_le_mul_left 2 (hp.trans (packingNumber_mono hg))))

def denseRecord_11_11_8_8_4 : DenseCertificate 11 11 where
  x := 8
  y := 8
  e := 4
  correct := by
    intro d ha hd hx hy he
    apply d.dense_full_certificate ha hd 8 8 hx hy he dense_11_11_8_8_4_2_2_profile (by decide) 45
    · have hp := packing_le_number dense_11_11_8_8_4_2_2_verified.1
      rwa [dense_11_11_8_8_4_2_2_verified.2] at hp
    · exact (show denseCoverBase 11 11 + (8 - halfUp 11) * (8 - halfUp 11) ≤ 2 * 45 from by decide)

def denseRecord_11_12_8_8_4 : DenseCertificate 11 12 where
  x := 8
  y := 8
  e := 4
  correct := by
    intro d ha hd hx hy he
    apply d.dense_full_certificate ha hd 8 8 hx hy he dense_11_12_8_8_4_2_2_profile (by decide) 48
    · have hp := packing_le_number dense_11_12_8_8_4_2_2_verified.1
      rwa [dense_11_12_8_8_4_2_2_verified.2] at hp
    · exact (show denseCoverBase 11 12 + (8 - halfUp 11) * (8 - halfUp 12) ≤ 2 * 48 from by decide)

def denseRecord_11_13_6_7_0 : DenseCertificate 11 13 where
  x := 6
  y := 7
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 6 7 hx hy he canonical_dense_11_13_6_7_0_profile (by decide) 52
    · have hp := packing_le_number canonical_dense_11_13_6_7_0_verified.1
      rwa [canonical_dense_11_13_6_7_0_verified.2] at hp
    · exact (show denseCoverBase 11 13 ≤ 2 * 52 from by decide)

def denseRecord_11_13_6_8_0 : DenseCertificate 11 13 where
  x := 6
  y := 8
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 6 8 hx hy he canonical_dense_11_13_6_8_0_profile (by decide) 52
    · have hp := packing_le_number canonical_dense_11_13_6_8_0_verified.1
      rwa [canonical_dense_11_13_6_8_0_verified.2] at hp
    · exact (show denseCoverBase 11 13 ≤ 2 * 52 from by decide)

def denseRecord_11_13_6_9_0 : DenseCertificate 11 13 where
  x := 6
  y := 9
  e := 0
  correct := by
    intro d ha hd hx hy he
    apply d.dense_zero_certificate ha hd 6 9 hx hy he canonical_dense_11_13_6_9_0_profile (by decide) 52
    · have hp := packing_le_number canonical_dense_11_13_6_9_0_verified.1
      rwa [canonical_dense_11_13_6_9_0_verified.2] at hp
    · exact (show denseCoverBase 11 13 ≤ 2 * 52 from by decide)

def denseRecord_15_15_11_11_9 : DenseCertificate 15 15 where
  x := 11
  y := 11
  e := 9
  correct := by
    intro d ha hd hx hy he
    apply d.dense_full_certificate ha hd 11 11 hx hy he canonical_dense_15_15_11_11_9_11_11_11_profile (by decide) 86
    · have hp := packing_le_number canonical_dense_15_15_11_11_9_11_11_11_verified.1
      rwa [canonical_dense_15_15_11_11_9_11_11_11_verified.2] at hp
    · exact (show denseCoverBase 15 15 + (11 - halfUp 15) * (11 - halfUp 15) ≤ 2 * 86 from by decide)

def denseCertificates : (a b : ℕ) → List (DenseCertificate a b)
  | 5, 9 => [denseRecord_5_9_3_5_0, denseRecord_5_9_3_6_0, denseRecord_5_9_3_7_0, denseRecord_5_9_4_7_2]
  | 6, 7 => [denseRecord_6_7_3_4_0, denseRecord_6_7_3_5_0]
  | 6, 9 => [denseRecord_6_9_3_5_0, denseRecord_6_9_3_6_0, denseRecord_6_9_3_7_0, denseRecord_6_9_4_7_2]
  | 7, 7 => [denseRecord_7_7_4_4_0, denseRecord_7_7_4_5_0, denseRecord_7_7_5_4_0, denseRecord_7_7_5_5_0, denseRecord_7_7_5_5_1]
  | 7, 9 => [denseRecord_7_9_4_5_0, denseRecord_7_9_4_6_0, denseRecord_7_9_4_7_0, denseRecord_7_9_5_7_2]
  | 9, 9 => [denseRecord_9_9_5_5_0, denseRecord_9_9_7_7_4]
  | 9, 11 => [denseRecord_9_11_7_9_4]
  | 10, 10 => [denseRecord_10_10_7_7_4]
  | 11, 11 => [denseRecord_11_11_6_6_0, denseRecord_11_11_6_7_0, denseRecord_11_11_7_6_0, denseRecord_11_11_7_7_0, denseRecord_11_11_7_7_1, denseRecord_11_11_8_8_3, denseRecord_11_11_8_8_4]
  | 11, 12 => [denseRecord_11_12_8_8_4]
  | 11, 13 => [denseRecord_11_13_6_7_0, denseRecord_11_13_6_8_0, denseRecord_11_13_6_9_0]
  | 15, 15 => [denseRecord_15_15_11_11_9]
  | _, _ => []

end ResearchMain.Tuza.Certificates
