import MainTheorems.Tuza.Certificates.DenseCatalogue
import MainTheorems.Tuza.ResidualInterval
import MainTheorems.Tuza.SmallClosure

namespace ResearchMain.Tuza

def denseIntervalTest (a b x y P : ℕ) : Bool :=
  residualInterval (denseCoverBase a b) P (denseNearBase a b x y)
    ((x - halfUp a) * (y - halfUp b))
    (denseCertificateTest (Certificates.denseCertificates a b) x y)

def denseTest (a b x y : ℕ) : Bool :=
  decide (a + b ≤ 12) || denseIntervalTest a b x y (denseBasicPackingValue a b x y) ||
    denseIntervalTest a b x y (denseFullPackingValue a b x y)

def denseSizeTest (a : ℕ) : Bool :=
  (List.range 175).all fun b =>
    if 0 < a ∧ a ≤ b ∧ halfUp a + halfUp b < 88 then
      (List.range (a - halfUp a + 1)).all fun w =>
        (List.range (b - halfUp b + 1)).all fun z => denseTest a b (halfUp a + w) (halfUp b + z)
    else true

namespace FerrersProfile

variable {a b : ℕ} (d : FerrersProfile a b)

theorem denseIntervalTest_sound (ha : 0 < a) (hd : halfUp a ≤ d.height (halfUp b))
    (P : ℕ) (hp : P ≤ packingNumber d.graph)
    (h : denseIntervalTest a b (d.height (halfUp b)) (d.medianDegree ha) P = true) : Inequality d.graph := by
  have hc := d.dense_cover_base_bound hd
  by_cases hP : denseCoverBase a b + d.lowerCrossCount (halfUp a) (halfUp b) ≤ 2 * P
  · exact hc.trans (hP.trans (Nat.mul_le_mul_left 2 hp))
  · by_cases hS : (denseCoverBase a b : ℤ) + d.lowerCrossCount (halfUp a) (halfUp b) ≤
        2 * (denseNearBase a b (d.height (halfUp b)) (d.medianDegree ha) +
          d.lowerCrossCount (halfUp a) (halfUp b))
    · have hi := hS.trans (mul_le_mul_of_nonneg_left (d.dense_near_base_bound ha hd) (by norm_num))
      have hn : denseCoverBase a b + d.lowerCrossCount (halfUp a) (halfUp b) ≤
          2 * packingNumber d.graph := by exact_mod_cast hi
      exact hc.trans hn
    · have hcert := residualInterval_extract (denseCoverBase a b) P
        (denseNearBase a b (d.height (halfUp b)) (d.medianDegree ha))
        ((d.height (halfUp b) - halfUp a) * (d.medianDegree ha - halfUp b))
        (d.lowerCrossCount (halfUp a) (halfUp b))
        (denseCertificateTest (Certificates.denseCertificates a b) (d.height (halfUp b)) (d.medianDegree ha))
        (d.lowerCrossCount_bound ha hd) (by omega) (by omega) h
      exact denseCertificateTest_sound d ha hd _ hcert

theorem denseTest_sound (ha : 0 < a) (hab : a ≤ b) (hd : halfUp a ≤ d.height (halfUp b))
    (h : denseTest a b (d.height (halfUp b)) (d.medianDegree ha) = true) : Inequality d.graph := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  simp only [denseTest, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (h | h) | h
  · exact d.small_inequality ha hab h
  · exact d.denseIntervalTest_sound ha hd _ (d.dense_basic_packing_value_bound ha hb hd) h
  · exact d.denseIntervalTest_sound ha hd _ (d.dense_full_packing_value_bound ha hb hd) h

theorem denseSizeTest_sound (ha : 0 < a) (hab : a ≤ b)
    (hd : halfUp a ≤ d.height (halfUp b)) (hn : halfUp a + halfUp b < 88)
    (h : denseSizeTest a = true) : Inequality d.graph := by
  have hb : b ∈ List.range 175 := List.mem_range.mpr (by unfold halfUp at hn; omega)
  have hm := List.all_eq_true.mp h b hb
  rw [ite_eq_left ⟨ha, hab, hn⟩] at hm
  have hx := d.height_le (halfUp b)
  have hy := d.medianDegree_le ha
  have ht := d.median_dense_degree ha hd
  have hw := List.all_eq_true.mp hm (d.height (halfUp b) - halfUp a)
    (List.mem_range.mpr (by omega))
  have hz := List.all_eq_true.mp hw (d.medianDegree ha - halfUp b)
    (List.mem_range.mpr (by omega))
  rw [Nat.add_sub_of_le hd, Nat.add_sub_of_le ht] at hz
  exact d.denseTest_sound ha hab hd hz

end FerrersProfile

end ResearchMain.Tuza
