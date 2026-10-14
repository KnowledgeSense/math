import SumsetRanges.PositionalCore

open Finset
namespace SumsetRanges

theorem topDigits_bounds (g s D : ℕ) {x : ℤ} (hx : x∈topDigits g s D) :
    0≤x ∧ x≤D := by
  simp only [topDigits,Finset.mem_insert,Finset.mem_image,Finset.mem_range] at hx
  rcases hx with rfl | ⟨a,ha,rfl⟩
  · omega
  · have hb : a*g^s≤D := calc
      a*g^s ≤ (D/g^s)*g^s := Nat.mul_le_mul_right _ (by omega)
      _ ≤ D := Nat.div_mul_le_self _ _
    exact ⟨by positivity,by exact_mod_cast hb⟩

theorem positionalCore_bounds (g s D : ℕ) (hg : 1≤g) (hD : g^s≤D)
    {x : ℤ} (hx : x∈positionalCore g s D) : 0≤x ∧ x≤D := by
  rcases Finset.mem_union.mp hx with hx | hx
  · exact topDigits_bounds g s D hx
  · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hx
    rcases Finset.mem_union.mp hi with hi | hi
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
      have hb := digitSet_lt_power g s i.val hg i.isLt ha
      exact ⟨by positivity,by exact_mod_cast (by omega : a≤D)⟩
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
      have hb := digitSet_lt_power g s i.val hg i.isLt ha
      have hc : (a:ℤ)≤D := by exact_mod_cast (by omega : a≤D)
      constructor <;> omega

theorem zero_mem_positionalCore (g s D : ℕ) : 0∈positionalCore g s D := by
  apply topDigits_subset_core
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨0,by simp,by simp⟩

theorem top_mem_positionalCore (g s D : ℕ) : (D:ℤ)∈positionalCore g s D :=
  topDigits_subset_core g s D (Finset.mem_insert_self _ _)

theorem card_topDigits_le (g s D : ℕ) (hg : 1≤g) (hD : D≤g^(s+1)) :
    (topDigits g s D).card≤g+2 := by
  have hdiv : D/g^s≤g := (Nat.div_le_iff_le_mul_add_pred (by positivity)).mpr (by
    have he : g^(s+1)=g*g^s := by rw [pow_succ,mul_comm]
    rw [he] at hD
    have hp : 1≤g^s := Nat.one_le_pow _ _ hg
    nlinarith)
  calc
    _ ≤ ((range (D/g^s+1)).image (fun j => ((j*g^s:ℕ):ℤ))).card+1 := Finset.card_insert_le _ _
    _ ≤ (D/g^s+1)+1 := Nat.add_le_add_right (Finset.card_image_le.trans_eq (Finset.card_range _)) _
    _ ≤ g+2 := by omega

theorem card_positionalCore_le (g s D : ℕ) (hg : 1≤g) (hD : D≤g^(s+1)) :
    (positionalCore g s D).card≤g+2+2*s*g := by
  unfold positionalCore
  calc
    _ ≤ (topDigits g s D).card+
      (univ.biUnion (fun i : Fin s => ((digitSet g i.val).image (fun x : ℕ => (x:ℤ))) ∪
        ((digitSet g i.val).image (fun x : ℕ => (D:ℤ)-(x:ℤ))))).card := Finset.card_union_le _ _
    _ ≤ (g+2)+∑i : Fin s,(((digitSet g i.val).image (fun x : ℕ => (x:ℤ))) ∪
        ((digitSet g i.val).image (fun x : ℕ => (D:ℤ)-(x:ℤ)))).card :=
      Nat.add_le_add (card_topDigits_le g s D hg hD) (Finset.card_biUnion_le)
    _ ≤ (g+2)+∑_i : Fin s,2*g := by
      apply Nat.add_le_add_left
      apply Finset.sum_le_sum
      intro i _
      calc
        _ ≤ ((digitSet g i.val).image (fun x : ℕ => (x:ℤ))).card+
          ((digitSet g i.val).image (fun x : ℕ => (D:ℤ)-(x:ℤ))).card := Finset.card_union_le _ _
        _ ≤ (digitSet g i.val).card+(digitSet g i.val).card := Nat.add_le_add Finset.card_image_le Finset.card_image_le
        _ = 2*g := by rw [card_digitSet g i.val hg]; omega
    _ = _ := by simp; ring

end SumsetRanges
