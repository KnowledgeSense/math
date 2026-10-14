import MainTheorems.MixedRadix

namespace ResearchMain.SIBO

theorem radixPrefix_step (qs : List ℕ) (t : ℕ) (ht : t < qs.length) :
    radixPrefix qs (t + 1) = radixPrefix qs t * (qs[t] + 1) := by
  induction qs generalizing t with
  | nil => simp at ht
  | cons q qs ih =>
    cases t with
    | zero => simp
    | succ t =>
      have ht' : t < qs.length := by simpa using ht
      simp only [radixPrefix_cons, List.getElem_cons_succ]
      rw [ih t ht', Nat.mul_assoc]

theorem radixPrefix_dvd (qs : List ℕ) (t : ℕ) : radixPrefix qs t ∣ radixSize qs := by
  refine ⟨radixSize (qs.drop t), ?_⟩
  calc
    radixSize qs = radixSize (qs.take t ++ qs.drop t) :=
      congrArg radixSize (List.take_append_drop t qs).symm
    _ = radixPrefix qs t * radixSize (qs.drop t) := by simp [radixSize, radixPrefix]

def forbiddenResidues (N a q : ℕ) : Finset (ZMod N) :=
  (Finset.range q).image (fun j => (((j + 1) * a - 1 : ℕ) : ZMod N))

theorem forbidden_representative_lt {a q j : ℕ} (ha : 0 < a) (hj : j < q) :
    (j + 1) * a - 1 < a * (q + 1) - 1 := by
  have hp : (j + 1) * a ≤ q * a := Nat.mul_le_mul_right a (by omega)
  have hz : 0 < (j + 1) * a := Nat.mul_pos (Nat.succ_pos j) ha
  have he : a * (q + 1) = q * a + a := by ring
  omega

theorem forbiddenResidues_card {N a q : ℕ} (ha : 0 < a) (hN : N = a * (q + 1)) :
    (forbiddenResidues N a q).card = q := by
  classical
  rw [forbiddenResidues, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj h
  have hi' : i < q := Finset.mem_range.mp hi
  have hj' : j < q := Finset.mem_range.mp hj
  have hil := forbidden_representative_lt ha hi'
  have hjl := forbidden_representative_lt ha hj'
  have heq := (ZMod.natCast_eq_natCast_iff' _ _ N).mp h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
  have hpi : 0 < (i + 1) * a := Nat.mul_pos (Nat.succ_pos i) ha
  have hpj : 0 < (j + 1) * a := Nat.mul_pos (Nat.succ_pos j) ha
  have hmul : (i + 1) * a = (j + 1) * a := by omega
  have hix := Nat.eq_of_mul_eq_mul_right ha hmul
  omega

def radixForbidden (qs : List ℕ) (t : Fin qs.length) : Finset (ZMod (radixPrefix qs (t.val + 1))) :=
  forbiddenResidues (radixPrefix qs (t.val + 1)) (radixPrefix qs t.val) qs[t]

theorem radixForbidden_card (qs : List ℕ) (t : Fin qs.length) :
    (radixForbidden qs t).card = qs[t] :=
  forbiddenResidues_card (radixSize_pos _) (radixPrefix_step qs t.val t.isLt)

theorem smaller_occupancy_forbidden (qs : List ℕ) (ell : ℕ) (h : ell < radixSize qs - 1) :
    ∃ t : Fin qs.length, (ell : ZMod (radixPrefix qs (t.val + 1))) ∈ radixForbidden qs t := by
  classical
  have hn : ¬ radixSize qs ∣ ell + 1 := Nat.not_dvd_of_pos_of_lt (Nat.succ_pos ell) (by omega)
  obtain ⟨t, j, hj, heq⟩ := exists_forbidden_radix qs 1 ell (by omega) (one_dvd _) (by simpa using hn)
  refine ⟨t, Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, ?_⟩⟩
  have hjlt := forbidden_representative_lt (radixSize_pos (qs.take t.val)) hj
  have hstep := radixPrefix_step qs t.val t.isLt
  change (j + 1) * radixPrefix qs t.val - 1 <
    radixPrefix qs t.val * (qs[t.val] + 1) - 1 at hjlt
  apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
  simp only [Nat.one_mul] at heq
  rw [heq, Nat.mod_eq_of_lt (by omega)]

theorem maximal_occupancy_feasible (qs : List ℕ) (t : Fin qs.length) :
    ((radixSize qs - 1 : ℕ) : ZMod (radixPrefix qs (t.val + 1))) ∉ radixForbidden qs t := by
  intro h
  obtain ⟨j, hj, heq⟩ := Finset.mem_image.mp h
  have hj' := Finset.mem_range.mp hj
  have ha := radixSize_pos (qs.take t.val)
  have hN := radixPrefix_step qs t.val t.isLt
  have hlt := forbidden_representative_lt ha hj'
  have hm := predecessor_mod_of_dvd (radixSize_pos qs)
    (radixSize_pos (qs.take (t.val + 1))) (radixPrefix_dvd qs (t.val + 1))
  change (j + 1) * radixPrefix qs t.val - 1 <
    radixPrefix qs t.val * (qs[t.val] + 1) - 1 at hlt
  change (radixSize qs - 1) % radixPrefix qs (t.val + 1) =
    radixPrefix qs (t.val + 1) - 1 at hm
  have he := (ZMod.natCast_eq_natCast_iff' _ _ _).mp heq
  rw [Nat.mod_eq_of_lt (by omega), hm] at he
  omega

end ResearchMain.SIBO
