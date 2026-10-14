import FugledeCertificates.Definitions

/-!
The list-based tiling condition implies a unique representation in the binary
vector space. The intermediate lemmas identify the representations counted by
`Tiles` with pairs drawn from the point and complement lists.
-/

namespace FugledeCertificates

theorem unique_match_of_count_one {α : Type} (predicate : α → Bool) (values : List α) :
    values.countP predicate = 1 →
      ∃ value, value ∈ values ∧ predicate value = true ∧
        ∀ other, other ∈ values → predicate other = true → other = value := by
  induction values with
  | nil => simp
  | cons head tail ih =>
      intro count
      cases hp : predicate head with
      | false =>
          have tailCount : tail.countP predicate = 1 := by
            simpa [List.countP_cons, hp] using count
          obtain ⟨value, member, hit, unique⟩ := ih tailCount
          refine ⟨value, List.mem_cons_of_mem head member, hit, ?_⟩
          intro other otherMember otherMatches
          rcases List.mem_cons.mp otherMember with equalsHead | inTail
          · subst other
            simp [hp] at otherMatches
          · exact unique other inTail otherMatches
      | true =>
          have tailCount : tail.countP predicate = 0 := by
            have count' : tail.countP predicate + 1 = 1 := by
              simpa [List.countP_cons, hp] using count
            omega
          refine ⟨head, by simp, hp, ?_⟩
          intro other otherMember otherMatches
          rcases List.mem_cons.mp otherMember with equalsHead | inTail
          · exact equalsHead
          · have noMatch := List.countP_eq_zero.mp tailCount other inTail
            exact False.elim (noMatch otherMatches)

def translationPairs (points complement : List Nat) : List (Nat × Nat) :=
  points.flatMap fun point => complement.map fun shift => (point, shift)

theorem mem_translation_pairs (points complement : List Nat) (pair : Nat × Nat) :
    pair ∈ translationPairs points complement ↔
      pair.1 ∈ points ∧ pair.2 ∈ complement := by
  rcases pair with ⟨point, shift⟩
  simp [translationPairs]

theorem map_translation_pairs (points complement : List Nat) :
    (translationPairs points complement).map (fun pair => Nat.xor pair.1 pair.2) =
      translationSums points complement := by
  simp [translationPairs, translationSums, List.map_flatMap, List.map_map, Function.comp_def]

/-- Every vector has exactly one decomposition as a point plus a translation. -/
def TranslationalTiling (r : Nat) (points complement : List Nat) : Prop :=
    ∀ x : Fin (2 ^ r),
      ∃ point, point ∈ points ∧ ∃ shift, shift ∈ complement ∧
        Nat.xor point shift = x.val ∧
        ∀ otherPoint, otherPoint ∈ points →
          ∀ otherShift, otherShift ∈ complement →
            Nat.xor otherPoint otherShift = x.val →
              otherPoint = point ∧ otherShift = shift

theorem tiles_give_unique_representation (r : Nat) (points complement : List Nat)
    (verified : Tiles r points complement) :
    TranslationalTiling r points complement := by
  obtain ⟨_, _, _, _, _, multiplicities⟩ := verified
  intro x
  have count : (translationPairs points complement).countP
      (fun pair => Nat.xor pair.1 pair.2 == x.val) = 1 := by
    have comparison :
        (translationPairs points complement).countP
          (fun pair => Nat.xor pair.1 pair.2 == x.val) =
          (translationSums points complement).count x.val := by
      rw [← map_translation_pairs points complement]
      rw [List.count, List.countP_map]
      rfl
    rw [comparison]
    exact multiplicities x
  obtain ⟨pair, member, hit, unique⟩ := unique_match_of_count_one
    (fun pair : Nat × Nat => Nat.xor pair.1 pair.2 == x.val)
    (translationPairs points complement) count
  have members := (mem_translation_pairs points complement pair).mp member
  refine ⟨pair.1, members.1, pair.2, members.2, by simpa using hit, ?_⟩
  intro otherPoint inPoints otherShift inComplement sameSum
  have pairEquality : (otherPoint, otherShift) = pair := unique (otherPoint, otherShift)
    ((mem_translation_pairs points complement (otherPoint, otherShift)).mpr ⟨inPoints, inComplement⟩)
    (by simpa using sameSum)
  exact ⟨congrArg Prod.fst pairEquality, congrArg Prod.snd pairEquality⟩


end FugledeCertificates

