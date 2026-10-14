import CokernelPolynomiality.RecodingInverse
import CokernelPolynomiality.AppendRegular

namespace CokernelPolynomiality
noncomputable section

variable {i q m : ℕ}

/-- Extend a finite coordinate embedding across one universal terminal level. -/
def extendLevels (e : Fin (q+1) ↪o Fin (m+1)) (k : ℕ) : ℕ :=
  if hk : k ≤ q then (e ⟨k,by omega⟩).val else m+(k-q)

 theorem extendLevels_at (e : Fin (q+1) ↪o Fin (m+1)) (k : Fin (q+1)) :
    extendLevels e k.val = (e k).val := by
  simp only [extendLevels,dite_eq_left (show k.val ≤ q by omega)]

 theorem extendLevels_strictMono (e : Fin (q+1) ↪o Fin (m+1)) :
    StrictMono (extendLevels e) := by
  intro a b hab
  by_cases ha : a ≤ q <;> by_cases hb : b ≤ q
  · simp only [extendLevels,dite_eq_left ha,dite_eq_left hb]
    exact e.strictMono (show (⟨a,by omega⟩ : Fin (q+1)) < ⟨b,by omega⟩ from hab)
  · simp only [extendLevels,dite_eq_left ha,dite_eq_right hb]
    have hh := (e ⟨a,by omega⟩).isLt
    omega
  · omega
  · simp only [extendLevels,dite_eq_right ha,dite_eq_right hb]
    omega

 theorem extendLevels_endpoint (e : Fin (q+1) ↪o Fin (m+1)) :
    extendLevels e (q+1) = m+1 := by
  simp [extendLevels]

 theorem extendLevels_zero (e : Fin (q+1) ↪o Fin (m+1)) (he0 : e 0 = 0) :
    extendLevels e 0 = 0 := by
  have hh := extendLevels_at e (0 : Fin (q+1))
  simpa only [he0,Fin.val_zero] using hh

 theorem recode_appended_coordinate (e : Fin (q+1) ↪o Fin (m+1)) (k : Fin (q+1)) :
    recodeLevel (extendLevels e) (extendLevels_strictMono e) (extendLevels_endpoint e) k.castSucc =
      (e k).castSucc := by
  apply Fin.ext
  exact extendLevels_at e k

/-- Admissibility depends only on the relative order of coordinate levels,
including every zero coordinate and an arbitrary trailing regular interval. -/
 theorem finite_recoding_admissible_iff (e : Fin (q+1) ↪o Fin (m+1)) (he0 : e 0 = 0)
    (d y : Fin i → Fin (q+1)) (E : SimpleGraph (Fin i)) (hd : Monotone d) :
    @Admissible (Vertex i m) (codeOrder (fun j => e (d j))) (codeGraph (fun j => e (y j)) E) ↔
    @Admissible (Vertex i q) (codeOrder d) (codeGraph y E) := by
  have hd' : Monotone (fun j => (d j).castSucc) := fun _ _ h => hd h
  have hc := recoded_admissible_iff (i := i) (extendLevels e) (extendLevels_strictMono e)
    (extendLevels_endpoint e) (extendLevels_zero e he0)
    (fun j => (d j).castSucc) (fun j => (y j).castSucc) E hd'
  have hdx : (fun j => recodeLevel (extendLevels e) (extendLevels_strictMono e)
      (extendLevels_endpoint e) (d j).castSucc) = (fun j => (e (d j)).castSucc) :=
    funext (fun j => recode_appended_coordinate e (d j))
  have hyx : (fun j => recodeLevel (extendLevels e) (extendLevels_strictMono e)
      (extendLevels_endpoint e) (y j).castSucc) = (fun j => (e (y j)).castSucc) :=
    funext (fun j => recode_appended_coordinate e (y j))
  rw [hdx,hyx] at hc
  exact (admissible_append_regular_iff (fun j => e (d j)) (fun j => e (y j)) E).symm.trans
    (hc.trans (admissible_append_regular_iff d y E))

end
end CokernelPolynomiality
