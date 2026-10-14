import ASR312.SignWitnesses

namespace ASR312

 theorem asm_row_minus_unique {n : ℕ} (A : Rectangle n n) (ha : IsASM A)
    (hav : Avoids312 A) (i : Fin n) {a b : Fin n}
    (ham : A i a = .minus) (hbm : A i b = .minus) : a = b := by
  suffices h : ∀ a b : Fin n, a < b → A i a = .minus → A i b = .minus → False by
    rcases lt_trichotomy a b with hab | hab | hba
    · exact False.elim (h a b hab ham hbm)
    · exact hab
    · exact False.elim (h b a hba hbm ham)
  intro a b hab ham hbm
  obtain ⟨x,hxi,hxb⟩ := plus_before_minus (fun x => A x b) (ha.1.2 b).2 i hbm
  obtain ⟨c,hca,hic⟩ := plus_before_minus (A i) (ha.1.1 i).2.1 a ham
  obtain ⟨y,hiy,hya⟩ := plus_after_minus (fun y => A y a) (ha.2.2 a).2 i ham
  exact hav ⟨x,i,y,c,a,b,hxi,hiy,hca,hab,hxb,hic,hya⟩

 theorem asm_col_minus_unique {n : ℕ} (A : Rectangle n n) (ha : IsASM A)
    (hav : Avoids312 A) (a : Fin n) {i j : Fin n}
    (him : A i a = .minus) (hjm : A j a = .minus) : i = j := by
  suffices h : ∀ i j : Fin n, i < j → A i a = .minus → A j a = .minus → False by
    rcases lt_trichotomy i j with hij | hij | hji
    · exact False.elim (h i j hij him hjm)
    · exact hij
    · exact False.elim (h j i hji hjm him)
  intro i j hij him hjm
  obtain ⟨c,hac,hic⟩ := plus_after_minus (A i) (ha.1.1 i).2.2 a him
  obtain ⟨b,hba,hjb⟩ := plus_before_minus (A j) (ha.1.1 j).2.1 a hjm
  obtain ⟨y,hjy,hya⟩ := plus_after_minus (fun y => A y a) (ha.2.2 a).2 j hjm
  exact hav ⟨i,j,y,b,a,c,hij,hjy,hba,hac,hic,hjb,hya⟩

 theorem extendable_row_minus_unique {r k : ℕ} (A : Rectangle r k)
    (he : ExtendablyAvoids312 A) (i : Fin r) {a b : Fin k}
    (ham : A i a = .minus) (hbm : A i b = .minus) : a = b := by
  obtain ⟨n,hr,hk,B,hB,hav,heq⟩ := he
  have hh := asm_row_minus_unique B hB hav (Fin.castLE hr i)
    (a:=Fin.castLE hk a) (b:=Fin.castLE hk b) (by rw [heq]; exact ham) (by rw [heq]; exact hbm)
  exact Fin.ext (congrArg (fun t : Fin n => t.val) hh)

 theorem extendable_col_minus_unique {r k : ℕ} (A : Rectangle r k)
    (he : ExtendablyAvoids312 A) (a : Fin k) {i j : Fin r}
    (him : A i a = .minus) (hjm : A j a = .minus) : i = j := by
  obtain ⟨n,hr,hk,B,hB,hav,heq⟩ := he
  have hh := asm_col_minus_unique B hB hav (Fin.castLE hk a)
    (i:=Fin.castLE hr i) (j:=Fin.castLE hr j) (by rw [heq]; exact him) (by rw [heq]; exact hjm)
  exact Fin.ext (congrArg (fun t : Fin n => t.val) hh)

end ASR312
