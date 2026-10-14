import SumsetRanges.IntervalChain

namespace SumsetRanges

def InNatBox {d : ℕ} (n x : Fin d → ℕ) : Prop := ∀ i, x i≤n i

@[simp] theorem inNatBox_snoc {d : ℕ} (n x : Fin d → ℕ) (N j : ℕ) :
    InNatBox (Fin.snoc n N) (Fin.snoc x j) ↔ InNatBox n x ∧ j≤N := by
  constructor
  · intro h
    exact ⟨fun i => by simpa using h i.castSucc, by simpa using h (Fin.last d)⟩
  · rintro ⟨h,hj⟩ i
    cases i using Fin.lastCases <;> simp_all [InNatBox]

 theorem snoc_le_snoc {d : ℕ} {x y : Fin d → ℕ} {i j : ℕ}
    (h : ∀a,x a≤y a) (hij : i≤j) : ∀a : Fin (d+1), (Fin.snoc x i : Fin (d+1) → ℕ) a≤(Fin.snoc y j : Fin (d+1) → ℕ) a := by
  intro a
  cases a using Fin.lastCases <;> simp_all

 theorem snoc_zero {d : ℕ} : Fin.snoc (fun _ : Fin d => 0) 0=(fun _ => 0) := by
  ext i
  cases i using Fin.lastCases <;> simp

/-- The finite-box interval lemma. Its hypotheses are uniform one-step and full-coordinate
bounds, and its conclusion supplies an actual point of the box at every intermediate value. -/
theorem integer_box_intermediate (d : ℕ) (n : Fin d → ℕ) (f : (Fin d → ℕ) → ℤ)
    (δ Δ : Fin d → ℤ)
    (anti : ∀x y, InNatBox n x → InNatBox n y → (∀i,x i≤y i) → f y≤f x)
    (step : ∀x, InNatBox n x → ∀i, x i<n i →
      f x-f (Function.update x i (x i+1))≤δ i)
    (width : ∀x, InNatBox n x → ∀i,
      Δ i≤f (Function.update x i 0)-f (Function.update x i (n i)))
    (first : ∀i, i.val=0 → δ i≤1)
    (next : ∀i j, j.val+1=i.val → δ i≤Δ j)
    (z : ℤ) (hz : f n≤z) (hz' : z≤f (fun _ => 0)) :
    ∃x, InNatBox n x ∧ f x=z := by
  induction d generalizing z with
  | zero =>
      have he : n=(fun _ => 0) := funext (fun i => Fin.elim0 i)
      exact ⟨n,fun _ => le_rfl,by rw [←he] at hz'; omega⟩
  | succ d ih =>
      let ns : Fin d → ℕ := Fin.init n
      let N := n (Fin.last d)
      have hn : n=Fin.snoc ns N := (Fin.snoc_init_self n).symm
      let F (j : ℕ) (x : Fin d → ℕ) := f (Fin.snoc x j)
      have hvalid (j : ℕ) (hj : j≤N) (x : Fin d → ℕ) (hx : InNatBox ns x) :
          InNatBox n (Fin.snoc x j) := by rw [hn]; exact inNatBox_snoc ns x N j |>.mpr ⟨hx,hj⟩
      have cover (j : ℕ) (hj : j≤N) (w : ℤ)
          (hw : F j ns≤w) (hw' : w≤F j (fun _ => 0)) :
          ∃x, InNatBox ns x ∧ F j x=w := by
        apply ih ns (F j) (fun i => δ i.castSucc) (fun i => Δ i.castSucc)
        · intro x y hx hy hxy
          exact anti _ _ (hvalid j hj x hx) (hvalid j hj y hy) (snoc_le_snoc hxy le_rfl)
        · intro x hx i hi
          have hs := step _ (hvalid j hj x hx) i.castSucc (by simpa [ns,Fin.init] using hi)
          simpa [F] using hs
        · intro x hx i
          have hs := width _ (hvalid j hj x hx) i.castSucc
          simpa [F,ns,Fin.init] using hs
        · intro i hi
          exact first i.castSucc hi
        · intro i l hi
          exact next i.castSucc l.castSucc hi
        · exact hw
        · exact hw'
      have hlo (j : ℕ) (hj : j<N) : F (j+1) ns≤F j ns :=
        anti _ _ (hvalid j (by omega) ns (fun _ => le_rfl))
          (hvalid (j+1) (by omega) ns (fun _ => le_rfl))
          (snoc_le_snoc (fun _ => le_rfl) (by omega))
      have hoverlap (j : ℕ) (hj : j<N) : F j ns≤F (j+1) (fun _ => 0)+1 := by
        let x : Fin (d+1) → ℕ := Fin.snoc (fun _ : Fin d => 0) j
        have hx : InNatBox n x := hvalid j (by omega) _ (fun i => Nat.zero_le _)
        have hs := step x hx (Fin.last d) (by simpa [x,N] using hj)
        have hs' : F j (fun _ => 0)-F (j+1) (fun _ => 0)≤δ (Fin.last d) := by
          simpa [x,F,Fin.update_snoc_last] using hs
        by_cases hd : d=0
        · subst d
          have he : ns=(fun _ => 0) := funext (fun i => Fin.elim0 i)
          have hf := first (Fin.last 0) rfl
          rw [he]
          omega
        · let i : Fin d := ⟨d-1,by omega⟩
          have hw := width x hx i.castSucc
          have he : Function.update x i.castSucc 0=x := by
            apply Function.update_eq_self_iff.mpr
            simp [x]
          rw [he] at hw
          have hy : InNatBox n (Function.update x i.castSucc (n i.castSucc)) := by
            intro a
            by_cases ha : a=i.castSucc
            · subst a; simp
            · simp [Function.update_of_ne ha,hx a]
          have hxy : ∀a : Fin (d+1), Function.update x i.castSucc (n i.castSucc) a≤(Fin.snoc ns j : Fin (d+1) → ℕ) a := by
            intro a
            cases a using Fin.lastCases with
            | last => simp [x,Function.update_of_ne (Fin.castSucc_ne_last i).symm]
            | cast a =>
                by_cases ha : a=i
                · subst a; simp [ns,Fin.init]
                · simp [x,Function.update_of_ne (by simpa using ha : a.castSucc≠i.castSucc)]
          have ha := anti _ _ hy (hvalid j (by omega) ns (fun _ => le_rfl)) hxy
          have hc := next (Fin.last d) i.castSucc (by simp [i]; omega)
          change Δ i.castSucc≤F j (fun _ => 0)-f (Function.update x i.castSucc (n i.castSucc)) at hw
          change F j ns≤f (Function.update x i.castSucc (n i.castSucc)) at ha
          omega
      obtain ⟨j,hj,x,hx,he⟩ := integer_interval_chain F (fun _ => InNatBox ns)
        (fun j => F j ns) (fun j => F j (fun _ => 0)) N cover hlo hoverlap z
        (by simpa [F,←hn] using hz) (by simpa [F,snoc_zero] using hz')
      exact ⟨Fin.snoc x j,hvalid j hj x hx,he⟩

end SumsetRanges
