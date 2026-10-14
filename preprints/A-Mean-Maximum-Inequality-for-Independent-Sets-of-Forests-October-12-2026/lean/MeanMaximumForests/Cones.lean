import MeanMaximumForests.Recursion

namespace MeanMaximumForests

def zeroVector : ConeVector := ⟨0, 0, 0, 0⟩
def add (v w : ConeVector) : ConeVector := ⟨v.p + w.p, v.q + w.q, v.x + w.x, v.y + w.y⟩
def scale (a : ℝ) (v : ConeVector) : ConeVector := ⟨a * v.p, a * v.q, a * v.x, a * v.y⟩

inductive GeneratedCone (G : Set ConeVector) : ConeVector → Prop where
  | zero : GeneratedCone G zeroVector
  | generator {v} : v ∈ G → GeneratedCone G v
  | add {v w} : GeneratedCone G v → GeneratedCone G w → GeneratedCone G (add v w)
  | scale {v} (a : ℝ) : 0 ≤ a → GeneratedCone G v → GeneratedCone G (scale a v)

theorem product_zero (v : ConeVector) : product zeroVector v = zeroVector := by
  ext <;> simp [product, zeroVector]
theorem product_add (u v w : ConeVector) :
    product (add u v) w = add (product u w) (product v w) := by
  ext <;> simp only [product, add] <;> ring
theorem product_scale (a : ℝ) (v w : ConeVector) :
    product (scale a v) w = scale a (product v w) := by
  ext <;> simp only [product, scale] <;> ring
theorem plant_zero (c : ℝ) (f : Bool) : plant c f zeroVector = zeroVector := by
  ext <;> simp [plant, zeroVector]
theorem plant_add (c : ℝ) (f : Bool) (v w : ConeVector) :
    plant c f (add v w) = add (plant c f v) (plant c f w) := by
  ext <;> simp only [plant, add] <;> ring
theorem plant_scale (c a : ℝ) (f : Bool) (v : ConeVector) :
    plant c f (scale a v) = scale a (plant c f v) := by
  ext <;> simp only [plant, scale] <;> ring

theorem product_mem_of_generators {G H K : Set ConeVector}
    (h : ∀ v ∈ G, ∀ w ∈ H, GeneratedCone K (product v w))
    {v w : ConeVector} (hv : GeneratedCone G v) (hw : GeneratedCone H w) :
    GeneratedCone K (product v w) := by
  induction hv with
  | zero => rw [product_zero]; exact .zero
  | @generator v hv =>
    induction hw with
    | zero => rw [product_comm, product_zero]; exact .zero
    | generator hw => exact h v hv _ hw
    | @add u w hu hw ihu ihw =>
      rw [product_comm, product_add, product_comm u v, product_comm w v]
      exact .add ihu ihw
    | @scale w a ha hw ih =>
      rw [product_comm, product_scale, product_comm w v]
      exact .scale a ha ih
  | add hv hw ihv ihw => rw [product_add]; exact .add ihv ihw
  | scale a ha hv ih => rw [product_scale]; exact .scale a ha ih

theorem plant_mem_of_generators {c : ℝ} {f : Bool} {G H : Set ConeVector}
    (h : ∀ v ∈ G, GeneratedCone H (plant c f v))
    {v : ConeVector} (hv : GeneratedCone G v) : GeneratedCone H (plant c f v) := by
  induction hv with
  | zero => rw [plant_zero]; exact .zero
  | generator hv => exact h _ hv
  | add hv hw ihv ihw => rw [plant_add]; exact .add ihv ihw
  | scale a ha hv ih => rw [plant_scale]; exact .scale a ha ih

theorem plant_sign_of_generators {c : ℝ} {f : Bool} {G : Set ConeVector}
    (h : ∀ v ∈ G, 0 ≤ (plant c f v).x)
    {v : ConeVector} (hv : GeneratedCone G v) : 0 ≤ (plant c f v).x := by
  induction hv with
  | zero => rw [plant_zero]; exact le_refl 0
  | generator hv => exact h _ hv
  | add hv hw ihv ihw => rw [plant_add]; exact add_nonneg ihv ihw
  | scale a ha hv ih => rw [plant_scale]; exact mul_nonneg ha ih

theorem invariant_of_generator_checks (c : ℝ) (G : Bool → Set ConeVector)
    (he : unitVector ∈ G false)
    (hprod : ∀ f g v, v ∈ G f → ∀ w, w ∈ G g → GeneratedCone (G (f || g)) (product v w))
    (hplant : ∀ f v, v ∈ G f → GeneratedCone (G (!f)) (plant c f v))
    (hsign : ∀ f v, v ∈ G f → 0 ≤ (plant c f v).x) :
    InvariantConditions c (fun f => {v | GeneratedCone (G f) v}) where
  empty := .generator he
  product f g _ _ hv hw := product_mem_of_generators (hprod f g) hv hw
  plant f _ hv := plant_mem_of_generators (hplant f) hv
  sign f _ hv := plant_sign_of_generators (hsign f) hv

end MeanMaximumForests
