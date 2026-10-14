import ReciprocalQGamma

example (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) {r : ℕ}
    (x y : Fin r → ℝ) (hx : StrictMono x) (hy : StrictMono y)
    (hx0 : ∀ i, 0 < x i) (hy0 : ∀ i, 0 < y i) :
    0 < (-1 : ℝ) ^ (r * (r - 1) / 2) *
      Matrix.det (fun i j => 1 / ReciprocalQGamma.qGamma q (x i + y j)) :=
  ReciprocalQGamma.reciprocal_qGamma_strict_sign_regular q hq0 hq1 x y hx hy hx0 hy0

example (q u v : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (hu0 : 0 < u) (hu1 : u < 1) (hv0 : 0 < v) (hv1 : v < 1) :
    ReciprocalQGamma.qInfiniteProduct q (u * v) =
      ReciprocalQGamma.qInfiniteProduct q v *
        ∑' k : ℕ, ReciprocalQGamma.qProduct q u k / ReciprocalQGamma.qProduct q q k * v ^ k :=
  ReciprocalQGamma.qBinomial_identity q u v hq0 hq1 hu0 hu1 hv0 hv1
