import MeanMaximumForests

#print axioms MeanMaximumForests.mean_maximum_inequality
#print axioms MeanMaximumForests.Release.release_invariant
#print axioms MeanMaximumForests.beta_bounds

example {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic) :
    (47 / 100 : ℝ) * G.indepNum ≤ MeanMaximumForests.graphMean G :=
  MeanMaximumForests.mean_maximum_inequality G hG
