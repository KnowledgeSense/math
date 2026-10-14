import MeanMaximumForests.GraphInvariants

#print axioms MeanMaximumForests.independentSetCount_recursion
#print axioms MeanMaximumForests.independentSetSizeSum_recursion
#print axioms MeanMaximumForests.independenceNumber_recursion
#print axioms MeanMaximumForests.meanIndependentSetSize_union
#print axioms MeanMaximumForests.ForestRealization.vector_eq
#print axioms MeanMaximumForests.ForestRealization.attach_leaf
#print axioms MeanMaximumForests.exists_forestRealization
#print axioms MeanMaximumForests.graphMean_lower_bound

example {V : Type*} [DecidableEq V] (G : SimpleGraph V) :
    MeanMaximumForests.meanIndependentSetSize G ∅ = 0 := by simp [MeanMaximumForests.meanIndependentSetSize]

example {V : Type*} [DecidableEq V] [Fintype V] (G : SimpleGraph V) :
    MeanMaximumForests.independenceNumber G Finset.univ = G.indepNum :=
  MeanMaximumForests.independenceNumber_univ G
