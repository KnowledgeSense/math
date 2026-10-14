import MeanMaximumForests.Data.Products00Row000
import MeanMaximumForests.Data.Products00Row001
import MeanMaximumForests.Data.Products00Row002
import MeanMaximumForests.Data.Products00Row003
import MeanMaximumForests.Data.Products00Row004
import MeanMaximumForests.Data.Products00Row005
import MeanMaximumForests.Data.Products00Row006
import MeanMaximumForests.Data.Products00Row007
import MeanMaximumForests.Data.Products00Row008
import MeanMaximumForests.Data.Products00Row009
import MeanMaximumForests.Data.Products00Row010
import MeanMaximumForests.Data.Products00Row011
import MeanMaximumForests.Data.Products00Row012
import MeanMaximumForests.Data.Products00Row013
import MeanMaximumForests.Data.Products00Row014
import MeanMaximumForests.Data.Products00Row015
import MeanMaximumForests.Data.Products00Row016
import MeanMaximumForests.Data.Products00Row017
import MeanMaximumForests.Data.Products00Row018
import MeanMaximumForests.Data.Products00Row019
import MeanMaximumForests.Data.Products00Row020
import MeanMaximumForests.Data.Products00Row021
import MeanMaximumForests.Data.Products00Row022
import MeanMaximumForests.Data.Products00Row023
import MeanMaximumForests.Data.Products00Row024
import MeanMaximumForests.Data.Products00Row025
import MeanMaximumForests.Data.Products00Row026
import MeanMaximumForests.Data.Products00Row027
import MeanMaximumForests.Data.Products00Row028
import MeanMaximumForests.Data.Products00Row029
import MeanMaximumForests.Data.Products00Row030
import MeanMaximumForests.Data.Products00Row031
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace MeanMaximumForests.Release
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem product00_upper_mem (i : Fin 32) (j : Fin 32) (h : i.val ≤ j.val) :
  GeneratedCone (generatorSet generators0) (product (generators0 i).toReal (generators0 j).toReal) := by
  rw [← IntegerVector.toReal_product]
  fin_cases i
  · exact CertificateData.sound _ _ _ (products00Row000_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row001_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row002_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row003_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row004_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row005_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row006_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row007_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row008_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row009_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row010_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row011_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row012_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row013_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row014_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row015_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row016_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row017_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row018_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row019_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row020_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row021_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row022_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row023_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row024_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row025_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row026_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row027_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row028_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row029_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row030_valid j h)
  · exact CertificateData.sound _ _ _ (products00Row031_valid j h)

theorem product00_mem (i : Fin 32) (j : Fin 32) :
    GeneratedCone (generatorSet generators0)
      (product (generators0 i).toReal (generators0 j).toReal) := by
  by_cases h : i.val ≤ j.val
  · exact product00_upper_mem i j h
  · rw [product_comm]
    exact product00_upper_mem j i (le_of_lt (lt_of_not_ge h))

end MeanMaximumForests.Release
