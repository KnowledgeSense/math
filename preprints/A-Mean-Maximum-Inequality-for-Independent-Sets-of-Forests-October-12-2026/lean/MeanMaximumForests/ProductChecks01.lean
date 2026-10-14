import MeanMaximumForests.Data.Products01Row000
import MeanMaximumForests.Data.Products01Row001
import MeanMaximumForests.Data.Products01Row002
import MeanMaximumForests.Data.Products01Row003
import MeanMaximumForests.Data.Products01Row004
import MeanMaximumForests.Data.Products01Row005
import MeanMaximumForests.Data.Products01Row006
import MeanMaximumForests.Data.Products01Row007
import MeanMaximumForests.Data.Products01Row008
import MeanMaximumForests.Data.Products01Row009
import MeanMaximumForests.Data.Products01Row010
import MeanMaximumForests.Data.Products01Row011
import MeanMaximumForests.Data.Products01Row012
import MeanMaximumForests.Data.Products01Row013
import MeanMaximumForests.Data.Products01Row014
import MeanMaximumForests.Data.Products01Row015
import MeanMaximumForests.Data.Products01Row016
import MeanMaximumForests.Data.Products01Row017
import MeanMaximumForests.Data.Products01Row018
import MeanMaximumForests.Data.Products01Row019
import MeanMaximumForests.Data.Products01Row020
import MeanMaximumForests.Data.Products01Row021
import MeanMaximumForests.Data.Products01Row022
import MeanMaximumForests.Data.Products01Row023
import MeanMaximumForests.Data.Products01Row024
import MeanMaximumForests.Data.Products01Row025
import MeanMaximumForests.Data.Products01Row026
import MeanMaximumForests.Data.Products01Row027
import MeanMaximumForests.Data.Products01Row028
import MeanMaximumForests.Data.Products01Row029
import MeanMaximumForests.Data.Products01Row030
import MeanMaximumForests.Data.Products01Row031
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Fin

namespace MeanMaximumForests.Release
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem product01_mem (i : Fin 32) (j : Fin 331) :
  GeneratedCone (generatorSet generators1) (product (generators0 i).toReal (generators1 j).toReal) := by
  rw [← IntegerVector.toReal_product]
  fin_cases i
  · exact CertificateData.sound _ _ _ (products01Row000_valid j)
  · exact CertificateData.sound _ _ _ (products01Row001_valid j)
  · exact CertificateData.sound _ _ _ (products01Row002_valid j)
  · exact CertificateData.sound _ _ _ (products01Row003_valid j)
  · exact CertificateData.sound _ _ _ (products01Row004_valid j)
  · exact CertificateData.sound _ _ _ (products01Row005_valid j)
  · exact CertificateData.sound _ _ _ (products01Row006_valid j)
  · exact CertificateData.sound _ _ _ (products01Row007_valid j)
  · exact CertificateData.sound _ _ _ (products01Row008_valid j)
  · exact CertificateData.sound _ _ _ (products01Row009_valid j)
  · exact CertificateData.sound _ _ _ (products01Row010_valid j)
  · exact CertificateData.sound _ _ _ (products01Row011_valid j)
  · exact CertificateData.sound _ _ _ (products01Row012_valid j)
  · exact CertificateData.sound _ _ _ (products01Row013_valid j)
  · exact CertificateData.sound _ _ _ (products01Row014_valid j)
  · exact CertificateData.sound _ _ _ (products01Row015_valid j)
  · exact CertificateData.sound _ _ _ (products01Row016_valid j)
  · exact CertificateData.sound _ _ _ (products01Row017_valid j)
  · exact CertificateData.sound _ _ _ (products01Row018_valid j)
  · exact CertificateData.sound _ _ _ (products01Row019_valid j)
  · exact CertificateData.sound _ _ _ (products01Row020_valid j)
  · exact CertificateData.sound _ _ _ (products01Row021_valid j)
  · exact CertificateData.sound _ _ _ (products01Row022_valid j)
  · exact CertificateData.sound _ _ _ (products01Row023_valid j)
  · exact CertificateData.sound _ _ _ (products01Row024_valid j)
  · exact CertificateData.sound _ _ _ (products01Row025_valid j)
  · exact CertificateData.sound _ _ _ (products01Row026_valid j)
  · exact CertificateData.sound _ _ _ (products01Row027_valid j)
  · exact CertificateData.sound _ _ _ (products01Row028_valid j)
  · exact CertificateData.sound _ _ _ (products01Row029_valid j)
  · exact CertificateData.sound _ _ _ (products01Row030_valid j)
  · exact CertificateData.sound _ _ _ (products01Row031_valid j)

end MeanMaximumForests.Release
