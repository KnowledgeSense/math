import MeanMaximumForests.Data.BasisChunk1000
import MeanMaximumForests.Data.BasisChunk1001
import MeanMaximumForests.Data.BasisChunk1002
import MeanMaximumForests.Data.BasisChunk1003
import MeanMaximumForests.Data.BasisChunk1004
import MeanMaximumForests.Data.BasisChunk1005
import MeanMaximumForests.Data.BasisChunk1006
import MeanMaximumForests.Data.BasisChunk1007
import MeanMaximumForests.Data.BasisChunk1008
import MeanMaximumForests.Data.BasisChunk1009
import MeanMaximumForests.Data.BasisChunk1010
import MeanMaximumForests.Data.BasisChunk1011
import MeanMaximumForests.Data.BasisChunk1012
import MeanMaximumForests.Data.BasisChunk1013
import MeanMaximumForests.Data.BasisChunk1014
import MeanMaximumForests.Data.BasisChunk1015
import MeanMaximumForests.Data.BasisChunk1016
import MeanMaximumForests.Data.BasisChunk1017
import MeanMaximumForests.Data.BasisChunk1018
import MeanMaximumForests.Data.BasisChunk1019
import MeanMaximumForests.Data.BasisChunk1020
import MeanMaximumForests.Data.BasisChunk1021
import MeanMaximumForests.Data.BasisChunk1022
import MeanMaximumForests.Data.BasisChunk1023
import MeanMaximumForests.Data.BasisChunk1024
import MeanMaximumForests.Data.BasisChunk1025
import MeanMaximumForests.Data.BasisChunk1026
import MeanMaximumForests.Data.BasisChunk1027
import MeanMaximumForests.Data.BasisChunk1028
import MeanMaximumForests.Data.BasisChunk1029
import MeanMaximumForests.Data.BasisChunk1030
import MeanMaximumForests.Data.BasisChunk1031

namespace MeanMaximumForests.Release

def getBasis1 (i : ℕ) : BasisData 331 :=
  match i / 32 with
  | 0 => basisChunk1000[i % 32]?.getD ⟨1, []⟩
  | 1 => basisChunk1001[i % 32]?.getD ⟨1, []⟩
  | 2 => basisChunk1002[i % 32]?.getD ⟨1, []⟩
  | 3 => basisChunk1003[i % 32]?.getD ⟨1, []⟩
  | 4 => basisChunk1004[i % 32]?.getD ⟨1, []⟩
  | 5 => basisChunk1005[i % 32]?.getD ⟨1, []⟩
  | 6 => basisChunk1006[i % 32]?.getD ⟨1, []⟩
  | 7 => basisChunk1007[i % 32]?.getD ⟨1, []⟩
  | 8 => basisChunk1008[i % 32]?.getD ⟨1, []⟩
  | 9 => basisChunk1009[i % 32]?.getD ⟨1, []⟩
  | 10 => basisChunk1010[i % 32]?.getD ⟨1, []⟩
  | 11 => basisChunk1011[i % 32]?.getD ⟨1, []⟩
  | 12 => basisChunk1012[i % 32]?.getD ⟨1, []⟩
  | 13 => basisChunk1013[i % 32]?.getD ⟨1, []⟩
  | 14 => basisChunk1014[i % 32]?.getD ⟨1, []⟩
  | 15 => basisChunk1015[i % 32]?.getD ⟨1, []⟩
  | 16 => basisChunk1016[i % 32]?.getD ⟨1, []⟩
  | 17 => basisChunk1017[i % 32]?.getD ⟨1, []⟩
  | 18 => basisChunk1018[i % 32]?.getD ⟨1, []⟩
  | 19 => basisChunk1019[i % 32]?.getD ⟨1, []⟩
  | 20 => basisChunk1020[i % 32]?.getD ⟨1, []⟩
  | 21 => basisChunk1021[i % 32]?.getD ⟨1, []⟩
  | 22 => basisChunk1022[i % 32]?.getD ⟨1, []⟩
  | 23 => basisChunk1023[i % 32]?.getD ⟨1, []⟩
  | 24 => basisChunk1024[i % 32]?.getD ⟨1, []⟩
  | 25 => basisChunk1025[i % 32]?.getD ⟨1, []⟩
  | 26 => basisChunk1026[i % 32]?.getD ⟨1, []⟩
  | 27 => basisChunk1027[i % 32]?.getD ⟨1, []⟩
  | 28 => basisChunk1028[i % 32]?.getD ⟨1, []⟩
  | 29 => basisChunk1029[i % 32]?.getD ⟨1, []⟩
  | 30 => basisChunk1030[i % 32]?.getD ⟨1, []⟩
  | 31 => basisChunk1031[i % 32]?.getD ⟨1, []⟩
  | _ => ⟨1, []⟩
def decode1 (v : IntegerVector) (r : OperationRecord 331) : CertificateData 331 :=
  decodeCertificateUsing generators1 getBasis1 ⟨329, by decide⟩ ⟨330, by decide⟩ v r

end MeanMaximumForests.Release
