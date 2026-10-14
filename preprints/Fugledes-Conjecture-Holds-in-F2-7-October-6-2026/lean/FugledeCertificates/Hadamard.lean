import FugledeCertificates.Data.Hadamard
import FugledeCertificates.Tiling

namespace FugledeCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem order16_certificate_count : Data.order16Certificates.length = 5 := by decide

theorem order32_certificate_count : Data.order32Certificates.length = 32 := by decide

theorem order16_certificates_valid :
    ∀ c ∈ Data.order16Certificates, c.Valid := by
  simp only [Data.order16Certificates, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals decide +kernel

theorem order32_certificates_valid :
    ∀ c ∈ Data.order32Certificates, c.Valid := by
  simp only [Data.order32Certificates, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals decide +kernel

theorem order16_certificates_tile (c : HadamardCase) (hc : c ∈ Data.order16Certificates) :
    TranslationalTiling c.certificate.rank c.certificate.points c.certificate.complement :=
  tiles_give_unique_representation _ _ _ (order16_certificates_valid c hc).tiling

theorem order32_certificates_tile (c : HadamardCase) (hc : c ∈ Data.order32Certificates) :
    TranslationalTiling c.certificate.rank c.certificate.points c.certificate.complement :=
  tiles_give_unique_representation _ _ _ (order32_certificates_valid c hc).tiling

end FugledeCertificates
