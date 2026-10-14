import FugledeCertificates.Data.EightPoint
import FugledeCertificates.Tiling

namespace FugledeCertificates

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem eight_point_certificate_count : Data.eightPointCertificates.length = 168 := by decide

theorem eight_point_certificates_valid :
    ∀ c ∈ Data.eightPointCertificates, ValidEightCertificate c := by
  simp only [Data.eightPointCertificates, List.forall_mem_cons]
  repeat' apply And.intro
  all_goals decide +kernel

theorem eight_point_certificates_tile (c : EightCertificate)
    (hc : c ∈ Data.eightPointCertificates) :
    TranslationalTiling c.rank c.points c.complement :=
  tiles_give_unique_representation _ _ _ (eight_point_certificates_valid c hc).tiling

theorem eight_point_certificates_spectral (c : EightCertificate)
    (hc : c ∈ Data.eightPointCertificates) : IsSpectrum c.rank c.points c.spectrum :=
  (eight_point_certificates_valid c hc).spectral

end FugledeCertificates
