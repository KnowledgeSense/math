import MainTheorems.Tuza.Certificates.Small

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace ResearchMain.Tuza

theorem smallChecked_6_6 :
    (rowTuples 6 6).all (fun f => cutTest 6 6 f ||
      profileTest (Certificates.smallProfiles 6 6) f) = true := by decide +kernel

end ResearchMain.Tuza
