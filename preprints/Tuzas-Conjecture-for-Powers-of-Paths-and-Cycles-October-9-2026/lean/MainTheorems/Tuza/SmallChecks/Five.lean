import MainTheorems.Tuza.Certificates.Small

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace ResearchMain.Tuza

theorem smallChecked_5_5 :
    (rowTuples 5 5).all (fun f => cutTest 5 5 f ||
      profileTest (Certificates.smallProfiles 5 5) f) = true := by decide +kernel

theorem smallChecked_5_6 :
    (rowTuples 5 6).all (fun f => cutTest 5 6 f ||
      profileTest (Certificates.smallProfiles 5 6) f) = true := by decide +kernel

theorem smallChecked_5_7 :
    (rowTuples 5 7).all (fun f => cutTest 5 7 f ||
      profileTest (Certificates.smallProfiles 5 7) f) = true := by decide +kernel

end ResearchMain.Tuza
