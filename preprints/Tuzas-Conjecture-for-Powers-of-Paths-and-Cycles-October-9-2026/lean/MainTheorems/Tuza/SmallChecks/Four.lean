import MainTheorems.Tuza.Certificates.Small

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace ResearchMain.Tuza

theorem smallChecked_4_4 :
    (rowTuples 4 4).all (fun f => cutTest 4 4 f ||
      profileTest (Certificates.smallProfiles 4 4) f) = true := by decide +kernel

theorem smallChecked_4_5 :
    (rowTuples 4 5).all (fun f => cutTest 4 5 f ||
      profileTest (Certificates.smallProfiles 4 5) f) = true := by decide +kernel

theorem smallChecked_4_6 :
    (rowTuples 4 6).all (fun f => cutTest 4 6 f ||
      profileTest (Certificates.smallProfiles 4 6) f) = true := by decide +kernel

theorem smallChecked_4_7 :
    (rowTuples 4 7).all (fun f => cutTest 4 7 f ||
      profileTest (Certificates.smallProfiles 4 7) f) = true := by decide +kernel

theorem smallChecked_4_8 :
    (rowTuples 4 8).all (fun f => cutTest 4 8 f ||
      profileTest (Certificates.smallProfiles 4 8) f) = true := by decide +kernel

end ResearchMain.Tuza
