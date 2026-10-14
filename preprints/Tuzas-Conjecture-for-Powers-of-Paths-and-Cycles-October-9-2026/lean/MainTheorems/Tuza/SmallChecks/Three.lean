import MainTheorems.Tuza.Certificates.Small

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace ResearchMain.Tuza

theorem smallChecked_3_3 :
    (rowTuples 3 3).all (fun f => cutTest 3 3 f ||
      profileTest (Certificates.smallProfiles 3 3) f) = true := by decide +kernel

theorem smallChecked_3_4 :
    (rowTuples 3 4).all (fun f => cutTest 3 4 f ||
      profileTest (Certificates.smallProfiles 3 4) f) = true := by decide +kernel

theorem smallChecked_3_5 :
    (rowTuples 3 5).all (fun f => cutTest 3 5 f ||
      profileTest (Certificates.smallProfiles 3 5) f) = true := by decide +kernel

theorem smallChecked_3_6 :
    (rowTuples 3 6).all (fun f => cutTest 3 6 f ||
      profileTest (Certificates.smallProfiles 3 6) f) = true := by decide +kernel

theorem smallChecked_3_7 :
    (rowTuples 3 7).all (fun f => cutTest 3 7 f ||
      profileTest (Certificates.smallProfiles 3 7) f) = true := by decide +kernel

theorem smallChecked_3_8 :
    (rowTuples 3 8).all (fun f => cutTest 3 8 f ||
      profileTest (Certificates.smallProfiles 3 8) f) = true := by decide +kernel

theorem smallChecked_3_9 :
    (rowTuples 3 9).all (fun f => cutTest 3 9 f ||
      profileTest (Certificates.smallProfiles 3 9) f) = true := by decide +kernel

end ResearchMain.Tuza
