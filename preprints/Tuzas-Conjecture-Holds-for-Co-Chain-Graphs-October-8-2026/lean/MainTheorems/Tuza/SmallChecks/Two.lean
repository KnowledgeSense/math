import MainTheorems.Tuza.Certificates.Small

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace ResearchMain.Tuza

theorem smallChecked_2_2 :
    (rowTuples 2 2).all (fun f => cutTest 2 2 f ||
      profileTest (Certificates.smallProfiles 2 2) f) = true := by decide +kernel

theorem smallChecked_2_3 :
    (rowTuples 2 3).all (fun f => cutTest 2 3 f ||
      profileTest (Certificates.smallProfiles 2 3) f) = true := by decide +kernel

theorem smallChecked_2_4 :
    (rowTuples 2 4).all (fun f => cutTest 2 4 f ||
      profileTest (Certificates.smallProfiles 2 4) f) = true := by decide +kernel

theorem smallChecked_2_5 :
    (rowTuples 2 5).all (fun f => cutTest 2 5 f ||
      profileTest (Certificates.smallProfiles 2 5) f) = true := by decide +kernel

theorem smallChecked_2_6 :
    (rowTuples 2 6).all (fun f => cutTest 2 6 f ||
      profileTest (Certificates.smallProfiles 2 6) f) = true := by decide +kernel

theorem smallChecked_2_7 :
    (rowTuples 2 7).all (fun f => cutTest 2 7 f ||
      profileTest (Certificates.smallProfiles 2 7) f) = true := by decide +kernel

theorem smallChecked_2_8 :
    (rowTuples 2 8).all (fun f => cutTest 2 8 f ||
      profileTest (Certificates.smallProfiles 2 8) f) = true := by decide +kernel

theorem smallChecked_2_9 :
    (rowTuples 2 9).all (fun f => cutTest 2 9 f ||
      profileTest (Certificates.smallProfiles 2 9) f) = true := by decide +kernel

theorem smallChecked_2_10 :
    (rowTuples 2 10).all (fun f => cutTest 2 10 f ||
      profileTest (Certificates.smallProfiles 2 10) f) = true := by decide +kernel

end ResearchMain.Tuza
