import MainTheorems.Tuza.Certificates.Small

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace ResearchMain.Tuza

theorem smallChecked_1_1 :
    (rowTuples 1 1).all (fun f => cutTest 1 1 f ||
      profileTest (Certificates.smallProfiles 1 1) f) = true := by decide +kernel

theorem smallChecked_1_2 :
    (rowTuples 1 2).all (fun f => cutTest 1 2 f ||
      profileTest (Certificates.smallProfiles 1 2) f) = true := by decide +kernel

theorem smallChecked_1_3 :
    (rowTuples 1 3).all (fun f => cutTest 1 3 f ||
      profileTest (Certificates.smallProfiles 1 3) f) = true := by decide +kernel

theorem smallChecked_1_4 :
    (rowTuples 1 4).all (fun f => cutTest 1 4 f ||
      profileTest (Certificates.smallProfiles 1 4) f) = true := by decide +kernel

theorem smallChecked_1_5 :
    (rowTuples 1 5).all (fun f => cutTest 1 5 f ||
      profileTest (Certificates.smallProfiles 1 5) f) = true := by decide +kernel

theorem smallChecked_1_6 :
    (rowTuples 1 6).all (fun f => cutTest 1 6 f ||
      profileTest (Certificates.smallProfiles 1 6) f) = true := by decide +kernel

theorem smallChecked_1_7 :
    (rowTuples 1 7).all (fun f => cutTest 1 7 f ||
      profileTest (Certificates.smallProfiles 1 7) f) = true := by decide +kernel

theorem smallChecked_1_8 :
    (rowTuples 1 8).all (fun f => cutTest 1 8 f ||
      profileTest (Certificates.smallProfiles 1 8) f) = true := by decide +kernel

theorem smallChecked_1_9 :
    (rowTuples 1 9).all (fun f => cutTest 1 9 f ||
      profileTest (Certificates.smallProfiles 1 9) f) = true := by decide +kernel

theorem smallChecked_1_10 :
    (rowTuples 1 10).all (fun f => cutTest 1 10 f ||
      profileTest (Certificates.smallProfiles 1 10) f) = true := by decide +kernel

theorem smallChecked_1_11 :
    (rowTuples 1 11).all (fun f => cutTest 1 11 f ||
      profileTest (Certificates.smallProfiles 1 11) f) = true := by decide +kernel

end ResearchMain.Tuza
