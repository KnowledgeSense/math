import HardCoreActivityThreshold.DerivativeBoxes00
import HardCoreActivityThreshold.DerivativeBoxes01
import HardCoreActivityThreshold.DerivativeBoxes02
import HardCoreActivityThreshold.DerivativeBoxes03
import HardCoreActivityThreshold.DerivativeBoxes04

namespace HardCoreActivityThreshold
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem derivative_cover_d_fourth (x : ℝ) (hx : 0<x) (hq : scalarOccupation x∈Set.Icc 0.05 0.6) :
    0<fourthNumerator (scalarOccupation x) (remainingPotential x) := by
  by_cases h0 : scalarOccupation x≤0.47109375
  · have hl0 : scalarOccupation x∈Set.Icc 0.05 0.47109375 := ⟨hq.1,h0⟩
    by_cases h1 : scalarOccupation x≤0.325
    · have hl1 : scalarOccupation x∈Set.Icc 0.05 0.325 := ⟨hl0.1,h1⟩
      by_cases h2 : scalarOccupation x≤0.1875
      · have hl2 : scalarOccupation x∈Set.Icc 0.05 0.1875 := ⟨hl1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.11875
        · have hl3 : scalarOccupation x∈Set.Icc 0.05 0.11875 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.084375
          · have hl4 : scalarOccupation x∈Set.Icc 0.05 0.084375 := ⟨hl3.1,h4⟩
            exact fourth_box_0000 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.084375 0.11875 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            exact fourth_box_0001 x hx hr4
        · have hr3 : scalarOccupation x∈Set.Icc 0.11875 0.1875 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.153125
          · have hl4 : scalarOccupation x∈Set.Icc 0.11875 0.153125 := ⟨hr3.1,h4⟩
            exact fourth_box_0002 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.153125 0.1875 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            exact fourth_box_0003 x hx hr4
      · have hr2 : scalarOccupation x∈Set.Icc 0.1875 0.325 := ⟨(lt_of_not_ge h2).le,hl1.2⟩
        by_cases h3 : scalarOccupation x≤0.25625
        · have hl3 : scalarOccupation x∈Set.Icc 0.1875 0.25625 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.221875
          · have hl4 : scalarOccupation x∈Set.Icc 0.1875 0.221875 := ⟨hl3.1,h4⟩
            exact fourth_box_0004 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.221875 0.25625 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            exact fourth_box_0005 x hx hr4
        · have hr3 : scalarOccupation x∈Set.Icc 0.25625 0.325 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.290625
          · have hl4 : scalarOccupation x∈Set.Icc 0.25625 0.290625 := ⟨hr3.1,h4⟩
            exact fourth_box_0006 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.290625 0.325 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.3078125
            · have hl5 : scalarOccupation x∈Set.Icc 0.290625 0.3078125 := ⟨hr4.1,h5⟩
              exact fourth_box_0007 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.3078125 0.325 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact fourth_box_0008 x hx hr5
    · have hr1 : scalarOccupation x∈Set.Icc 0.325 0.47109375 := ⟨(lt_of_not_ge h1).le,hl0.2⟩
      by_cases h2 : scalarOccupation x≤0.39375
      · have hl2 : scalarOccupation x∈Set.Icc 0.325 0.39375 := ⟨hr1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.359375
        · have hl3 : scalarOccupation x∈Set.Icc 0.325 0.359375 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.3421875
          · have hl4 : scalarOccupation x∈Set.Icc 0.325 0.3421875 := ⟨hl3.1,h4⟩
            exact fourth_box_0009 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.3421875 0.359375 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            exact fourth_box_0010 x hx hr4
        · have hr3 : scalarOccupation x∈Set.Icc 0.359375 0.39375 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.3765625
          · have hl4 : scalarOccupation x∈Set.Icc 0.359375 0.3765625 := ⟨hr3.1,h4⟩
            exact fourth_box_0011 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.3765625 0.39375 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            exact fourth_box_0012 x hx hr4
      · have hr2 : scalarOccupation x∈Set.Icc 0.39375 0.47109375 := ⟨(lt_of_not_ge h2).le,hr1.2⟩
        by_cases h3 : scalarOccupation x≤0.428125
        · have hl3 : scalarOccupation x∈Set.Icc 0.39375 0.428125 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.4109375
          · have hl4 : scalarOccupation x∈Set.Icc 0.39375 0.4109375 := ⟨hl3.1,h4⟩
            exact fourth_box_0013 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.4109375 0.428125 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            exact fourth_box_0014 x hx hr4
        · have hr3 : scalarOccupation x∈Set.Icc 0.428125 0.47109375 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.4453125
          · have hl4 : scalarOccupation x∈Set.Icc 0.428125 0.4453125 := ⟨hr3.1,h4⟩
            exact fourth_box_0015 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.4453125 0.47109375 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.4625
            · have hl5 : scalarOccupation x∈Set.Icc 0.4453125 0.4625 := ⟨hr4.1,h5⟩
              exact fourth_box_0016 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.4625 0.47109375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact fourth_box_0017 x hx hr5
  · have hr0 : scalarOccupation x∈Set.Icc 0.47109375 0.6 := ⟨(lt_of_not_ge h0).le,hq.2⟩
    by_cases h1 : scalarOccupation x≤0.5484375
    · have hl1 : scalarOccupation x∈Set.Icc 0.47109375 0.5484375 := ⟨hr0.1,h1⟩
      by_cases h2 : scalarOccupation x≤0.50546875
      · have hl2 : scalarOccupation x∈Set.Icc 0.47109375 0.50546875 := ⟨hl1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.48828125
        · have hl3 : scalarOccupation x∈Set.Icc 0.47109375 0.48828125 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.4796875
          · have hl4 : scalarOccupation x∈Set.Icc 0.47109375 0.4796875 := ⟨hl3.1,h4⟩
            exact fourth_box_0018 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.4796875 0.48828125 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            exact fourth_box_0019 x hx hr4
        · have hr3 : scalarOccupation x∈Set.Icc 0.48828125 0.50546875 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.496875
          · have hl4 : scalarOccupation x∈Set.Icc 0.48828125 0.496875 := ⟨hr3.1,h4⟩
            exact fourth_box_0020 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.496875 0.50546875 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            exact fourth_box_0021 x hx hr4
      · have hr2 : scalarOccupation x∈Set.Icc 0.50546875 0.5484375 := ⟨(lt_of_not_ge h2).le,hl1.2⟩
        by_cases h3 : scalarOccupation x≤0.52265625
        · have hl3 : scalarOccupation x∈Set.Icc 0.50546875 0.52265625 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.5140625
          · have hl4 : scalarOccupation x∈Set.Icc 0.50546875 0.5140625 := ⟨hl3.1,h4⟩
            exact fourth_box_0022 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.5140625 0.52265625 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            exact fourth_box_0023 x hx hr4
        · have hr3 : scalarOccupation x∈Set.Icc 0.52265625 0.5484375 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.53125
          · have hl4 : scalarOccupation x∈Set.Icc 0.52265625 0.53125 := ⟨hr3.1,h4⟩
            exact fourth_box_0024 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.53125 0.5484375 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.53984375
            · have hl5 : scalarOccupation x∈Set.Icc 0.53125 0.53984375 := ⟨hr4.1,h5⟩
              exact fourth_box_0025 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.53984375 0.5484375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact fourth_box_0026 x hx hr5
    · have hr1 : scalarOccupation x∈Set.Icc 0.5484375 0.6 := ⟨(lt_of_not_ge h1).le,hr0.2⟩
      by_cases h2 : scalarOccupation x≤0.578515625
      · have hl2 : scalarOccupation x∈Set.Icc 0.5484375 0.578515625 := ⟨hr1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.565625
        · have hl3 : scalarOccupation x∈Set.Icc 0.5484375 0.565625 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.55703125
          · have hl4 : scalarOccupation x∈Set.Icc 0.5484375 0.55703125 := ⟨hl3.1,h4⟩
            exact fourth_box_0027 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.55703125 0.565625 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            exact fourth_box_0028 x hx hr4
        · have hr3 : scalarOccupation x∈Set.Icc 0.565625 0.578515625 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.569921875
          · have hl4 : scalarOccupation x∈Set.Icc 0.565625 0.569921875 := ⟨hr3.1,h4⟩
            exact fourth_box_0029 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.569921875 0.578515625 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.57421875
            · have hl5 : scalarOccupation x∈Set.Icc 0.569921875 0.57421875 := ⟨hr4.1,h5⟩
              exact fourth_box_0030 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.57421875 0.578515625 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact fourth_box_0031 x hx hr5
      · have hr2 : scalarOccupation x∈Set.Icc 0.578515625 0.6 := ⟨(lt_of_not_ge h2).le,hr1.2⟩
        by_cases h3 : scalarOccupation x≤0.587109375
        · have hl3 : scalarOccupation x∈Set.Icc 0.578515625 0.587109375 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.5828125
          · have hl4 : scalarOccupation x∈Set.Icc 0.578515625 0.5828125 := ⟨hl3.1,h4⟩
            exact fourth_box_0032 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.5828125 0.587109375 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            exact fourth_box_0033 x hx hr4
        · have hr3 : scalarOccupation x∈Set.Icc 0.587109375 0.6 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.59140625
          · have hl4 : scalarOccupation x∈Set.Icc 0.587109375 0.59140625 := ⟨hr3.1,h4⟩
            exact fourth_box_0034 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.59140625 0.6 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.595703125
            · have hl5 : scalarOccupation x∈Set.Icc 0.59140625 0.595703125 := ⟨hr4.1,h5⟩
              exact fourth_box_0035 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.595703125 0.6 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact fourth_box_0036 x hx hr5

theorem derivative_cover_e_Gsecond (x : ℝ) (hx : 0<x) (hq : scalarOccupation x∈Set.Icc 0.393 0.463) :
    0<secondFivefoldDerivative x := by
  by_cases h0 : scalarOccupation x≤0.428
  · have hl0 : scalarOccupation x∈Set.Icc 0.393 0.428 := ⟨hq.1,h0⟩
    by_cases h1 : scalarOccupation x≤0.4105
    · have hl1 : scalarOccupation x∈Set.Icc 0.393 0.4105 := ⟨hl0.1,h1⟩
      exact gap_box_0037 x hx hl1
    · have hr1 : scalarOccupation x∈Set.Icc 0.4105 0.428 := ⟨(lt_of_not_ge h1).le,hl0.2⟩
      exact gap_box_0038 x hx hr1
  · have hr0 : scalarOccupation x∈Set.Icc 0.428 0.463 := ⟨(lt_of_not_ge h0).le,hq.2⟩
    by_cases h1 : scalarOccupation x≤0.4455
    · have hl1 : scalarOccupation x∈Set.Icc 0.428 0.4455 := ⟨hr0.1,h1⟩
      exact gap_box_0039 x hx hl1
    · have hr1 : scalarOccupation x∈Set.Icc 0.4455 0.463 := ⟨(lt_of_not_ge h1).le,hr0.2⟩
      exact gap_box_0040 x hx hr1

end HardCoreActivityThreshold
