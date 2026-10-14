import HardCoreActivityThreshold.ScalarBoxes00
import HardCoreActivityThreshold.ScalarBoxes01
import HardCoreActivityThreshold.ScalarBoxes02
import HardCoreActivityThreshold.ScalarBoxes03
import HardCoreActivityThreshold.ScalarBoxes04
import HardCoreActivityThreshold.ScalarBoxes05
import HardCoreActivityThreshold.ScalarBoxes06
import HardCoreActivityThreshold.ScalarBoxes07
import HardCoreActivityThreshold.ScalarBoxes08
import HardCoreActivityThreshold.ScalarBoxes09
import HardCoreActivityThreshold.ScalarBoxes10
import HardCoreActivityThreshold.ScalarBoxes11
import HardCoreActivityThreshold.ScalarBoxes12
import HardCoreActivityThreshold.ScalarBoxes13
import HardCoreActivityThreshold.ScalarBoxes14
import HardCoreActivityThreshold.ScalarBoxes15
import HardCoreActivityThreshold.ScalarBoxes16
import HardCoreActivityThreshold.ScalarBoxes17
import HardCoreActivityThreshold.ScalarBoxes18
import HardCoreActivityThreshold.ScalarBoxes19
import HardCoreActivityThreshold.ScalarBoxes20
import HardCoreActivityThreshold.ScalarBoxes21
import HardCoreActivityThreshold.ScalarBoxes22
import HardCoreActivityThreshold.ScalarBoxes23
import HardCoreActivityThreshold.ScalarBoxes24
import HardCoreActivityThreshold.ScalarBoxes25
import HardCoreActivityThreshold.ScalarBoxes26
import HardCoreActivityThreshold.ScalarBoxes27
import HardCoreActivityThreshold.ScalarBoxes28
import HardCoreActivityThreshold.ScalarBoxes29
import HardCoreActivityThreshold.ScalarBoxes30
import HardCoreActivityThreshold.ScalarBoxes31
import HardCoreActivityThreshold.ScalarBoxes32
import HardCoreActivityThreshold.ScalarBoxes33
import HardCoreActivityThreshold.ScalarBoxes34
import HardCoreActivityThreshold.ScalarBoxes35
import HardCoreActivityThreshold.ScalarBoxes36
import HardCoreActivityThreshold.ScalarBoxes37
import HardCoreActivityThreshold.ScalarBoxes38
import HardCoreActivityThreshold.ScalarBoxes39
import HardCoreActivityThreshold.ScalarBoxes40
import HardCoreActivityThreshold.ScalarBoxes41
import HardCoreActivityThreshold.ScalarBoxes42
import HardCoreActivityThreshold.ScalarBoxes43
import HardCoreActivityThreshold.ScalarBoxes44

namespace HardCoreActivityThreshold
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem scalar_cover_a_global (x : ℝ) (hx : 0<x) (hq : scalarOccupation x∈Set.Icc 0.01 0.941) :
    scalarPartitionFunction x<1.001*x := by
  by_cases h0 : scalarOccupation x≤0.451634033203125
  · have hl0 : scalarOccupation x∈Set.Icc 0.01 0.451634033203125 := ⟨hq.1,h0⟩
    by_cases h1 : scalarOccupation x≤0.437087158203125
    · have hl1 : scalarOccupation x∈Set.Icc 0.01 0.437087158203125 := ⟨hl0.1,h1⟩
      by_cases h2 : scalarOccupation x≤0.4145849609375
      · have hl2 : scalarOccupation x∈Set.Icc 0.01 0.4145849609375 := ⟨hl1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.37003515625
        · have hl3 : scalarOccupation x∈Set.Icc 0.01 0.37003515625 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.286390625
          · have hl4 : scalarOccupation x∈Set.Icc 0.01 0.286390625 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.15546875
            · have hl5 : scalarOccupation x∈Set.Icc 0.01 0.15546875 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.0681875
              · have hl6 : scalarOccupation x∈Set.Icc 0.01 0.0681875 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.024546875
                · have hl7 : scalarOccupation x∈Set.Icc 0.01 0.024546875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0000 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.024546875 0.0681875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.03909375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.024546875 0.03909375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0001 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.03909375 0.0681875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0002 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.0681875 0.15546875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.09728125
                · have hl7 : scalarOccupation x∈Set.Icc 0.0681875 0.09728125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0003 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.09728125 0.15546875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.126375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.09728125 0.126375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0004 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.126375 0.15546875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0005 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.15546875 0.286390625 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.228203125
              · have hl6 : scalarOccupation x∈Set.Icc 0.15546875 0.228203125 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.1845625
                · have hl7 : scalarOccupation x∈Set.Icc 0.15546875 0.1845625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0006 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.1845625 0.228203125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.21365625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.1845625 0.21365625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0007 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.21365625 0.228203125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0008 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.228203125 0.286390625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.257296875
                · have hl7 : scalarOccupation x∈Set.Icc 0.228203125 0.257296875 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.24275
                  · have hl8 : scalarOccupation x∈Set.Icc 0.228203125 0.24275 := ⟨hl7.1,h8⟩
                    exact scalar_box_0009 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.24275 0.257296875 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0010 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.257296875 0.286390625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.27184375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.257296875 0.27184375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0011 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.27184375 0.286390625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0012 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.286390625 0.37003515625 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.3373046875
            · have hl5 : scalarOccupation x∈Set.Icc 0.286390625 0.3373046875 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.315484375
              · have hl6 : scalarOccupation x∈Set.Icc 0.286390625 0.315484375 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.3009375
                · have hl7 : scalarOccupation x∈Set.Icc 0.286390625 0.3009375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0013 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.3009375 0.315484375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.3082109375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.3009375 0.3082109375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0014 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.3082109375 0.315484375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0015 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.315484375 0.3373046875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.3227578125
                · have hl7 : scalarOccupation x∈Set.Icc 0.315484375 0.3227578125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0016 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.3227578125 0.3373046875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.33003125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.3227578125 0.33003125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0017 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.33003125 0.3373046875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0018 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.3373046875 0.37003515625 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.35548828125
              · have hl6 : scalarOccupation x∈Set.Icc 0.3373046875 0.35548828125 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.344578125
                · have hl7 : scalarOccupation x∈Set.Icc 0.3373046875 0.344578125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0019 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.344578125 0.35548828125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.3518515625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.344578125 0.3518515625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0020 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.3518515625 0.35548828125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0021 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.35548828125 0.37003515625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.36276171875
                · have hl7 : scalarOccupation x∈Set.Icc 0.35548828125 0.36276171875 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.359125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.35548828125 0.359125 := ⟨hl7.1,h8⟩
                    exact scalar_box_0022 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.359125 0.36276171875 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0023 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.36276171875 0.37003515625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.3663984375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.36276171875 0.3663984375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0024 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.3663984375 0.37003515625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0025 x hx hr8
        · have hr3 : scalarOccupation x∈Set.Icc 0.37003515625 0.4145849609375 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.39912890625
          · have hl4 : scalarOccupation x∈Set.Icc 0.37003515625 0.39912890625 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.386400390625
            · have hl5 : scalarOccupation x∈Set.Icc 0.37003515625 0.386400390625 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.3809453125
              · have hl6 : scalarOccupation x∈Set.Icc 0.37003515625 0.3809453125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.373671875
                · have hl7 : scalarOccupation x∈Set.Icc 0.37003515625 0.373671875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0026 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.373671875 0.3809453125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.37730859375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.373671875 0.37730859375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0027 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.37730859375 0.3809453125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0028 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.3809453125 0.386400390625 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.382763671875
                · have hl7 : scalarOccupation x∈Set.Icc 0.3809453125 0.382763671875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0029 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.382763671875 0.386400390625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.38458203125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.382763671875 0.38458203125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0030 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.38458203125 0.386400390625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0031 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.386400390625 0.39912890625 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.39185546875
              · have hl6 : scalarOccupation x∈Set.Icc 0.386400390625 0.39185546875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.38821875
                · have hl7 : scalarOccupation x∈Set.Icc 0.386400390625 0.38821875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0032 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.38821875 0.39185546875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.390037109375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.38821875 0.390037109375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0033 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.390037109375 0.39185546875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0034 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.39185546875 0.39912890625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.3954921875
                · have hl7 : scalarOccupation x∈Set.Icc 0.39185546875 0.3954921875 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.393673828125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.39185546875 0.393673828125 := ⟨hl7.1,h8⟩
                    exact scalar_box_0035 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.393673828125 0.3954921875 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0036 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.3954921875 0.39912890625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.397310546875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.3954921875 0.397310546875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0037 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.397310546875 0.39912890625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0038 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.39912890625 0.4145849609375 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.408220703125
            · have hl5 : scalarOccupation x∈Set.Icc 0.39912890625 0.408220703125 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.404583984375
              · have hl6 : scalarOccupation x∈Set.Icc 0.39912890625 0.404583984375 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.400947265625
                · have hl7 : scalarOccupation x∈Set.Icc 0.39912890625 0.400947265625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0039 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.400947265625 0.404583984375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.402765625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.400947265625 0.402765625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0040 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.402765625 0.404583984375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0041 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.404583984375 0.408220703125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.40640234375
                · have hl7 : scalarOccupation x∈Set.Icc 0.404583984375 0.40640234375 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4054931640625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.404583984375 0.4054931640625 := ⟨hl7.1,h8⟩
                    exact scalar_box_0042 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4054931640625 0.40640234375 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0043 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.40640234375 0.408220703125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4073115234375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.40640234375 0.4073115234375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0044 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4073115234375 0.408220703125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0045 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.408220703125 0.4145849609375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.4109482421875
              · have hl6 : scalarOccupation x∈Set.Icc 0.408220703125 0.4109482421875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4091298828125
                · have hl7 : scalarOccupation x∈Set.Icc 0.408220703125 0.4091298828125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0046 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4091298828125 0.4109482421875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4100390625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4091298828125 0.4100390625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0047 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4100390625 0.4109482421875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0048 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4109482421875 0.4145849609375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4127666015625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4109482421875 0.4127666015625 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.411857421875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4109482421875 0.411857421875 := ⟨hl7.1,h8⟩
                    exact scalar_box_0049 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.411857421875 0.4127666015625 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0050 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4127666015625 0.4145849609375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.41367578125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4127666015625 0.41367578125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0051 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.41367578125 0.4145849609375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0052 x hx hr8
      · have hr2 : scalarOccupation x∈Set.Icc 0.4145849609375 0.437087158203125 := ⟨(lt_of_not_ge h2).le,hl1.2⟩
        by_cases h3 : scalarOccupation x≤0.42958642578125
        · have hl3 : scalarOccupation x∈Set.Icc 0.4145849609375 0.42958642578125 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.4236767578125
          · have hl4 : scalarOccupation x∈Set.Icc 0.4145849609375 0.4236767578125 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.4200400390625
            · have hl5 : scalarOccupation x∈Set.Icc 0.4145849609375 0.4200400390625 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4173125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4145849609375 0.4173125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.415494140625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4145849609375 0.415494140625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0053 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.415494140625 0.4173125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4164033203125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.415494140625 0.4164033203125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0054 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4164033203125 0.4173125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0055 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4173125 0.4200400390625 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4182216796875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4173125 0.4182216796875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0056 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4182216796875 0.4200400390625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.419130859375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4182216796875 0.419130859375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0057 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.419130859375 0.4200400390625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0058 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.4200400390625 0.4236767578125 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.4218583984375
              · have hl6 : scalarOccupation x∈Set.Icc 0.4200400390625 0.4218583984375 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.42094921875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4200400390625 0.42094921875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0059 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.42094921875 0.4218583984375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.42140380859375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.42094921875 0.42140380859375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0060 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.42140380859375 0.4218583984375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0061 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4218583984375 0.4236767578125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.422767578125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4218583984375 0.422767578125 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.42231298828125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4218583984375 0.42231298828125 := ⟨hl7.1,h8⟩
                    exact scalar_box_0062 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.42231298828125 0.422767578125 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0063 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.422767578125 0.4236767578125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.42322216796875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.422767578125 0.42322216796875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0064 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.42322216796875 0.4236767578125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0065 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.4236767578125 0.42958642578125 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.426404296875
            · have hl5 : scalarOccupation x∈Set.Icc 0.4236767578125 0.426404296875 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.42504052734375
              · have hl6 : scalarOccupation x∈Set.Icc 0.4236767578125 0.42504052734375 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.42413134765625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4236767578125 0.42413134765625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0066 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.42413134765625 0.42504052734375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4245859375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.42413134765625 0.4245859375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0067 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4245859375 0.42504052734375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0068 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.42504052734375 0.426404296875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4254951171875
                · have hl7 : scalarOccupation x∈Set.Icc 0.42504052734375 0.4254951171875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0069 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4254951171875 0.426404296875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.42594970703125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4254951171875 0.42594970703125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0070 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.42594970703125 0.426404296875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0071 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.426404296875 0.42958642578125 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.42776806640625
              · have hl6 : scalarOccupation x∈Set.Icc 0.426404296875 0.42776806640625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.42685888671875
                · have hl7 : scalarOccupation x∈Set.Icc 0.426404296875 0.42685888671875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0072 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.42685888671875 0.42776806640625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4273134765625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.42685888671875 0.4273134765625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0073 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4273134765625 0.42776806640625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0074 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.42776806640625 0.42958642578125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.42867724609375
                · have hl7 : scalarOccupation x∈Set.Icc 0.42776806640625 0.42867724609375 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.42822265625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.42776806640625 0.42822265625 := ⟨hl7.1,h8⟩
                    exact scalar_box_0075 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.42822265625 0.42867724609375 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0076 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.42867724609375 0.42958642578125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4291318359375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.42867724609375 0.4291318359375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0077 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4291318359375 0.42958642578125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0078 x hx hr8
        · have hr3 : scalarOccupation x∈Set.Icc 0.42958642578125 0.437087158203125 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.433905029296875
          · have hl4 : scalarOccupation x∈Set.Icc 0.42958642578125 0.433905029296875 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.43231396484375
            · have hl5 : scalarOccupation x∈Set.Icc 0.42958642578125 0.43231396484375 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4309501953125
              · have hl6 : scalarOccupation x∈Set.Icc 0.42958642578125 0.4309501953125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.430041015625
                · have hl7 : scalarOccupation x∈Set.Icc 0.42958642578125 0.430041015625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0079 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.430041015625 0.4309501953125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.43049560546875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.430041015625 0.43049560546875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0080 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.43049560546875 0.4309501953125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0081 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4309501953125 0.43231396484375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.43140478515625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4309501953125 0.43140478515625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0082 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.43140478515625 0.43231396484375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.431859375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.43140478515625 0.431859375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0083 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.431859375 0.43231396484375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0084 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.43231396484375 0.433905029296875 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.432995849609375
              · have hl6 : scalarOccupation x∈Set.Icc 0.43231396484375 0.432995849609375 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.432541259765625
                · have hl7 : scalarOccupation x∈Set.Icc 0.43231396484375 0.432541259765625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0085 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.432541259765625 0.432995849609375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4327685546875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.432541259765625 0.4327685546875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0086 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4327685546875 0.432995849609375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0087 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.432995849609375 0.433905029296875 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.433450439453125
                · have hl7 : scalarOccupation x∈Set.Icc 0.432995849609375 0.433450439453125 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.43322314453125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.432995849609375 0.43322314453125 := ⟨hl7.1,h8⟩
                    exact scalar_box_0088 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.43322314453125 0.433450439453125 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0089 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.433450439453125 0.433905029296875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.433677734375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.433450439453125 0.433677734375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0090 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.433677734375 0.433905029296875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0091 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.433905029296875 0.437087158203125 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.43549609375
            · have hl5 : scalarOccupation x∈Set.Icc 0.433905029296875 0.43549609375 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4345869140625
              · have hl6 : scalarOccupation x∈Set.Icc 0.433905029296875 0.4345869140625 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.43413232421875
                · have hl7 : scalarOccupation x∈Set.Icc 0.433905029296875 0.43413232421875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0092 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.43413232421875 0.4345869140625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.434359619140625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.43413232421875 0.434359619140625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0093 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.434359619140625 0.4345869140625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0094 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4345869140625 0.43549609375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.43504150390625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4345869140625 0.43504150390625 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.434814208984375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4345869140625 0.434814208984375 := ⟨hl7.1,h8⟩
                    exact scalar_box_0095 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.434814208984375 0.43504150390625 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0096 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.43504150390625 0.43549609375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.435268798828125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.43504150390625 0.435268798828125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0097 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.435268798828125 0.43549609375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0098 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.43549609375 0.437087158203125 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.436177978515625
              · have hl6 : scalarOccupation x∈Set.Icc 0.43549609375 0.436177978515625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.435723388671875
                · have hl7 : scalarOccupation x∈Set.Icc 0.43549609375 0.435723388671875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0099 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.435723388671875 0.436177978515625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.43595068359375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.435723388671875 0.43595068359375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0100 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.43595068359375 0.436177978515625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0101 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.436177978515625 0.437087158203125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.436632568359375
                · have hl7 : scalarOccupation x∈Set.Icc 0.436177978515625 0.436632568359375 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4364052734375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.436177978515625 0.4364052734375 := ⟨hl7.1,h8⟩
                    exact scalar_box_0102 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4364052734375 0.436632568359375 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0103 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.436632568359375 0.437087158203125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.43685986328125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.436632568359375 0.43685986328125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0104 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.43685986328125 0.437087158203125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0105 x hx hr8
    · have hr1 : scalarOccupation x∈Set.Icc 0.437087158203125 0.451634033203125 := ⟨(lt_of_not_ge h1).le,hl0.2⟩
      by_cases h2 : scalarOccupation x≤0.4454970703125
      · have hl2 : scalarOccupation x∈Set.Icc 0.437087158203125 0.4454970703125 := ⟨hr1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.4424285888671875
        · have hl3 : scalarOccupation x∈Set.Icc 0.437087158203125 0.4424285888671875 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.4400419921875
          · have hl4 : scalarOccupation x∈Set.Icc 0.437087158203125 0.4400419921875 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.438450927734375
            · have hl5 : scalarOccupation x∈Set.Icc 0.437087158203125 0.438450927734375 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.43776904296875
              · have hl6 : scalarOccupation x∈Set.Icc 0.437087158203125 0.43776904296875 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.437314453125
                · have hl7 : scalarOccupation x∈Set.Icc 0.437087158203125 0.437314453125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0106 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.437314453125 0.43776904296875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.437541748046875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.437314453125 0.437541748046875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0107 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.437541748046875 0.43776904296875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0108 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.43776904296875 0.438450927734375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.437996337890625
                · have hl7 : scalarOccupation x∈Set.Icc 0.43776904296875 0.437996337890625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0109 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.437996337890625 0.438450927734375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4382236328125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.437996337890625 0.4382236328125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0110 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4382236328125 0.438450927734375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0111 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.438450927734375 0.4400419921875 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.4391328125
              · have hl6 : scalarOccupation x∈Set.Icc 0.438450927734375 0.4391328125 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.43867822265625
                · have hl7 : scalarOccupation x∈Set.Icc 0.438450927734375 0.43867822265625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0112 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.43867822265625 0.4391328125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.438905517578125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.43867822265625 0.438905517578125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0113 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.438905517578125 0.4391328125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0114 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4391328125 0.4400419921875 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.43958740234375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4391328125 0.43958740234375 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.439360107421875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4391328125 0.439360107421875 := ⟨hl7.1,h8⟩
                    exact scalar_box_0115 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.439360107421875 0.43958740234375 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0116 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.43958740234375 0.4400419921875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.439814697265625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.43958740234375 0.439814697265625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0117 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.439814697265625 0.4400419921875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0118 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.4400419921875 0.4424285888671875 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.44140576171875
            · have hl5 : scalarOccupation x∈Set.Icc 0.4400419921875 0.44140576171875 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.440723876953125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4400419921875 0.440723876953125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.440269287109375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4400419921875 0.440269287109375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0119 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.440269287109375 0.440723876953125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.44049658203125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.440269287109375 0.44049658203125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0120 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.44049658203125 0.440723876953125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0121 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.440723876953125 0.44140576171875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.440951171875
                · have hl7 : scalarOccupation x∈Set.Icc 0.440723876953125 0.440951171875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0122 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.440951171875 0.44140576171875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.441178466796875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.440951171875 0.441178466796875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0123 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.441178466796875 0.44140576171875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0124 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.44140576171875 0.4424285888671875 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.4419739990234375
              · have hl6 : scalarOccupation x∈Set.Icc 0.44140576171875 0.4419739990234375 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.441633056640625
                · have hl7 : scalarOccupation x∈Set.Icc 0.44140576171875 0.441633056640625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0125 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.441633056640625 0.4419739990234375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4418603515625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.441633056640625 0.4418603515625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0126 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4418603515625 0.4419739990234375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0127 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4419739990234375 0.4424285888671875 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4422012939453125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4419739990234375 0.4422012939453125 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.442087646484375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4419739990234375 0.442087646484375 := ⟨hl7.1,h8⟩
                    exact scalar_box_0128 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.442087646484375 0.4422012939453125 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0129 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4422012939453125 0.4424285888671875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.44231494140625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4422012939453125 0.44231494140625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0130 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.44231494140625 0.4424285888671875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0131 x hx hr8
        · have hr3 : scalarOccupation x∈Set.Icc 0.4424285888671875 0.4454970703125 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.443906005859375
          · have hl4 : scalarOccupation x∈Set.Icc 0.4424285888671875 0.443906005859375 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.4431104736328125
            · have hl5 : scalarOccupation x∈Set.Icc 0.4424285888671875 0.4431104736328125 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.44276953125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4424285888671875 0.44276953125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.442542236328125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4424285888671875 0.442542236328125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0132 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.442542236328125 0.44276953125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4426558837890625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.442542236328125 0.4426558837890625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0133 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4426558837890625 0.44276953125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0134 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.44276953125 0.4431104736328125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4428831787109375
                · have hl7 : scalarOccupation x∈Set.Icc 0.44276953125 0.4428831787109375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0135 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4428831787109375 0.4431104736328125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.442996826171875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4428831787109375 0.442996826171875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0136 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.442996826171875 0.4431104736328125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0137 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.4431104736328125 0.443906005859375 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.443451416015625
              · have hl6 : scalarOccupation x∈Set.Icc 0.4431104736328125 0.443451416015625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.44322412109375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4431104736328125 0.44322412109375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0138 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.44322412109375 0.443451416015625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4433377685546875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.44322412109375 0.4433377685546875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0139 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4433377685546875 0.443451416015625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0140 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.443451416015625 0.443906005859375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4436787109375
                · have hl7 : scalarOccupation x∈Set.Icc 0.443451416015625 0.4436787109375 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4435650634765625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.443451416015625 0.4435650634765625 := ⟨hl7.1,h8⟩
                    exact scalar_box_0141 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4435650634765625 0.4436787109375 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0142 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4436787109375 0.443906005859375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4437923583984375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4436787109375 0.4437923583984375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0143 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4437923583984375 0.443906005859375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0144 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.443906005859375 0.4454970703125 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.4447015380859375
            · have hl5 : scalarOccupation x∈Set.Icc 0.443906005859375 0.4447015380859375 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4442469482421875
              · have hl6 : scalarOccupation x∈Set.Icc 0.443906005859375 0.4442469482421875 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4440196533203125
                · have hl7 : scalarOccupation x∈Set.Icc 0.443906005859375 0.4440196533203125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0145 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4440196533203125 0.4442469482421875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.44413330078125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4440196533203125 0.44413330078125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0146 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.44413330078125 0.4442469482421875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0147 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4442469482421875 0.4447015380859375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4444742431640625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4442469482421875 0.4444742431640625 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.444360595703125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4442469482421875 0.444360595703125 := ⟨hl7.1,h8⟩
                    exact scalar_box_0148 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.444360595703125 0.4444742431640625 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0149 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4444742431640625 0.4447015380859375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.444587890625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4444742431640625 0.444587890625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0150 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.444587890625 0.4447015380859375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0151 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.4447015380859375 0.4454970703125 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.44504248046875
              · have hl6 : scalarOccupation x∈Set.Icc 0.4447015380859375 0.44504248046875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.444815185546875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4447015380859375 0.444815185546875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0152 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.444815185546875 0.44504248046875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4449288330078125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.444815185546875 0.4449288330078125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0153 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4449288330078125 0.44504248046875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0154 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.44504248046875 0.4454970703125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.445269775390625
                · have hl7 : scalarOccupation x∈Set.Icc 0.44504248046875 0.445269775390625 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4451561279296875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.44504248046875 0.4451561279296875 := ⟨hl7.1,h8⟩
                    exact scalar_box_0155 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4451561279296875 0.445269775390625 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0156 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.445269775390625 0.4454970703125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4453834228515625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.445269775390625 0.4453834228515625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0157 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4453834228515625 0.4454970703125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0158 x hx hr8
      · have hr2 : scalarOccupation x∈Set.Icc 0.4454970703125 0.451634033203125 := ⟨(lt_of_not_ge h2).le,hr1.2⟩
        by_cases h3 : scalarOccupation x≤0.4485655517578125
        · have hl3 : scalarOccupation x∈Set.Icc 0.4454970703125 0.4485655517578125 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.4469744873046875
          · have hl4 : scalarOccupation x∈Set.Icc 0.4454970703125 0.4469744873046875 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.446178955078125
            · have hl5 : scalarOccupation x∈Set.Icc 0.4454970703125 0.446178955078125 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4458380126953125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4454970703125 0.4458380126953125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4456107177734375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4454970703125 0.4456107177734375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0159 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4456107177734375 0.4458380126953125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.445724365234375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4456107177734375 0.445724365234375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0160 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.445724365234375 0.4458380126953125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0161 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4458380126953125 0.446178955078125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.44595166015625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4458380126953125 0.44595166015625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0162 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.44595166015625 0.446178955078125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4460653076171875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.44595166015625 0.4460653076171875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0163 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4460653076171875 0.446178955078125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0164 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.446178955078125 0.4469744873046875 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.4465198974609375
              · have hl6 : scalarOccupation x∈Set.Icc 0.446178955078125 0.4465198974609375 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4462926025390625
                · have hl7 : scalarOccupation x∈Set.Icc 0.446178955078125 0.4462926025390625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0165 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4462926025390625 0.4465198974609375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.44640625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4462926025390625 0.44640625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0166 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.44640625 0.4465198974609375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0167 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4465198974609375 0.4469744873046875 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4467471923828125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4465198974609375 0.4467471923828125 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.446633544921875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4465198974609375 0.446633544921875 := ⟨hl7.1,h8⟩
                    exact scalar_box_0168 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.446633544921875 0.4467471923828125 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0169 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4467471923828125 0.4469744873046875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.44686083984375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4467471923828125 0.44686083984375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0170 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.44686083984375 0.4469744873046875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0171 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.4469744873046875 0.4485655517578125 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.44777001953125
            · have hl5 : scalarOccupation x∈Set.Icc 0.4469744873046875 0.44777001953125 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4473154296875
              · have hl6 : scalarOccupation x∈Set.Icc 0.4469744873046875 0.4473154296875 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.447088134765625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4469744873046875 0.447088134765625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0172 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.447088134765625 0.4473154296875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4472017822265625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.447088134765625 0.4472017822265625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0173 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4472017822265625 0.4473154296875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0174 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4473154296875 0.44777001953125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.447542724609375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4473154296875 0.447542724609375 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4474290771484375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4473154296875 0.4474290771484375 := ⟨hl7.1,h8⟩
                    exact scalar_box_0175 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4474290771484375 0.447542724609375 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0176 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.447542724609375 0.44777001953125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4476563720703125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.447542724609375 0.4476563720703125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0177 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4476563720703125 0.44777001953125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0178 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.44777001953125 0.4485655517578125 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.4481109619140625
              · have hl6 : scalarOccupation x∈Set.Icc 0.44777001953125 0.4481109619140625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4478836669921875
                · have hl7 : scalarOccupation x∈Set.Icc 0.44777001953125 0.4478836669921875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0179 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4478836669921875 0.4481109619140625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.447997314453125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4478836669921875 0.447997314453125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0180 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.447997314453125 0.4481109619140625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0181 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4481109619140625 0.4485655517578125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4483382568359375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4481109619140625 0.4483382568359375 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.448224609375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4481109619140625 0.448224609375 := ⟨hl7.1,h8⟩
                    exact scalar_box_0182 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.448224609375 0.4483382568359375 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0183 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4483382568359375 0.4485655517578125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.448451904296875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4483382568359375 0.448451904296875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0184 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.448451904296875 0.4485655517578125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0185 x hx hr8
        · have hr3 : scalarOccupation x∈Set.Icc 0.4485655517578125 0.451634033203125 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.45004296875
          · have hl4 : scalarOccupation x∈Set.Icc 0.4485655517578125 0.45004296875 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.4492474365234375
            · have hl5 : scalarOccupation x∈Set.Icc 0.4485655517578125 0.4492474365234375 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.448906494140625
              · have hl6 : scalarOccupation x∈Set.Icc 0.4485655517578125 0.448906494140625 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.44867919921875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4485655517578125 0.44867919921875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0186 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.44867919921875 0.448906494140625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4487928466796875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.44867919921875 0.4487928466796875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0187 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4487928466796875 0.448906494140625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0188 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.448906494140625 0.4492474365234375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4490201416015625
                · have hl7 : scalarOccupation x∈Set.Icc 0.448906494140625 0.4490201416015625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0189 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4490201416015625 0.4492474365234375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4491337890625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4490201416015625 0.4491337890625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0190 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4491337890625 0.4492474365234375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0191 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.4492474365234375 0.45004296875 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.44958837890625
              · have hl6 : scalarOccupation x∈Set.Icc 0.4492474365234375 0.44958837890625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.449361083984375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4492474365234375 0.449361083984375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0192 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.449361083984375 0.44958837890625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4494747314453125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.449361083984375 0.4494747314453125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0193 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4494747314453125 0.44958837890625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0194 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.44958837890625 0.45004296875 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.449815673828125
                · have hl7 : scalarOccupation x∈Set.Icc 0.44958837890625 0.449815673828125 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4497020263671875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.44958837890625 0.4497020263671875 := ⟨hl7.1,h8⟩
                    exact scalar_box_0195 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4497020263671875 0.449815673828125 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0196 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.449815673828125 0.45004296875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4499293212890625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.449815673828125 0.4499293212890625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0197 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4499293212890625 0.45004296875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0198 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.45004296875 0.451634033203125 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.4508385009765625
            · have hl5 : scalarOccupation x∈Set.Icc 0.45004296875 0.4508385009765625 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4503839111328125
              · have hl6 : scalarOccupation x∈Set.Icc 0.45004296875 0.4503839111328125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4501566162109375
                · have hl7 : scalarOccupation x∈Set.Icc 0.45004296875 0.4501566162109375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0199 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4501566162109375 0.4503839111328125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.450270263671875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4501566162109375 0.450270263671875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0200 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.450270263671875 0.4503839111328125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0201 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4503839111328125 0.4508385009765625 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4506112060546875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4503839111328125 0.4506112060546875 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.45049755859375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4503839111328125 0.45049755859375 := ⟨hl7.1,h8⟩
                    exact scalar_box_0202 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.45049755859375 0.4506112060546875 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0203 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4506112060546875 0.4508385009765625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.450724853515625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4506112060546875 0.450724853515625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0204 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.450724853515625 0.4508385009765625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0205 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.4508385009765625 0.451634033203125 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.451179443359375
              · have hl6 : scalarOccupation x∈Set.Icc 0.4508385009765625 0.451179443359375 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4509521484375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4508385009765625 0.4509521484375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0206 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4509521484375 0.451179443359375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4510657958984375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4509521484375 0.4510657958984375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0207 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4510657958984375 0.451179443359375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0208 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.451179443359375 0.451634033203125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.45140673828125
                · have hl7 : scalarOccupation x∈Set.Icc 0.451179443359375 0.45140673828125 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4512930908203125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.451179443359375 0.4512930908203125 := ⟨hl7.1,h8⟩
                    exact scalar_box_0209 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4512930908203125 0.45140673828125 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0210 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.45140673828125 0.451634033203125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4515203857421875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.45140673828125 0.4515203857421875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0211 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4515203857421875 0.451634033203125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0212 x hx hr8
  · have hr0 : scalarOccupation x∈Set.Icc 0.451634033203125 0.941 := ⟨(lt_of_not_ge h0).le,hq.2⟩
    by_cases h1 : scalarOccupation x≤0.46413525390625
    · have hl1 : scalarOccupation x∈Set.Icc 0.451634033203125 0.46413525390625 := ⟨hr0.1,h1⟩
      by_cases h2 : scalarOccupation x≤0.4576573486328125
      · have hl2 : scalarOccupation x∈Set.Icc 0.451634033203125 0.4576573486328125 := ⟨hl1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.4545888671875
        · have hl3 : scalarOccupation x∈Set.Icc 0.451634033203125 0.4545888671875 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.4531114501953125
          · have hl4 : scalarOccupation x∈Set.Icc 0.451634033203125 0.4531114501953125 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.45231591796875
            · have hl5 : scalarOccupation x∈Set.Icc 0.451634033203125 0.45231591796875 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4519749755859375
              · have hl6 : scalarOccupation x∈Set.Icc 0.451634033203125 0.4519749755859375 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4517476806640625
                · have hl7 : scalarOccupation x∈Set.Icc 0.451634033203125 0.4517476806640625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0213 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4517476806640625 0.4519749755859375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.451861328125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4517476806640625 0.451861328125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0214 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.451861328125 0.4519749755859375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0215 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4519749755859375 0.45231591796875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.452088623046875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4519749755859375 0.452088623046875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0216 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.452088623046875 0.45231591796875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4522022705078125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.452088623046875 0.4522022705078125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0217 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4522022705078125 0.45231591796875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0218 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.45231591796875 0.4531114501953125 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.4526568603515625
              · have hl6 : scalarOccupation x∈Set.Icc 0.45231591796875 0.4526568603515625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4524295654296875
                · have hl7 : scalarOccupation x∈Set.Icc 0.45231591796875 0.4524295654296875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0219 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4524295654296875 0.4526568603515625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.452543212890625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4524295654296875 0.452543212890625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0220 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.452543212890625 0.4526568603515625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0221 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4526568603515625 0.4531114501953125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4528841552734375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4526568603515625 0.4528841552734375 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4527705078125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4526568603515625 0.4527705078125 := ⟨hl7.1,h8⟩
                    exact scalar_box_0222 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4527705078125 0.4528841552734375 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0223 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4528841552734375 0.4531114501953125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.452997802734375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4528841552734375 0.452997802734375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0224 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.452997802734375 0.4531114501953125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0225 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.4531114501953125 0.4545888671875 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.4537933349609375
            · have hl5 : scalarOccupation x∈Set.Icc 0.4531114501953125 0.4537933349609375 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.453452392578125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4531114501953125 0.453452392578125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.45322509765625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4531114501953125 0.45322509765625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0226 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.45322509765625 0.453452392578125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4533387451171875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.45322509765625 0.4533387451171875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0227 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4533387451171875 0.453452392578125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0228 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.453452392578125 0.4537933349609375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4535660400390625
                · have hl7 : scalarOccupation x∈Set.Icc 0.453452392578125 0.4535660400390625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0229 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4535660400390625 0.4537933349609375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4536796875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4535660400390625 0.4536796875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0230 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4536796875 0.4537933349609375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0231 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.4537933349609375 0.4545888671875 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.45413427734375
              · have hl6 : scalarOccupation x∈Set.Icc 0.4537933349609375 0.45413427734375 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.453906982421875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4537933349609375 0.453906982421875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0232 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.453906982421875 0.45413427734375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4540206298828125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.453906982421875 0.4540206298828125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0233 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4540206298828125 0.45413427734375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0234 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.45413427734375 0.4545888671875 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.454361572265625
                · have hl7 : scalarOccupation x∈Set.Icc 0.45413427734375 0.454361572265625 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4542479248046875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.45413427734375 0.4542479248046875 := ⟨hl7.1,h8⟩
                    exact scalar_box_0235 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4542479248046875 0.454361572265625 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0236 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.454361572265625 0.4545888671875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4544752197265625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.454361572265625 0.4544752197265625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0237 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4544752197265625 0.4545888671875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0238 x hx hr8
        · have hr3 : scalarOccupation x∈Set.Icc 0.4545888671875 0.4576573486328125 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.4560662841796875
          · have hl4 : scalarOccupation x∈Set.Icc 0.4545888671875 0.4560662841796875 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.455270751953125
            · have hl5 : scalarOccupation x∈Set.Icc 0.4545888671875 0.455270751953125 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4549298095703125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4545888671875 0.4549298095703125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4547025146484375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4545888671875 0.4547025146484375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0239 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4547025146484375 0.4549298095703125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.454816162109375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4547025146484375 0.454816162109375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0240 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.454816162109375 0.4549298095703125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0241 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4549298095703125 0.455270751953125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.45504345703125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4549298095703125 0.45504345703125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0242 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.45504345703125 0.455270751953125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4551571044921875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.45504345703125 0.4551571044921875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0243 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4551571044921875 0.455270751953125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0244 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.455270751953125 0.4560662841796875 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.4556116943359375
              · have hl6 : scalarOccupation x∈Set.Icc 0.455270751953125 0.4556116943359375 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4553843994140625
                · have hl7 : scalarOccupation x∈Set.Icc 0.455270751953125 0.4553843994140625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0245 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4553843994140625 0.4556116943359375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.455498046875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4553843994140625 0.455498046875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0246 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.455498046875 0.4556116943359375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0247 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4556116943359375 0.4560662841796875 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4558389892578125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4556116943359375 0.4558389892578125 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.455725341796875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4556116943359375 0.455725341796875 := ⟨hl7.1,h8⟩
                    exact scalar_box_0248 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.455725341796875 0.4558389892578125 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0249 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4558389892578125 0.4560662841796875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.45595263671875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4558389892578125 0.45595263671875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0250 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.45595263671875 0.4560662841796875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0251 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.4560662841796875 0.4576573486328125 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.45686181640625
            · have hl5 : scalarOccupation x∈Set.Icc 0.4560662841796875 0.45686181640625 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4564072265625
              · have hl6 : scalarOccupation x∈Set.Icc 0.4560662841796875 0.4564072265625 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.456179931640625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4560662841796875 0.456179931640625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0252 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.456179931640625 0.4564072265625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4562935791015625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.456179931640625 0.4562935791015625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0253 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4562935791015625 0.4564072265625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0254 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4564072265625 0.45686181640625 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.456634521484375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4564072265625 0.456634521484375 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4565208740234375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4564072265625 0.4565208740234375 := ⟨hl7.1,h8⟩
                    exact scalar_box_0255 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4565208740234375 0.456634521484375 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0256 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.456634521484375 0.45686181640625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4567481689453125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.456634521484375 0.4567481689453125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0257 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4567481689453125 0.45686181640625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0258 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.45686181640625 0.4576573486328125 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.4572027587890625
              · have hl6 : scalarOccupation x∈Set.Icc 0.45686181640625 0.4572027587890625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4569754638671875
                · have hl7 : scalarOccupation x∈Set.Icc 0.45686181640625 0.4569754638671875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0259 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4569754638671875 0.4572027587890625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.457089111328125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4569754638671875 0.457089111328125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0260 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.457089111328125 0.4572027587890625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0261 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4572027587890625 0.4576573486328125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4574300537109375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4572027587890625 0.4574300537109375 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.45731640625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4572027587890625 0.45731640625 := ⟨hl7.1,h8⟩
                    exact scalar_box_0262 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.45731640625 0.4574300537109375 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0263 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4574300537109375 0.4576573486328125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.457543701171875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4574300537109375 0.457543701171875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0264 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.457543701171875 0.4576573486328125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0265 x hx hr8
      · have hr2 : scalarOccupation x∈Set.Icc 0.4576573486328125 0.46413525390625 := ⟨(lt_of_not_ge h2).le,hl1.2⟩
        by_cases h3 : scalarOccupation x≤0.4606121826171875
        · have hl3 : scalarOccupation x∈Set.Icc 0.4576573486328125 0.4606121826171875 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.459134765625
          · have hl4 : scalarOccupation x∈Set.Icc 0.4576573486328125 0.459134765625 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.4583392333984375
            · have hl5 : scalarOccupation x∈Set.Icc 0.4576573486328125 0.4583392333984375 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.457998291015625
              · have hl6 : scalarOccupation x∈Set.Icc 0.4576573486328125 0.457998291015625 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.45777099609375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4576573486328125 0.45777099609375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0266 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.45777099609375 0.457998291015625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4578846435546875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.45777099609375 0.4578846435546875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0267 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4578846435546875 0.457998291015625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0268 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.457998291015625 0.4583392333984375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4581119384765625
                · have hl7 : scalarOccupation x∈Set.Icc 0.457998291015625 0.4581119384765625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0269 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4581119384765625 0.4583392333984375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4582255859375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4581119384765625 0.4582255859375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0270 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4582255859375 0.4583392333984375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0271 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.4583392333984375 0.459134765625 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.45868017578125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4583392333984375 0.45868017578125 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.458452880859375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4583392333984375 0.458452880859375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0272 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.458452880859375 0.45868017578125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4585665283203125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.458452880859375 0.4585665283203125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0273 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4585665283203125 0.45868017578125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0274 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.45868017578125 0.459134765625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.458907470703125
                · have hl7 : scalarOccupation x∈Set.Icc 0.45868017578125 0.458907470703125 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4587938232421875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.45868017578125 0.4587938232421875 := ⟨hl7.1,h8⟩
                    exact scalar_box_0275 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4587938232421875 0.458907470703125 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0276 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.458907470703125 0.459134765625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4590211181640625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.458907470703125 0.4590211181640625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0277 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4590211181640625 0.459134765625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0278 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.459134765625 0.4606121826171875 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.459816650390625
            · have hl5 : scalarOccupation x∈Set.Icc 0.459134765625 0.459816650390625 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4594757080078125
              · have hl6 : scalarOccupation x∈Set.Icc 0.459134765625 0.4594757080078125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4592484130859375
                · have hl7 : scalarOccupation x∈Set.Icc 0.459134765625 0.4592484130859375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0279 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4592484130859375 0.4594757080078125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.459362060546875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4592484130859375 0.459362060546875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0280 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.459362060546875 0.4594757080078125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0281 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4594757080078125 0.459816650390625 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.45958935546875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4594757080078125 0.45958935546875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0282 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.45958935546875 0.459816650390625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4597030029296875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.45958935546875 0.4597030029296875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0283 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4597030029296875 0.459816650390625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0284 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.459816650390625 0.4606121826171875 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.4601575927734375
              · have hl6 : scalarOccupation x∈Set.Icc 0.459816650390625 0.4601575927734375 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4599302978515625
                · have hl7 : scalarOccupation x∈Set.Icc 0.459816650390625 0.4599302978515625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0285 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4599302978515625 0.4601575927734375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4600439453125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4599302978515625 0.4600439453125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0286 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4600439453125 0.4601575927734375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0287 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4601575927734375 0.4606121826171875 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4603848876953125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4601575927734375 0.4603848876953125 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.460271240234375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4601575927734375 0.460271240234375 := ⟨hl7.1,h8⟩
                    exact scalar_box_0288 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.460271240234375 0.4603848876953125 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0289 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4603848876953125 0.4606121826171875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.46049853515625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4603848876953125 0.46049853515625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0290 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.46049853515625 0.4606121826171875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0291 x hx hr8
        · have hr3 : scalarOccupation x∈Set.Icc 0.4606121826171875 0.46413525390625 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.462089599609375
          · have hl4 : scalarOccupation x∈Set.Icc 0.4606121826171875 0.462089599609375 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.4612940673828125
            · have hl5 : scalarOccupation x∈Set.Icc 0.4606121826171875 0.4612940673828125 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.460953125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4606121826171875 0.460953125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.460725830078125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4606121826171875 0.460725830078125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0292 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.460725830078125 0.460953125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4608394775390625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.460725830078125 0.4608394775390625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0293 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4608394775390625 0.460953125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0294 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.460953125 0.4612940673828125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4610667724609375
                · have hl7 : scalarOccupation x∈Set.Icc 0.460953125 0.4610667724609375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0295 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4610667724609375 0.4612940673828125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.461180419921875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4610667724609375 0.461180419921875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0296 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.461180419921875 0.4612940673828125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0297 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.4612940673828125 0.462089599609375 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.461635009765625
              · have hl6 : scalarOccupation x∈Set.Icc 0.4612940673828125 0.461635009765625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.46140771484375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4612940673828125 0.46140771484375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0298 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46140771484375 0.461635009765625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4615213623046875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.46140771484375 0.4615213623046875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0299 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4615213623046875 0.461635009765625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0300 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.461635009765625 0.462089599609375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4618623046875
                · have hl7 : scalarOccupation x∈Set.Icc 0.461635009765625 0.4618623046875 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4617486572265625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.461635009765625 0.4617486572265625 := ⟨hl7.1,h8⟩
                    exact scalar_box_0301 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4617486572265625 0.4618623046875 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0302 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4618623046875 0.462089599609375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4619759521484375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4618623046875 0.4619759521484375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0303 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4619759521484375 0.462089599609375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0304 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.462089599609375 0.46413525390625 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.4628851318359375
            · have hl5 : scalarOccupation x∈Set.Icc 0.462089599609375 0.4628851318359375 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4624305419921875
              · have hl6 : scalarOccupation x∈Set.Icc 0.462089599609375 0.4624305419921875 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4622032470703125
                · have hl7 : scalarOccupation x∈Set.Icc 0.462089599609375 0.4622032470703125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0305 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4622032470703125 0.4624305419921875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.46231689453125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4622032470703125 0.46231689453125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0306 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.46231689453125 0.4624305419921875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0307 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4624305419921875 0.4628851318359375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4626578369140625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4624305419921875 0.4626578369140625 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.462544189453125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4624305419921875 0.462544189453125 := ⟨hl7.1,h8⟩
                    exact scalar_box_0308 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.462544189453125 0.4626578369140625 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0309 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4626578369140625 0.4628851318359375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.462771484375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4626578369140625 0.462771484375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0310 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.462771484375 0.4628851318359375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0311 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.4628851318359375 0.46413525390625 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.46322607421875
              · have hl6 : scalarOccupation x∈Set.Icc 0.4628851318359375 0.46322607421875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.462998779296875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4628851318359375 0.462998779296875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0312 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.462998779296875 0.46322607421875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4631124267578125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.462998779296875 0.4631124267578125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0313 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4631124267578125 0.46322607421875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0314 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.46322607421875 0.46413525390625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4636806640625
                · have hl7 : scalarOccupation x∈Set.Icc 0.46322607421875 0.4636806640625 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.463453369140625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.46322607421875 0.463453369140625 := ⟨hl7.1,h8⟩
                    exact scalar_box_0315 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.463453369140625 0.4636806640625 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0316 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4636806640625 0.46413525390625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.463907958984375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4636806640625 0.463907958984375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0317 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.463907958984375 0.46413525390625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0318 x hx hr8
    · have hr1 : scalarOccupation x∈Set.Icc 0.46413525390625 0.941 := ⟨(lt_of_not_ge h1).le,hr0.2⟩
      by_cases h2 : scalarOccupation x≤0.4800458984375
      · have hl2 : scalarOccupation x∈Set.Icc 0.46413525390625 0.4800458984375 := ⟨hr1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.470044921875
        · have hl3 : scalarOccupation x∈Set.Icc 0.46413525390625 0.470044921875 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.467090087890625
          · have hl4 : scalarOccupation x∈Set.Icc 0.46413525390625 0.467090087890625 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.4654990234375
            · have hl5 : scalarOccupation x∈Set.Icc 0.46413525390625 0.4654990234375 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.464817138671875
              · have hl6 : scalarOccupation x∈Set.Icc 0.46413525390625 0.464817138671875 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.464362548828125
                · have hl7 : scalarOccupation x∈Set.Icc 0.46413525390625 0.464362548828125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0319 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.464362548828125 0.464817138671875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.46458984375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.464362548828125 0.46458984375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0320 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.46458984375 0.464817138671875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0321 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.464817138671875 0.4654990234375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.46504443359375
                · have hl7 : scalarOccupation x∈Set.Icc 0.464817138671875 0.46504443359375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0322 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46504443359375 0.4654990234375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.465271728515625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.46504443359375 0.465271728515625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0323 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.465271728515625 0.4654990234375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0324 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.4654990234375 0.467090087890625 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.466180908203125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4654990234375 0.466180908203125 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.465726318359375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4654990234375 0.465726318359375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0325 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.465726318359375 0.466180908203125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.46595361328125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.465726318359375 0.46595361328125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0326 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.46595361328125 0.466180908203125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0327 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.466180908203125 0.467090087890625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.466635498046875
                · have hl7 : scalarOccupation x∈Set.Icc 0.466180908203125 0.466635498046875 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.466408203125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.466180908203125 0.466408203125 := ⟨hl7.1,h8⟩
                    exact scalar_box_0328 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.466408203125 0.466635498046875 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0329 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.466635498046875 0.467090087890625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.46686279296875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.466635498046875 0.46686279296875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0330 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.46686279296875 0.467090087890625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0331 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.467090087890625 0.470044921875 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.468453857421875
            · have hl5 : scalarOccupation x∈Set.Icc 0.467090087890625 0.468453857421875 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.46777197265625
              · have hl6 : scalarOccupation x∈Set.Icc 0.467090087890625 0.46777197265625 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4673173828125
                · have hl7 : scalarOccupation x∈Set.Icc 0.467090087890625 0.4673173828125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0332 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4673173828125 0.46777197265625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.467544677734375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4673173828125 0.467544677734375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0333 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.467544677734375 0.46777197265625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0334 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.46777197265625 0.468453857421875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.467999267578125
                · have hl7 : scalarOccupation x∈Set.Icc 0.46777197265625 0.467999267578125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0335 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.467999267578125 0.468453857421875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4682265625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.467999267578125 0.4682265625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0336 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4682265625 0.468453857421875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0337 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.468453857421875 0.470044921875 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.4691357421875
              · have hl6 : scalarOccupation x∈Set.Icc 0.468453857421875 0.4691357421875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.46868115234375
                · have hl7 : scalarOccupation x∈Set.Icc 0.468453857421875 0.46868115234375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0338 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46868115234375 0.4691357421875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.468908447265625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.46868115234375 0.468908447265625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0339 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.468908447265625 0.4691357421875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0340 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4691357421875 0.470044921875 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.46959033203125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4691357421875 0.46959033203125 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.469363037109375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4691357421875 0.469363037109375 := ⟨hl7.1,h8⟩
                    exact scalar_box_0341 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.469363037109375 0.46959033203125 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0342 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.46959033203125 0.470044921875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.469817626953125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.46959033203125 0.469817626953125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0343 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.469817626953125 0.470044921875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0344 x hx hr8
        · have hr3 : scalarOccupation x∈Set.Icc 0.470044921875 0.4800458984375 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.473681640625
          · have hl4 : scalarOccupation x∈Set.Icc 0.470044921875 0.473681640625 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.47140869140625
            · have hl5 : scalarOccupation x∈Set.Icc 0.470044921875 0.47140869140625 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.470726806640625
              · have hl6 : scalarOccupation x∈Set.Icc 0.470044921875 0.470726806640625 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.470272216796875
                · have hl7 : scalarOccupation x∈Set.Icc 0.470044921875 0.470272216796875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0345 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.470272216796875 0.470726806640625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.47049951171875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.470272216796875 0.47049951171875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0346 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.47049951171875 0.470726806640625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0347 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.470726806640625 0.47140869140625 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4709541015625
                · have hl7 : scalarOccupation x∈Set.Icc 0.470726806640625 0.4709541015625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0348 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4709541015625 0.47140869140625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.471181396484375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4709541015625 0.471181396484375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0349 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.471181396484375 0.47140869140625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0350 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.47140869140625 0.473681640625 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.472090576171875
              · have hl6 : scalarOccupation x∈Set.Icc 0.47140869140625 0.472090576171875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.471635986328125
                · have hl7 : scalarOccupation x∈Set.Icc 0.47140869140625 0.471635986328125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0351 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.471635986328125 0.472090576171875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.47186328125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.471635986328125 0.47186328125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0352 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.47186328125 0.472090576171875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0353 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.472090576171875 0.473681640625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4727724609375
                · have hl7 : scalarOccupation x∈Set.Icc 0.472090576171875 0.4727724609375 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.47231787109375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.472090576171875 0.47231787109375 := ⟨hl7.1,h8⟩
                    exact scalar_box_0354 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.47231787109375 0.4727724609375 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0355 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4727724609375 0.473681640625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.47322705078125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4727724609375 0.47322705078125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0356 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.47322705078125 0.473681640625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0357 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.473681640625 0.4800458984375 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.47686376953125
            · have hl5 : scalarOccupation x∈Set.Icc 0.473681640625 0.47686376953125 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.47504541015625
              · have hl6 : scalarOccupation x∈Set.Icc 0.473681640625 0.47504541015625 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.47413623046875
                · have hl7 : scalarOccupation x∈Set.Icc 0.473681640625 0.47413623046875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0358 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.47413623046875 0.47504541015625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4745908203125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.47413623046875 0.4745908203125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0359 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4745908203125 0.47504541015625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0360 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.47504541015625 0.47686376953125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.47595458984375
                · have hl7 : scalarOccupation x∈Set.Icc 0.47504541015625 0.47595458984375 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4755
                  · have hl8 : scalarOccupation x∈Set.Icc 0.47504541015625 0.4755 := ⟨hl7.1,h8⟩
                    exact scalar_box_0361 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4755 0.47595458984375 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0362 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.47595458984375 0.47686376953125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4764091796875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.47595458984375 0.4764091796875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0363 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4764091796875 0.47686376953125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0364 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.47686376953125 0.4800458984375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.4782275390625
              · have hl6 : scalarOccupation x∈Set.Icc 0.47686376953125 0.4782275390625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.477318359375
                · have hl7 : scalarOccupation x∈Set.Icc 0.47686376953125 0.477318359375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0365 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.477318359375 0.4782275390625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.47777294921875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.477318359375 0.47777294921875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0366 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.47777294921875 0.4782275390625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0367 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4782275390625 0.4800458984375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.47913671875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4782275390625 0.47913671875 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.47868212890625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4782275390625 0.47868212890625 := ⟨hl7.1,h8⟩
                    exact scalar_box_0368 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.47868212890625 0.47913671875 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0369 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.47913671875 0.4800458984375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.47959130859375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.47913671875 0.47959130859375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0370 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.47959130859375 0.4800458984375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0371 x hx hr8
      · have hr2 : scalarOccupation x∈Set.Icc 0.4800458984375 0.941 := ⟨(lt_of_not_ge h2).le,hr1.2⟩
        by_cases h3 : scalarOccupation x≤0.50459375
        · have hl3 : scalarOccupation x∈Set.Icc 0.4800458984375 0.50459375 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.488228515625
          · have hl4 : scalarOccupation x∈Set.Icc 0.4800458984375 0.488228515625 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.4827734375
            · have hl5 : scalarOccupation x∈Set.Icc 0.4800458984375 0.4827734375 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.48140966796875
              · have hl6 : scalarOccupation x∈Set.Icc 0.4800458984375 0.48140966796875 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.48050048828125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4800458984375 0.48050048828125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0372 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.48050048828125 0.48140966796875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.480955078125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.48050048828125 0.480955078125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0373 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.480955078125 0.48140966796875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0374 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.48140966796875 0.4827734375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4818642578125
                · have hl7 : scalarOccupation x∈Set.Icc 0.48140966796875 0.4818642578125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0375 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4818642578125 0.4827734375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.48231884765625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4818642578125 0.48231884765625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0376 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.48231884765625 0.4827734375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0377 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.4827734375 0.488228515625 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.484591796875
              · have hl6 : scalarOccupation x∈Set.Icc 0.4827734375 0.484591796875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.48322802734375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4827734375 0.48322802734375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0378 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.48322802734375 0.484591796875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4836826171875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.48322802734375 0.4836826171875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0379 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4836826171875 0.484591796875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0380 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.484591796875 0.488228515625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.48641015625
                · have hl7 : scalarOccupation x∈Set.Icc 0.484591796875 0.48641015625 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.4855009765625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.484591796875 0.4855009765625 := ⟨hl7.1,h8⟩
                    exact scalar_box_0381 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4855009765625 0.48641015625 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0382 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.48641015625 0.488228515625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4873193359375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.48641015625 0.4873193359375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0383 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4873193359375 0.488228515625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0384 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.488228515625 0.50459375 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.4945927734375
            · have hl5 : scalarOccupation x∈Set.Icc 0.488228515625 0.4945927734375 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4909560546875
              · have hl6 : scalarOccupation x∈Set.Icc 0.488228515625 0.4909560546875 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4891376953125
                · have hl7 : scalarOccupation x∈Set.Icc 0.488228515625 0.4891376953125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0385 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4891376953125 0.4909560546875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.490046875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4891376953125 0.490046875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0386 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.490046875 0.4909560546875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0387 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4909560546875 0.4945927734375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4927744140625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4909560546875 0.4927744140625 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.491865234375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4909560546875 0.491865234375 := ⟨hl7.1,h8⟩
                    exact scalar_box_0388 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.491865234375 0.4927744140625 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0389 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.4927744140625 0.4945927734375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.49368359375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4927744140625 0.49368359375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0390 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.49368359375 0.4945927734375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0391 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.4945927734375 0.50459375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.4973203125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4945927734375 0.4973203125 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.495501953125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4945927734375 0.495501953125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0392 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.495501953125 0.4973203125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.4964111328125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.495501953125 0.4964111328125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0393 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.4964111328125 0.4973203125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0394 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.4973203125 0.50459375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.50095703125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4973203125 0.50095703125 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.499138671875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.4973203125 0.499138671875 := ⟨hl7.1,h8⟩
                    exact scalar_box_0395 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.499138671875 0.50095703125 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0396 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.50095703125 0.50459375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.502775390625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.50095703125 0.502775390625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0397 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.502775390625 0.50459375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0398 x hx hr8
        · have hr3 : scalarOccupation x∈Set.Icc 0.50459375 0.941 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.5409609375
          · have hl4 : scalarOccupation x∈Set.Icc 0.50459375 0.5409609375 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.51550390625
            · have hl5 : scalarOccupation x∈Set.Icc 0.50459375 0.51550390625 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.510048828125
              · have hl6 : scalarOccupation x∈Set.Icc 0.50459375 0.510048828125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.506412109375
                · have hl7 : scalarOccupation x∈Set.Icc 0.50459375 0.506412109375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0399 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.506412109375 0.510048828125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.50823046875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.506412109375 0.50823046875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0400 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.50823046875 0.510048828125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0401 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.510048828125 0.51550390625 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.5118671875
                · have hl7 : scalarOccupation x∈Set.Icc 0.510048828125 0.5118671875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0402 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.5118671875 0.51550390625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.513685546875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.5118671875 0.513685546875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0403 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.513685546875 0.51550390625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0404 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.51550390625 0.5409609375 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.5264140625
              · have hl6 : scalarOccupation x∈Set.Icc 0.51550390625 0.5264140625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.519140625
                · have hl7 : scalarOccupation x∈Set.Icc 0.51550390625 0.519140625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0405 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.519140625 0.5264140625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.52277734375
                  · have hl8 : scalarOccupation x∈Set.Icc 0.519140625 0.52277734375 := ⟨hr7.1,h8⟩
                    exact scalar_box_0406 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.52277734375 0.5264140625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0407 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.5264140625 0.5409609375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.5336875
                · have hl7 : scalarOccupation x∈Set.Icc 0.5264140625 0.5336875 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.53005078125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.5264140625 0.53005078125 := ⟨hl7.1,h8⟩
                    exact scalar_box_0408 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.53005078125 0.5336875 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0409 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.5336875 0.5409609375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.53732421875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.5336875 0.53732421875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0410 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.53732421875 0.5409609375 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0411 x hx hr8
          · have hr4 : scalarOccupation x∈Set.Icc 0.5409609375 0.941 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.606421875
            · have hl5 : scalarOccupation x∈Set.Icc 0.5409609375 0.606421875 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.56278125
              · have hl6 : scalarOccupation x∈Set.Icc 0.5409609375 0.56278125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.548234375
                · have hl7 : scalarOccupation x∈Set.Icc 0.5409609375 0.548234375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0412 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.548234375 0.56278125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.5555078125
                  · have hl8 : scalarOccupation x∈Set.Icc 0.548234375 0.5555078125 := ⟨hr7.1,h8⟩
                    exact scalar_box_0413 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.5555078125 0.56278125 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0414 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.56278125 0.606421875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.577328125
                · have hl7 : scalarOccupation x∈Set.Icc 0.56278125 0.577328125 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.5700546875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.56278125 0.5700546875 := ⟨hl7.1,h8⟩
                    exact scalar_box_0415 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.5700546875 0.577328125 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0416 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.577328125 0.606421875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.591875
                  · have hl8 : scalarOccupation x∈Set.Icc 0.577328125 0.591875 := ⟨hr7.1,h8⟩
                    exact scalar_box_0417 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.591875 0.606421875 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0418 x hx hr8
            · have hr5 : scalarOccupation x∈Set.Icc 0.606421875 0.941 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.67915625
              · have hl6 : scalarOccupation x∈Set.Icc 0.606421875 0.67915625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.62096875
                · have hl7 : scalarOccupation x∈Set.Icc 0.606421875 0.62096875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0419 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.62096875 0.67915625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  by_cases h8 : scalarOccupation x≤0.6500625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.62096875 0.6500625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0420 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.6500625 0.67915625 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0421 x hx hr8
              · have hr6 : scalarOccupation x∈Set.Icc 0.67915625 0.941 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.7664375
                · have hl7 : scalarOccupation x∈Set.Icc 0.67915625 0.7664375 := ⟨hr6.1,h7⟩
                  by_cases h8 : scalarOccupation x≤0.70825
                  · have hl8 : scalarOccupation x∈Set.Icc 0.67915625 0.70825 := ⟨hl7.1,h8⟩
                    exact scalar_box_0422 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.70825 0.7664375 := ⟨(lt_of_not_ge h8).le,hl7.2⟩
                    exact scalar_box_0423 x hx hr8
                · have hr7 : scalarOccupation x∈Set.Icc 0.7664375 0.941 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  by_cases h8 : scalarOccupation x≤0.824625
                  · have hl8 : scalarOccupation x∈Set.Icc 0.7664375 0.824625 := ⟨hr7.1,h8⟩
                    exact scalar_box_0424 x hx hl8
                  · have hr8 : scalarOccupation x∈Set.Icc 0.824625 0.941 := ⟨(lt_of_not_ge h8).le,hr7.2⟩
                    exact scalar_box_0425 x hx hr8

theorem scalar_cover_b_high (x : ℝ) (hx : 0<x) (hq : scalarOccupation x∈Set.Icc 0.6 0.941) :
    scalarPartitionFunction x<0.99*x := by
  by_cases h0 : scalarOccupation x≤0.6639375
  · have hl0 : scalarOccupation x∈Set.Icc 0.6 0.6639375 := ⟨hq.1,h0⟩
    by_cases h1 : scalarOccupation x≤0.6213125
    · have hl1 : scalarOccupation x∈Set.Icc 0.6 0.6213125 := ⟨hl0.1,h1⟩
      by_cases h2 : scalarOccupation x≤0.61065625
      · have hl2 : scalarOccupation x∈Set.Icc 0.6 0.61065625 := ⟨hl1.1,h2⟩
        exact scalar_box_0426 x hx hl2
      · have hr2 : scalarOccupation x∈Set.Icc 0.61065625 0.6213125 := ⟨(lt_of_not_ge h2).le,hl1.2⟩
        exact scalar_box_0427 x hx hr2
    · have hr1 : scalarOccupation x∈Set.Icc 0.6213125 0.6639375 := ⟨(lt_of_not_ge h1).le,hl0.2⟩
      by_cases h2 : scalarOccupation x≤0.642625
      · have hl2 : scalarOccupation x∈Set.Icc 0.6213125 0.642625 := ⟨hr1.1,h2⟩
        exact scalar_box_0428 x hx hl2
      · have hr2 : scalarOccupation x∈Set.Icc 0.642625 0.6639375 := ⟨(lt_of_not_ge h2).le,hr1.2⟩
        exact scalar_box_0429 x hx hr2
  · have hr0 : scalarOccupation x∈Set.Icc 0.6639375 0.941 := ⟨(lt_of_not_ge h0).le,hq.2⟩
    by_cases h1 : scalarOccupation x≤0.727875
    · have hl1 : scalarOccupation x∈Set.Icc 0.6639375 0.727875 := ⟨hr0.1,h1⟩
      by_cases h2 : scalarOccupation x≤0.68525
      · have hl2 : scalarOccupation x∈Set.Icc 0.6639375 0.68525 := ⟨hl1.1,h2⟩
        exact scalar_box_0430 x hx hl2
      · have hr2 : scalarOccupation x∈Set.Icc 0.68525 0.727875 := ⟨(lt_of_not_ge h2).le,hl1.2⟩
        exact scalar_box_0431 x hx hr2
    · have hr1 : scalarOccupation x∈Set.Icc 0.727875 0.941 := ⟨(lt_of_not_ge h1).le,hr0.2⟩
      by_cases h2 : scalarOccupation x≤0.7705
      · have hl2 : scalarOccupation x∈Set.Icc 0.727875 0.7705 := ⟨hr1.1,h2⟩
        exact scalar_box_0432 x hx hl2
      · have hr2 : scalarOccupation x∈Set.Icc 0.7705 0.941 := ⟨(lt_of_not_ge h2).le,hr1.2⟩
        by_cases h3 : scalarOccupation x≤0.85575
        · have hl3 : scalarOccupation x∈Set.Icc 0.7705 0.85575 := ⟨hr2.1,h3⟩
          exact scalar_box_0433 x hx hl3
        · have hr3 : scalarOccupation x∈Set.Icc 0.85575 0.941 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          exact scalar_box_0434 x hx hr3

theorem scalar_cover_c_low (x : ℝ) (hx : 0<x) (hq : scalarOccupation x∈Set.Icc 0.01 0.406) :
    scalarPartitionFunction x<1*x := by
  by_cases h0 : scalarOccupation x≤0.3503125
  · have hl0 : scalarOccupation x∈Set.Icc 0.01 0.3503125 := ⟨hq.1,h0⟩
    by_cases h1 : scalarOccupation x≤0.245125
    · have hl1 : scalarOccupation x∈Set.Icc 0.01 0.245125 := ⟨hl0.1,h1⟩
      by_cases h2 : scalarOccupation x≤0.109
      · have hl2 : scalarOccupation x∈Set.Icc 0.01 0.109 := ⟨hl1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.03475
        · have hl3 : scalarOccupation x∈Set.Icc 0.01 0.03475 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.022375
          · have hl4 : scalarOccupation x∈Set.Icc 0.01 0.022375 := ⟨hl3.1,h4⟩
            exact scalar_box_0435 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.022375 0.03475 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            exact scalar_box_0436 x hx hr4
        · have hr3 : scalarOccupation x∈Set.Icc 0.03475 0.109 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.0595
          · have hl4 : scalarOccupation x∈Set.Icc 0.03475 0.0595 := ⟨hr3.1,h4⟩
            exact scalar_box_0437 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.0595 0.109 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.08425
            · have hl5 : scalarOccupation x∈Set.Icc 0.0595 0.08425 := ⟨hr4.1,h5⟩
              exact scalar_box_0438 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.08425 0.109 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0439 x hx hr5
      · have hr2 : scalarOccupation x∈Set.Icc 0.109 0.245125 := ⟨(lt_of_not_ge h2).le,hl1.2⟩
        by_cases h3 : scalarOccupation x≤0.18325
        · have hl3 : scalarOccupation x∈Set.Icc 0.109 0.18325 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.13375
          · have hl4 : scalarOccupation x∈Set.Icc 0.109 0.13375 := ⟨hl3.1,h4⟩
            exact scalar_box_0440 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.13375 0.18325 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.1585
            · have hl5 : scalarOccupation x∈Set.Icc 0.13375 0.1585 := ⟨hr4.1,h5⟩
              exact scalar_box_0441 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.1585 0.18325 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0442 x hx hr5
        · have hr3 : scalarOccupation x∈Set.Icc 0.18325 0.245125 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.208
          · have hl4 : scalarOccupation x∈Set.Icc 0.18325 0.208 := ⟨hr3.1,h4⟩
            exact scalar_box_0443 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.208 0.245125 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.23275
            · have hl5 : scalarOccupation x∈Set.Icc 0.208 0.23275 := ⟨hr4.1,h5⟩
              exact scalar_box_0444 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.23275 0.245125 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0445 x hx hr5
    · have hr1 : scalarOccupation x∈Set.Icc 0.245125 0.3503125 := ⟨(lt_of_not_ge h1).le,hl0.2⟩
      by_cases h2 : scalarOccupation x≤0.3131875
      · have hl2 : scalarOccupation x∈Set.Icc 0.245125 0.3131875 := ⟨hr1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.28225
        · have hl3 : scalarOccupation x∈Set.Icc 0.245125 0.28225 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.2575
          · have hl4 : scalarOccupation x∈Set.Icc 0.245125 0.2575 := ⟨hl3.1,h4⟩
            exact scalar_box_0446 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.2575 0.28225 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.269875
            · have hl5 : scalarOccupation x∈Set.Icc 0.2575 0.269875 := ⟨hr4.1,h5⟩
              exact scalar_box_0447 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.269875 0.28225 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0448 x hx hr5
        · have hr3 : scalarOccupation x∈Set.Icc 0.28225 0.3131875 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.294625
          · have hl4 : scalarOccupation x∈Set.Icc 0.28225 0.294625 := ⟨hr3.1,h4⟩
            exact scalar_box_0449 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.294625 0.3131875 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.307
            · have hl5 : scalarOccupation x∈Set.Icc 0.294625 0.307 := ⟨hr4.1,h5⟩
              exact scalar_box_0450 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.307 0.3131875 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0451 x hx hr5
      · have hr2 : scalarOccupation x∈Set.Icc 0.3131875 0.3503125 := ⟨(lt_of_not_ge h2).le,hr1.2⟩
        by_cases h3 : scalarOccupation x≤0.33175
        · have hl3 : scalarOccupation x∈Set.Icc 0.3131875 0.33175 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.319375
          · have hl4 : scalarOccupation x∈Set.Icc 0.3131875 0.319375 := ⟨hl3.1,h4⟩
            exact scalar_box_0452 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.319375 0.33175 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.3255625
            · have hl5 : scalarOccupation x∈Set.Icc 0.319375 0.3255625 := ⟨hr4.1,h5⟩
              exact scalar_box_0453 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.3255625 0.33175 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0454 x hx hr5
        · have hr3 : scalarOccupation x∈Set.Icc 0.33175 0.3503125 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.3379375
          · have hl4 : scalarOccupation x∈Set.Icc 0.33175 0.3379375 := ⟨hr3.1,h4⟩
            exact scalar_box_0455 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.3379375 0.3503125 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.344125
            · have hl5 : scalarOccupation x∈Set.Icc 0.3379375 0.344125 := ⟨hr4.1,h5⟩
              exact scalar_box_0456 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.344125 0.3503125 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0457 x hx hr5
  · have hr0 : scalarOccupation x∈Set.Icc 0.3503125 0.406 := ⟨(lt_of_not_ge h0).le,hq.2⟩
    by_cases h1 : scalarOccupation x≤0.3874375
    · have hl1 : scalarOccupation x∈Set.Icc 0.3503125 0.3874375 := ⟨hr0.1,h1⟩
      by_cases h2 : scalarOccupation x≤0.368875
      · have hl2 : scalarOccupation x∈Set.Icc 0.3503125 0.368875 := ⟨hl1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.35959375
        · have hl3 : scalarOccupation x∈Set.Icc 0.3503125 0.35959375 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.3565
          · have hl4 : scalarOccupation x∈Set.Icc 0.3503125 0.3565 := ⟨hl3.1,h4⟩
            exact scalar_box_0458 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.3565 0.35959375 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            exact scalar_box_0459 x hx hr4
        · have hr3 : scalarOccupation x∈Set.Icc 0.35959375 0.368875 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.3626875
          · have hl4 : scalarOccupation x∈Set.Icc 0.35959375 0.3626875 := ⟨hr3.1,h4⟩
            exact scalar_box_0460 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.3626875 0.368875 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.36578125
            · have hl5 : scalarOccupation x∈Set.Icc 0.3626875 0.36578125 := ⟨hr4.1,h5⟩
              exact scalar_box_0461 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.36578125 0.368875 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0462 x hx hr5
      · have hr2 : scalarOccupation x∈Set.Icc 0.368875 0.3874375 := ⟨(lt_of_not_ge h2).le,hl1.2⟩
        by_cases h3 : scalarOccupation x≤0.37815625
        · have hl3 : scalarOccupation x∈Set.Icc 0.368875 0.37815625 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.37196875
          · have hl4 : scalarOccupation x∈Set.Icc 0.368875 0.37196875 := ⟨hl3.1,h4⟩
            exact scalar_box_0463 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.37196875 0.37815625 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.3750625
            · have hl5 : scalarOccupation x∈Set.Icc 0.37196875 0.3750625 := ⟨hr4.1,h5⟩
              exact scalar_box_0464 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.3750625 0.37815625 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0465 x hx hr5
        · have hr3 : scalarOccupation x∈Set.Icc 0.37815625 0.3874375 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.38125
          · have hl4 : scalarOccupation x∈Set.Icc 0.37815625 0.38125 := ⟨hr3.1,h4⟩
            exact scalar_box_0466 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.38125 0.3874375 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.38434375
            · have hl5 : scalarOccupation x∈Set.Icc 0.38125 0.38434375 := ⟨hr4.1,h5⟩
              exact scalar_box_0467 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.38434375 0.3874375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0468 x hx hr5
    · have hr1 : scalarOccupation x∈Set.Icc 0.3874375 0.406 := ⟨(lt_of_not_ge h1).le,hr0.2⟩
      by_cases h2 : scalarOccupation x≤0.39671875
      · have hl2 : scalarOccupation x∈Set.Icc 0.3874375 0.39671875 := ⟨hr1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.392078125
        · have hl3 : scalarOccupation x∈Set.Icc 0.3874375 0.392078125 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.388984375
          · have hl4 : scalarOccupation x∈Set.Icc 0.3874375 0.388984375 := ⟨hl3.1,h4⟩
            exact scalar_box_0469 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.388984375 0.392078125 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.39053125
            · have hl5 : scalarOccupation x∈Set.Icc 0.388984375 0.39053125 := ⟨hr4.1,h5⟩
              exact scalar_box_0470 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.39053125 0.392078125 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0471 x hx hr5
        · have hr3 : scalarOccupation x∈Set.Icc 0.392078125 0.39671875 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.393625
          · have hl4 : scalarOccupation x∈Set.Icc 0.392078125 0.393625 := ⟨hr3.1,h4⟩
            exact scalar_box_0472 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.393625 0.39671875 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.395171875
            · have hl5 : scalarOccupation x∈Set.Icc 0.393625 0.395171875 := ⟨hr4.1,h5⟩
              exact scalar_box_0473 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.395171875 0.39671875 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0474 x hx hr5
      · have hr2 : scalarOccupation x∈Set.Icc 0.39671875 0.406 := ⟨(lt_of_not_ge h2).le,hr1.2⟩
        by_cases h3 : scalarOccupation x≤0.401359375
        · have hl3 : scalarOccupation x∈Set.Icc 0.39671875 0.401359375 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.398265625
          · have hl4 : scalarOccupation x∈Set.Icc 0.39671875 0.398265625 := ⟨hl3.1,h4⟩
            exact scalar_box_0475 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.398265625 0.401359375 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.3998125
            · have hl5 : scalarOccupation x∈Set.Icc 0.398265625 0.3998125 := ⟨hr4.1,h5⟩
              exact scalar_box_0476 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.3998125 0.401359375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0477 x hx hr5
        · have hr3 : scalarOccupation x∈Set.Icc 0.401359375 0.406 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.40290625
          · have hl4 : scalarOccupation x∈Set.Icc 0.401359375 0.40290625 := ⟨hr3.1,h4⟩
            exact scalar_box_0478 x hx hl4
          · have hr4 : scalarOccupation x∈Set.Icc 0.40290625 0.406 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.404453125
            · have hl5 : scalarOccupation x∈Set.Icc 0.40290625 0.404453125 := ⟨hr4.1,h5⟩
              exact scalar_box_0479 x hx hl5
            · have hr5 : scalarOccupation x∈Set.Icc 0.404453125 0.406 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              exact scalar_box_0480 x hx hr5

theorem scalar_cover_c_high (x : ℝ) (hx : 0<x) (hq : scalarOccupation x∈Set.Icc 0.4647 0.941) :
    scalarPartitionFunction x<1*x := by
  by_cases h0 : scalarOccupation x≤0.4699327880859375
  · have hl0 : scalarOccupation x∈Set.Icc 0.4647 0.4699327880859375 := ⟨hq.1,h0⟩
    by_cases h1 : scalarOccupation x≤0.46615355224609375
    · have hl1 : scalarOccupation x∈Set.Icc 0.4647 0.46615355224609375 := ⟨hl0.1,h1⟩
      by_cases h2 : scalarOccupation x≤0.465310491943359375
      · have hl2 : scalarOccupation x∈Set.Icc 0.4647 0.465310491943359375 := ⟨hl1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.464903497314453125
        · have hl3 : scalarOccupation x∈Set.Icc 0.4647 0.464903497314453125 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.4648017486572265625
          · have hl4 : scalarOccupation x∈Set.Icc 0.4647 0.4648017486572265625 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.4647436065673828125
            · have hl5 : scalarOccupation x∈Set.Icc 0.4647 0.4647436065673828125 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4647145355224609375
              · have hl6 : scalarOccupation x∈Set.Icc 0.4647 0.4647145355224609375 := ⟨hl5.1,h6⟩
                exact scalar_box_0481 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.4647145355224609375 0.4647436065673828125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.464729071044921875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4647145355224609375 0.464729071044921875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0482 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.464729071044921875 0.4647436065673828125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0483 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.4647436065673828125 0.4648017486572265625 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.4647726776123046875
              · have hl6 : scalarOccupation x∈Set.Icc 0.4647436065673828125 0.4647726776123046875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.46475814208984375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4647436065673828125 0.46475814208984375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0484 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46475814208984375 0.4647726776123046875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0485 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.4647726776123046875 0.4648017486572265625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.464787213134765625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4647726776123046875 0.464787213134765625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0486 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.464787213134765625 0.4648017486572265625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0487 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.4648017486572265625 0.464903497314453125 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.464845355224609375
            · have hl5 : scalarOccupation x∈Set.Icc 0.4648017486572265625 0.464845355224609375 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4648162841796875
              · have hl6 : scalarOccupation x∈Set.Icc 0.4648017486572265625 0.4648162841796875 := ⟨hl5.1,h6⟩
                exact scalar_box_0488 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.4648162841796875 0.464845355224609375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4648308197021484375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4648162841796875 0.4648308197021484375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0489 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4648308197021484375 0.464845355224609375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0490 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.464845355224609375 0.464903497314453125 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.46487442626953125
              · have hl6 : scalarOccupation x∈Set.Icc 0.464845355224609375 0.46487442626953125 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4648598907470703125
                · have hl7 : scalarOccupation x∈Set.Icc 0.464845355224609375 0.4648598907470703125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0491 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4648598907470703125 0.46487442626953125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0492 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.46487442626953125 0.464903497314453125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4648889617919921875
                · have hl7 : scalarOccupation x∈Set.Icc 0.46487442626953125 0.4648889617919921875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0493 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4648889617919921875 0.464903497314453125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0494 x hx hr7
        · have hr3 : scalarOccupation x∈Set.Icc 0.464903497314453125 0.465310491943359375 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.465077923583984375
          · have hl4 : scalarOccupation x∈Set.Icc 0.464903497314453125 0.465077923583984375 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.464961639404296875
            · have hl5 : scalarOccupation x∈Set.Icc 0.464903497314453125 0.464961639404296875 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4649180328369140625
              · have hl6 : scalarOccupation x∈Set.Icc 0.464903497314453125 0.4649180328369140625 := ⟨hl5.1,h6⟩
                exact scalar_box_0495 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.4649180328369140625 0.464961639404296875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.464932568359375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4649180328369140625 0.464932568359375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0496 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.464932568359375 0.464961639404296875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0497 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.464961639404296875 0.465077923583984375 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.465019781494140625
              · have hl6 : scalarOccupation x∈Set.Icc 0.464961639404296875 0.465019781494140625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.46499071044921875
                · have hl7 : scalarOccupation x∈Set.Icc 0.464961639404296875 0.46499071044921875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0498 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46499071044921875 0.465019781494140625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0499 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.465019781494140625 0.465077923583984375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4650488525390625
                · have hl7 : scalarOccupation x∈Set.Icc 0.465019781494140625 0.4650488525390625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0500 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4650488525390625 0.465077923583984375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0501 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.465077923583984375 0.465310491943359375 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.465194207763671875
            · have hl5 : scalarOccupation x∈Set.Icc 0.465077923583984375 0.465194207763671875 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.465136065673828125
              · have hl6 : scalarOccupation x∈Set.Icc 0.465077923583984375 0.465136065673828125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.46510699462890625
                · have hl7 : scalarOccupation x∈Set.Icc 0.465077923583984375 0.46510699462890625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0502 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46510699462890625 0.465136065673828125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0503 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.465136065673828125 0.465194207763671875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.46516513671875
                · have hl7 : scalarOccupation x∈Set.Icc 0.465136065673828125 0.46516513671875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0504 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46516513671875 0.465194207763671875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0505 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.465194207763671875 0.465310491943359375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.465252349853515625
              · have hl6 : scalarOccupation x∈Set.Icc 0.465194207763671875 0.465252349853515625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.46522327880859375
                · have hl7 : scalarOccupation x∈Set.Icc 0.465194207763671875 0.46522327880859375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0506 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46522327880859375 0.465252349853515625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0507 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.465252349853515625 0.465310491943359375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4652814208984375
                · have hl7 : scalarOccupation x∈Set.Icc 0.465252349853515625 0.4652814208984375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0508 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4652814208984375 0.465310491943359375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0509 x hx hr7
      · have hr2 : scalarOccupation x∈Set.Icc 0.465310491943359375 0.46615355224609375 := ⟨(lt_of_not_ge h2).le,hl1.2⟩
        by_cases h3 : scalarOccupation x≤0.465717486572265625
        · have hl3 : scalarOccupation x∈Set.Icc 0.465310491943359375 0.465717486572265625 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.4655139892578125
          · have hl4 : scalarOccupation x∈Set.Icc 0.465310491943359375 0.4655139892578125 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.465397705078125
            · have hl5 : scalarOccupation x∈Set.Icc 0.465310491943359375 0.465397705078125 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.46533956298828125
              · have hl6 : scalarOccupation x∈Set.Icc 0.465310491943359375 0.46533956298828125 := ⟨hl5.1,h6⟩
                exact scalar_box_0510 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.46533956298828125 0.465397705078125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.465368634033203125
                · have hl7 : scalarOccupation x∈Set.Icc 0.46533956298828125 0.465368634033203125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0511 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.465368634033203125 0.465397705078125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0512 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.465397705078125 0.4655139892578125 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.46545584716796875
              · have hl6 : scalarOccupation x∈Set.Icc 0.465397705078125 0.46545584716796875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.465426776123046875
                · have hl7 : scalarOccupation x∈Set.Icc 0.465397705078125 0.465426776123046875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0513 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.465426776123046875 0.46545584716796875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0514 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.46545584716796875 0.4655139892578125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.465484918212890625
                · have hl7 : scalarOccupation x∈Set.Icc 0.46545584716796875 0.465484918212890625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0515 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.465484918212890625 0.4655139892578125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0516 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.4655139892578125 0.465717486572265625 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.465601202392578125
            · have hl5 : scalarOccupation x∈Set.Icc 0.4655139892578125 0.465601202392578125 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.465543060302734375
              · have hl6 : scalarOccupation x∈Set.Icc 0.4655139892578125 0.465543060302734375 := ⟨hl5.1,h6⟩
                exact scalar_box_0517 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.465543060302734375 0.465601202392578125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.46557213134765625
                · have hl7 : scalarOccupation x∈Set.Icc 0.465543060302734375 0.46557213134765625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0518 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46557213134765625 0.465601202392578125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0519 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.465601202392578125 0.465717486572265625 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.465659344482421875
              · have hl6 : scalarOccupation x∈Set.Icc 0.465601202392578125 0.465659344482421875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4656302734375
                · have hl7 : scalarOccupation x∈Set.Icc 0.465601202392578125 0.4656302734375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0520 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4656302734375 0.465659344482421875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0521 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.465659344482421875 0.465717486572265625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.46568841552734375
                · have hl7 : scalarOccupation x∈Set.Icc 0.465659344482421875 0.46568841552734375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0522 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46568841552734375 0.465717486572265625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0523 x hx hr7
        · have hr3 : scalarOccupation x∈Set.Icc 0.465717486572265625 0.46615355224609375 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.46592098388671875
          · have hl4 : scalarOccupation x∈Set.Icc 0.465717486572265625 0.46592098388671875 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.46580469970703125
            · have hl5 : scalarOccupation x∈Set.Icc 0.465717486572265625 0.46580469970703125 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4657465576171875
              · have hl6 : scalarOccupation x∈Set.Icc 0.465717486572265625 0.4657465576171875 := ⟨hl5.1,h6⟩
                exact scalar_box_0524 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.4657465576171875 0.46580469970703125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.465775628662109375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4657465576171875 0.465775628662109375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0525 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.465775628662109375 0.46580469970703125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0526 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.46580469970703125 0.46592098388671875 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.465862841796875
              · have hl6 : scalarOccupation x∈Set.Icc 0.46580469970703125 0.465862841796875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.465833770751953125
                · have hl7 : scalarOccupation x∈Set.Icc 0.46580469970703125 0.465833770751953125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0527 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.465833770751953125 0.465862841796875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0528 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.465862841796875 0.46592098388671875 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.465891912841796875
                · have hl7 : scalarOccupation x∈Set.Icc 0.465862841796875 0.465891912841796875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0529 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.465891912841796875 0.46592098388671875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0530 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.46592098388671875 0.46615355224609375 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.46603726806640625
            · have hl5 : scalarOccupation x∈Set.Icc 0.46592098388671875 0.46603726806640625 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4659791259765625
              · have hl6 : scalarOccupation x∈Set.Icc 0.46592098388671875 0.4659791259765625 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.465950054931640625
                · have hl7 : scalarOccupation x∈Set.Icc 0.46592098388671875 0.465950054931640625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0531 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.465950054931640625 0.4659791259765625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0532 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.4659791259765625 0.46603726806640625 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.466008197021484375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4659791259765625 0.466008197021484375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0533 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.466008197021484375 0.46603726806640625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0534 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.46603726806640625 0.46615355224609375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.46609541015625
              · have hl6 : scalarOccupation x∈Set.Icc 0.46603726806640625 0.46609541015625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.466066339111328125
                · have hl7 : scalarOccupation x∈Set.Icc 0.46603726806640625 0.466066339111328125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0535 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.466066339111328125 0.46609541015625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0536 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.46609541015625 0.46615355224609375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.466124481201171875
                · have hl7 : scalarOccupation x∈Set.Icc 0.46609541015625 0.466124481201171875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0537 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.466124481201171875 0.46615355224609375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0538 x hx hr7
    · have hr1 : scalarOccupation x∈Set.Icc 0.46615355224609375 0.4699327880859375 := ⟨(lt_of_not_ge h1).le,hl0.2⟩
      by_cases h2 : scalarOccupation x≤0.46766524658203125
      · have hl2 : scalarOccupation x∈Set.Icc 0.46615355224609375 0.46766524658203125 := ⟨hr1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.466793115234375
        · have hl3 : scalarOccupation x∈Set.Icc 0.46615355224609375 0.466793115234375 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.46638612060546875
          · have hl4 : scalarOccupation x∈Set.Icc 0.46615355224609375 0.46638612060546875 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.466240765380859375
            · have hl5 : scalarOccupation x∈Set.Icc 0.46615355224609375 0.466240765380859375 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.466182623291015625
              · have hl6 : scalarOccupation x∈Set.Icc 0.46615355224609375 0.466182623291015625 := ⟨hl5.1,h6⟩
                exact scalar_box_0539 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.466182623291015625 0.466240765380859375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4662116943359375
                · have hl7 : scalarOccupation x∈Set.Icc 0.466182623291015625 0.4662116943359375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0540 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4662116943359375 0.466240765380859375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0541 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.466240765380859375 0.46638612060546875 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.466298907470703125
              · have hl6 : scalarOccupation x∈Set.Icc 0.466240765380859375 0.466298907470703125 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.46626983642578125
                · have hl7 : scalarOccupation x∈Set.Icc 0.466240765380859375 0.46626983642578125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0542 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46626983642578125 0.466298907470703125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0543 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.466298907470703125 0.46638612060546875 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.466327978515625
                · have hl7 : scalarOccupation x∈Set.Icc 0.466298907470703125 0.466327978515625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0544 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.466327978515625 0.46638612060546875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0545 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.46638612060546875 0.466793115234375 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.466560546875
            · have hl5 : scalarOccupation x∈Set.Icc 0.46638612060546875 0.466560546875 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4664442626953125
              · have hl6 : scalarOccupation x∈Set.Icc 0.46638612060546875 0.4664442626953125 := ⟨hl5.1,h6⟩
                exact scalar_box_0546 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.4664442626953125 0.466560546875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.46650240478515625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4664442626953125 0.46650240478515625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0547 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46650240478515625 0.466560546875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0548 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.466560546875 0.466793115234375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.4666768310546875
              · have hl6 : scalarOccupation x∈Set.Icc 0.466560546875 0.4666768310546875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.46661868896484375
                · have hl7 : scalarOccupation x∈Set.Icc 0.466560546875 0.46661868896484375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0549 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46661868896484375 0.4666768310546875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0550 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.4666768310546875 0.466793115234375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.46673497314453125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4666768310546875 0.46673497314453125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0551 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46673497314453125 0.466793115234375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0552 x hx hr7
        · have hr3 : scalarOccupation x∈Set.Icc 0.466793115234375 0.46766524658203125 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.46720010986328125
          · have hl4 : scalarOccupation x∈Set.Icc 0.466793115234375 0.46720010986328125 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.46696754150390625
            · have hl5 : scalarOccupation x∈Set.Icc 0.466793115234375 0.46696754150390625 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.46685125732421875
              · have hl6 : scalarOccupation x∈Set.Icc 0.466793115234375 0.46685125732421875 := ⟨hl5.1,h6⟩
                exact scalar_box_0553 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.46685125732421875 0.46696754150390625 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4669093994140625
                · have hl7 : scalarOccupation x∈Set.Icc 0.46685125732421875 0.4669093994140625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0554 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4669093994140625 0.46696754150390625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0555 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.46696754150390625 0.46720010986328125 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.46708382568359375
              · have hl6 : scalarOccupation x∈Set.Icc 0.46696754150390625 0.46708382568359375 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.46702568359375
                · have hl7 : scalarOccupation x∈Set.Icc 0.46696754150390625 0.46702568359375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0556 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46702568359375 0.46708382568359375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0557 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.46708382568359375 0.46720010986328125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4671419677734375
                · have hl7 : scalarOccupation x∈Set.Icc 0.46708382568359375 0.4671419677734375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0558 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4671419677734375 0.46720010986328125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0559 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.46720010986328125 0.46766524658203125 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.46743267822265625
            · have hl5 : scalarOccupation x∈Set.Icc 0.46720010986328125 0.46743267822265625 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.46731639404296875
              · have hl6 : scalarOccupation x∈Set.Icc 0.46720010986328125 0.46731639404296875 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.467258251953125
                · have hl7 : scalarOccupation x∈Set.Icc 0.46720010986328125 0.467258251953125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0560 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.467258251953125 0.46731639404296875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0561 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.46731639404296875 0.46743267822265625 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4673745361328125
                · have hl7 : scalarOccupation x∈Set.Icc 0.46731639404296875 0.4673745361328125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0562 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4673745361328125 0.46743267822265625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0563 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.46743267822265625 0.46766524658203125 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.46754896240234375
              · have hl6 : scalarOccupation x∈Set.Icc 0.46743267822265625 0.46754896240234375 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4674908203125
                · have hl7 : scalarOccupation x∈Set.Icc 0.46743267822265625 0.4674908203125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0564 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4674908203125 0.46754896240234375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0565 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.46754896240234375 0.46766524658203125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4676071044921875
                · have hl7 : scalarOccupation x∈Set.Icc 0.46754896240234375 0.4676071044921875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0566 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4676071044921875 0.46766524658203125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0567 x hx hr7
      · have hr2 : scalarOccupation x∈Set.Icc 0.46766524658203125 0.4699327880859375 := ⟨(lt_of_not_ge h2).le,hr1.2⟩
        by_cases h3 : scalarOccupation x≤0.46847923583984375
        · have hl3 : scalarOccupation x∈Set.Icc 0.46766524658203125 0.46847923583984375 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.4680722412109375
          · have hl4 : scalarOccupation x∈Set.Icc 0.46766524658203125 0.4680722412109375 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.4678396728515625
            · have hl5 : scalarOccupation x∈Set.Icc 0.46766524658203125 0.4678396728515625 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.467723388671875
              · have hl6 : scalarOccupation x∈Set.Icc 0.46766524658203125 0.467723388671875 := ⟨hl5.1,h6⟩
                exact scalar_box_0568 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.467723388671875 0.4678396728515625 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.46778153076171875
                · have hl7 : scalarOccupation x∈Set.Icc 0.467723388671875 0.46778153076171875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0569 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46778153076171875 0.4678396728515625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0570 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.4678396728515625 0.4680722412109375 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.46795595703125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4678396728515625 0.46795595703125 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.46789781494140625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4678396728515625 0.46789781494140625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0571 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46789781494140625 0.46795595703125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0572 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.46795595703125 0.4680722412109375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.46801409912109375
                · have hl7 : scalarOccupation x∈Set.Icc 0.46795595703125 0.46801409912109375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0573 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46801409912109375 0.4680722412109375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0574 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.4680722412109375 0.46847923583984375 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.46824666748046875
            · have hl5 : scalarOccupation x∈Set.Icc 0.4680722412109375 0.46824666748046875 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.46813038330078125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4680722412109375 0.46813038330078125 := ⟨hl5.1,h6⟩
                exact scalar_box_0575 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.46813038330078125 0.46824666748046875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.468188525390625
                · have hl7 : scalarOccupation x∈Set.Icc 0.46813038330078125 0.468188525390625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0576 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.468188525390625 0.46824666748046875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0577 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.46824666748046875 0.46847923583984375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.46836295166015625
              · have hl6 : scalarOccupation x∈Set.Icc 0.46824666748046875 0.46836295166015625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4683048095703125
                · have hl7 : scalarOccupation x∈Set.Icc 0.46824666748046875 0.4683048095703125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0578 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4683048095703125 0.46836295166015625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0579 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.46836295166015625 0.46847923583984375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.46842109375
                · have hl7 : scalarOccupation x∈Set.Icc 0.46836295166015625 0.46842109375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0580 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46842109375 0.46847923583984375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0581 x hx hr7
        · have hr3 : scalarOccupation x∈Set.Icc 0.46847923583984375 0.4699327880859375 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.4690025146484375
          · have hl4 : scalarOccupation x∈Set.Icc 0.46847923583984375 0.4690025146484375 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.468653662109375
            · have hl5 : scalarOccupation x∈Set.Icc 0.46847923583984375 0.468653662109375 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4685373779296875
              · have hl6 : scalarOccupation x∈Set.Icc 0.46847923583984375 0.4685373779296875 := ⟨hl5.1,h6⟩
                exact scalar_box_0582 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.4685373779296875 0.468653662109375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.46859552001953125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4685373779296875 0.46859552001953125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0583 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46859552001953125 0.468653662109375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0584 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.468653662109375 0.4690025146484375 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.4687699462890625
              · have hl6 : scalarOccupation x∈Set.Icc 0.468653662109375 0.4687699462890625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.46871180419921875
                · have hl7 : scalarOccupation x∈Set.Icc 0.468653662109375 0.46871180419921875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0585 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46871180419921875 0.4687699462890625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0586 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.4687699462890625 0.4690025146484375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.46888623046875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4687699462890625 0.46888623046875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0587 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46888623046875 0.4690025146484375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0588 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.4690025146484375 0.4699327880859375 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.4694676513671875
            · have hl5 : scalarOccupation x∈Set.Icc 0.4690025146484375 0.4694676513671875 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4692350830078125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4690025146484375 0.4692350830078125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.469118798828125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4690025146484375 0.469118798828125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0589 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.469118798828125 0.4692350830078125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0590 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.4692350830078125 0.4694676513671875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4693513671875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4692350830078125 0.4693513671875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0591 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4693513671875 0.4694676513671875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0592 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.4694676513671875 0.4699327880859375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.4697002197265625
              · have hl6 : scalarOccupation x∈Set.Icc 0.4694676513671875 0.4697002197265625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.469583935546875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4694676513671875 0.469583935546875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0593 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.469583935546875 0.4697002197265625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0594 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.4697002197265625 0.4699327880859375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.46981650390625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4697002197265625 0.46981650390625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0595 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.46981650390625 0.4699327880859375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0596 x hx hr7
  · have hr0 : scalarOccupation x∈Set.Icc 0.4699327880859375 0.941 := ⟨(lt_of_not_ge h0).le,hq.2⟩
    by_cases h1 : scalarOccupation x≤0.48191005859375
    · have hl1 : scalarOccupation x∈Set.Icc 0.4699327880859375 0.48191005859375 := ⟨hr0.1,h1⟩
      by_cases h2 : scalarOccupation x≤0.473770166015625
      · have hl2 : scalarOccupation x∈Set.Icc 0.4699327880859375 0.473770166015625 := ⟨hl1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.4715607666015625
        · have hl3 : scalarOccupation x∈Set.Icc 0.4699327880859375 0.4715607666015625 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.47074677734375
          · have hl4 : scalarOccupation x∈Set.Icc 0.4699327880859375 0.47074677734375 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.470281640625
            · have hl5 : scalarOccupation x∈Set.Icc 0.4699327880859375 0.470281640625 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.470049072265625
              · have hl6 : scalarOccupation x∈Set.Icc 0.4699327880859375 0.470049072265625 := ⟨hl5.1,h6⟩
                exact scalar_box_0597 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.470049072265625 0.470281640625 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4701653564453125
                · have hl7 : scalarOccupation x∈Set.Icc 0.470049072265625 0.4701653564453125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0598 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4701653564453125 0.470281640625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0599 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.470281640625 0.47074677734375 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.470514208984375
              · have hl6 : scalarOccupation x∈Set.Icc 0.470281640625 0.470514208984375 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4703979248046875
                · have hl7 : scalarOccupation x∈Set.Icc 0.470281640625 0.4703979248046875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0600 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4703979248046875 0.470514208984375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0601 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.470514208984375 0.47074677734375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4706304931640625
                · have hl7 : scalarOccupation x∈Set.Icc 0.470514208984375 0.4706304931640625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0602 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4706304931640625 0.47074677734375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0603 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.47074677734375 0.4715607666015625 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.4710956298828125
            · have hl5 : scalarOccupation x∈Set.Icc 0.47074677734375 0.4710956298828125 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4708630615234375
              · have hl6 : scalarOccupation x∈Set.Icc 0.47074677734375 0.4708630615234375 := ⟨hl5.1,h6⟩
                exact scalar_box_0604 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.4708630615234375 0.4710956298828125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.470979345703125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4708630615234375 0.470979345703125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0605 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.470979345703125 0.4710956298828125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0606 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.4710956298828125 0.4715607666015625 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.4713281982421875
              · have hl6 : scalarOccupation x∈Set.Icc 0.4710956298828125 0.4713281982421875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4712119140625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4710956298828125 0.4712119140625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0607 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4712119140625 0.4713281982421875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0608 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.4713281982421875 0.4715607666015625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.471444482421875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4713281982421875 0.471444482421875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0609 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.471444482421875 0.4715607666015625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0610 x hx hr7
        · have hr3 : scalarOccupation x∈Set.Icc 0.4715607666015625 0.473770166015625 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.472374755859375
          · have hl4 : scalarOccupation x∈Set.Icc 0.4715607666015625 0.472374755859375 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.471909619140625
            · have hl5 : scalarOccupation x∈Set.Icc 0.4715607666015625 0.471909619140625 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.47167705078125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4715607666015625 0.47167705078125 := ⟨hl5.1,h6⟩
                exact scalar_box_0611 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.47167705078125 0.471909619140625 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4717933349609375
                · have hl7 : scalarOccupation x∈Set.Icc 0.47167705078125 0.4717933349609375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0612 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4717933349609375 0.471909619140625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0613 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.471909619140625 0.472374755859375 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.4721421875
              · have hl6 : scalarOccupation x∈Set.Icc 0.471909619140625 0.4721421875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4720259033203125
                · have hl7 : scalarOccupation x∈Set.Icc 0.471909619140625 0.4720259033203125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0614 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4720259033203125 0.4721421875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0615 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.4721421875 0.472374755859375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4722584716796875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4721421875 0.4722584716796875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0616 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4722584716796875 0.472374755859375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0617 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.472374755859375 0.473770166015625 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.472839892578125
            · have hl5 : scalarOccupation x∈Set.Icc 0.472374755859375 0.472839892578125 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.47260732421875
              · have hl6 : scalarOccupation x∈Set.Icc 0.472374755859375 0.47260732421875 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4724910400390625
                · have hl7 : scalarOccupation x∈Set.Icc 0.472374755859375 0.4724910400390625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0618 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4724910400390625 0.47260732421875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0619 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.47260732421875 0.472839892578125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4727236083984375
                · have hl7 : scalarOccupation x∈Set.Icc 0.47260732421875 0.4727236083984375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0620 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4727236083984375 0.472839892578125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0621 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.472839892578125 0.473770166015625 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.473305029296875
              · have hl6 : scalarOccupation x∈Set.Icc 0.472839892578125 0.473305029296875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4730724609375
                · have hl7 : scalarOccupation x∈Set.Icc 0.472839892578125 0.4730724609375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0622 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4730724609375 0.473305029296875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0623 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.473305029296875 0.473770166015625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.47353759765625
                · have hl7 : scalarOccupation x∈Set.Icc 0.473305029296875 0.47353759765625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0624 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.47353759765625 0.473770166015625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0625 x hx hr7
      · have hr2 : scalarOccupation x∈Set.Icc 0.473770166015625 0.48191005859375 := ⟨(lt_of_not_ge h2).le,hl1.2⟩
        by_cases h3 : scalarOccupation x≤0.477026123046875
        · have hl3 : scalarOccupation x∈Set.Icc 0.473770166015625 0.477026123046875 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.47539814453125
          · have hl4 : scalarOccupation x∈Set.Icc 0.473770166015625 0.47539814453125 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.47446787109375
            · have hl5 : scalarOccupation x∈Set.Icc 0.473770166015625 0.47446787109375 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.474002734375
              · have hl6 : scalarOccupation x∈Set.Icc 0.473770166015625 0.474002734375 := ⟨hl5.1,h6⟩
                exact scalar_box_0626 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.474002734375 0.47446787109375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.474235302734375
                · have hl7 : scalarOccupation x∈Set.Icc 0.474002734375 0.474235302734375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0627 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.474235302734375 0.47446787109375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0628 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.47446787109375 0.47539814453125 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.4749330078125
              · have hl6 : scalarOccupation x∈Set.Icc 0.47446787109375 0.4749330078125 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.474700439453125
                · have hl7 : scalarOccupation x∈Set.Icc 0.47446787109375 0.474700439453125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0629 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.474700439453125 0.4749330078125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0630 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.4749330078125 0.47539814453125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.475165576171875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4749330078125 0.475165576171875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0631 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.475165576171875 0.47539814453125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0632 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.47539814453125 0.477026123046875 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.476095849609375
            · have hl5 : scalarOccupation x∈Set.Icc 0.47539814453125 0.476095849609375 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.475630712890625
              · have hl6 : scalarOccupation x∈Set.Icc 0.47539814453125 0.475630712890625 := ⟨hl5.1,h6⟩
                exact scalar_box_0633 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.475630712890625 0.476095849609375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.47586328125
                · have hl7 : scalarOccupation x∈Set.Icc 0.475630712890625 0.47586328125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0634 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.47586328125 0.476095849609375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0635 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.476095849609375 0.477026123046875 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.476560986328125
              · have hl6 : scalarOccupation x∈Set.Icc 0.476095849609375 0.476560986328125 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.47632841796875
                · have hl7 : scalarOccupation x∈Set.Icc 0.476095849609375 0.47632841796875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0636 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.47632841796875 0.476560986328125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0637 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.476560986328125 0.477026123046875 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4767935546875
                · have hl7 : scalarOccupation x∈Set.Icc 0.476560986328125 0.4767935546875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0638 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4767935546875 0.477026123046875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0639 x hx hr7
        · have hr3 : scalarOccupation x∈Set.Icc 0.477026123046875 0.48191005859375 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.4786541015625
          · have hl4 : scalarOccupation x∈Set.Icc 0.477026123046875 0.4786541015625 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.477723828125
            · have hl5 : scalarOccupation x∈Set.Icc 0.477026123046875 0.477723828125 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.47725869140625
              · have hl6 : scalarOccupation x∈Set.Icc 0.477026123046875 0.47725869140625 := ⟨hl5.1,h6⟩
                exact scalar_box_0640 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.47725869140625 0.477723828125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.477491259765625
                · have hl7 : scalarOccupation x∈Set.Icc 0.47725869140625 0.477491259765625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0641 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.477491259765625 0.477723828125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0642 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.477723828125 0.4786541015625 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.47818896484375
              · have hl6 : scalarOccupation x∈Set.Icc 0.477723828125 0.47818896484375 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.477956396484375
                · have hl7 : scalarOccupation x∈Set.Icc 0.477723828125 0.477956396484375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0643 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.477956396484375 0.47818896484375 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0644 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.47818896484375 0.4786541015625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.478421533203125
                · have hl7 : scalarOccupation x∈Set.Icc 0.47818896484375 0.478421533203125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0645 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.478421533203125 0.4786541015625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0646 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.4786541015625 0.48191005859375 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.48004951171875
            · have hl5 : scalarOccupation x∈Set.Icc 0.4786541015625 0.48004951171875 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.47911923828125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4786541015625 0.47911923828125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.478886669921875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4786541015625 0.478886669921875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0647 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.478886669921875 0.47911923828125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0648 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.47911923828125 0.48004951171875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.479584375
                · have hl7 : scalarOccupation x∈Set.Icc 0.47911923828125 0.479584375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0649 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.479584375 0.48004951171875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0650 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.48004951171875 0.48191005859375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.48097978515625
              · have hl6 : scalarOccupation x∈Set.Icc 0.48004951171875 0.48097978515625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4805146484375
                · have hl7 : scalarOccupation x∈Set.Icc 0.48004951171875 0.4805146484375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0651 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4805146484375 0.48097978515625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0652 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.48097978515625 0.48191005859375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.481444921875
                · have hl7 : scalarOccupation x∈Set.Icc 0.48097978515625 0.481444921875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0653 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.481444921875 0.48191005859375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0654 x hx hr7
    · have hr1 : scalarOccupation x∈Set.Icc 0.48191005859375 0.941 := ⟨(lt_of_not_ge h1).le,hr0.2⟩
      by_cases h2 : scalarOccupation x≤0.503771484375
      · have hl2 : scalarOccupation x∈Set.Icc 0.48191005859375 0.503771484375 := ⟨hr1.1,h2⟩
        by_cases h3 : scalarOccupation x≤0.488887109375
        · have hl3 : scalarOccupation x∈Set.Icc 0.48191005859375 0.488887109375 := ⟨hl2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.485166015625
          · have hl4 : scalarOccupation x∈Set.Icc 0.48191005859375 0.485166015625 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.48330546875
            · have hl5 : scalarOccupation x∈Set.Icc 0.48191005859375 0.48330546875 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4823751953125
              · have hl6 : scalarOccupation x∈Set.Icc 0.48191005859375 0.4823751953125 := ⟨hl5.1,h6⟩
                exact scalar_box_0655 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.4823751953125 0.48330546875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.48284033203125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4823751953125 0.48284033203125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0656 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.48284033203125 0.48330546875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0657 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.48330546875 0.485166015625 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.4842357421875
              · have hl6 : scalarOccupation x∈Set.Icc 0.48330546875 0.4842357421875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.48377060546875
                · have hl7 : scalarOccupation x∈Set.Icc 0.48330546875 0.48377060546875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0658 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.48377060546875 0.4842357421875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0659 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.4842357421875 0.485166015625 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.48470087890625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4842357421875 0.48470087890625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0660 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.48470087890625 0.485166015625 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0661 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.485166015625 0.488887109375 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.48656142578125
            · have hl5 : scalarOccupation x∈Set.Icc 0.485166015625 0.48656142578125 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.48563115234375
              · have hl6 : scalarOccupation x∈Set.Icc 0.485166015625 0.48563115234375 := ⟨hl5.1,h6⟩
                exact scalar_box_0662 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.48563115234375 0.48656142578125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.4860962890625
                · have hl7 : scalarOccupation x∈Set.Icc 0.48563115234375 0.4860962890625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0663 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4860962890625 0.48656142578125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0664 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.48656142578125 0.488887109375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.48749169921875
              · have hl6 : scalarOccupation x∈Set.Icc 0.48656142578125 0.48749169921875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.4870265625
                · have hl7 : scalarOccupation x∈Set.Icc 0.48656142578125 0.4870265625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0665 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4870265625 0.48749169921875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0666 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.48749169921875 0.488887109375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.4879568359375
                · have hl7 : scalarOccupation x∈Set.Icc 0.48749169921875 0.4879568359375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0667 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.4879568359375 0.488887109375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0668 x hx hr7
        · have hr3 : scalarOccupation x∈Set.Icc 0.488887109375 0.503771484375 := ⟨(lt_of_not_ge h3).le,hl2.2⟩
          by_cases h4 : scalarOccupation x≤0.4953990234375
          · have hl4 : scalarOccupation x∈Set.Icc 0.488887109375 0.4953990234375 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.4916779296875
            · have hl5 : scalarOccupation x∈Set.Icc 0.488887109375 0.4916779296875 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4898173828125
              · have hl6 : scalarOccupation x∈Set.Icc 0.488887109375 0.4898173828125 := ⟨hl5.1,h6⟩
                exact scalar_box_0669 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.4898173828125 0.4916779296875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.49074765625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4898173828125 0.49074765625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0670 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.49074765625 0.4916779296875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0671 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.4916779296875 0.4953990234375 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.4935384765625
              · have hl6 : scalarOccupation x∈Set.Icc 0.4916779296875 0.4935384765625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.492608203125
                · have hl7 : scalarOccupation x∈Set.Icc 0.4916779296875 0.492608203125 := ⟨hl6.1,h7⟩
                  exact scalar_box_0672 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.492608203125 0.4935384765625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0673 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.4935384765625 0.4953990234375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.49446875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4935384765625 0.49446875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0674 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.49446875 0.4953990234375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0675 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.4953990234375 0.503771484375 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.4991201171875
            · have hl5 : scalarOccupation x∈Set.Icc 0.4953990234375 0.4991201171875 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.4972595703125
              · have hl6 : scalarOccupation x∈Set.Icc 0.4953990234375 0.4972595703125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.496329296875
                · have hl7 : scalarOccupation x∈Set.Icc 0.4953990234375 0.496329296875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0676 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.496329296875 0.4972595703125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0677 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.4972595703125 0.4991201171875 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.49818984375
                · have hl7 : scalarOccupation x∈Set.Icc 0.4972595703125 0.49818984375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0678 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.49818984375 0.4991201171875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0679 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.4991201171875 0.503771484375 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.5009806640625
              · have hl6 : scalarOccupation x∈Set.Icc 0.4991201171875 0.5009806640625 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.500050390625
                · have hl7 : scalarOccupation x∈Set.Icc 0.4991201171875 0.500050390625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0680 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.500050390625 0.5009806640625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0681 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.5009806640625 0.503771484375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.5019109375
                · have hl7 : scalarOccupation x∈Set.Icc 0.5009806640625 0.5019109375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0682 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.5019109375 0.503771484375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0683 x hx hr7
      · have hr2 : scalarOccupation x∈Set.Icc 0.503771484375 0.941 := ⟨(lt_of_not_ge h2).le,hr1.2⟩
        by_cases h3 : scalarOccupation x≤0.54284296875
        · have hl3 : scalarOccupation x∈Set.Icc 0.503771484375 0.54284296875 := ⟨hr2.1,h3⟩
          by_cases h4 : scalarOccupation x≤0.5167953125
          · have hl4 : scalarOccupation x∈Set.Icc 0.503771484375 0.5167953125 := ⟨hl3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.509353125
            · have hl5 : scalarOccupation x∈Set.Icc 0.503771484375 0.509353125 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.50563203125
              · have hl6 : scalarOccupation x∈Set.Icc 0.503771484375 0.50563203125 := ⟨hl5.1,h6⟩
                exact scalar_box_0684 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.50563203125 0.509353125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.507492578125
                · have hl7 : scalarOccupation x∈Set.Icc 0.50563203125 0.507492578125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0685 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.507492578125 0.509353125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0686 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.509353125 0.5167953125 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.51307421875
              · have hl6 : scalarOccupation x∈Set.Icc 0.509353125 0.51307421875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.511213671875
                · have hl7 : scalarOccupation x∈Set.Icc 0.509353125 0.511213671875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0687 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.511213671875 0.51307421875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0688 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.51307421875 0.5167953125 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.514934765625
                · have hl7 : scalarOccupation x∈Set.Icc 0.51307421875 0.514934765625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0689 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.514934765625 0.5167953125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0690 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.5167953125 0.54284296875 := ⟨(lt_of_not_ge h4).le,hl3.2⟩
            by_cases h5 : scalarOccupation x≤0.52795859375
            · have hl5 : scalarOccupation x∈Set.Icc 0.5167953125 0.52795859375 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.52051640625
              · have hl6 : scalarOccupation x∈Set.Icc 0.5167953125 0.52051640625 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.518655859375
                · have hl7 : scalarOccupation x∈Set.Icc 0.5167953125 0.518655859375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0691 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.518655859375 0.52051640625 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0692 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.52051640625 0.52795859375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.5242375
                · have hl7 : scalarOccupation x∈Set.Icc 0.52051640625 0.5242375 := ⟨hr6.1,h7⟩
                  exact scalar_box_0693 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.5242375 0.52795859375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0694 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.52795859375 0.54284296875 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.53540078125
              · have hl6 : scalarOccupation x∈Set.Icc 0.52795859375 0.53540078125 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.5316796875
                · have hl7 : scalarOccupation x∈Set.Icc 0.52795859375 0.5316796875 := ⟨hl6.1,h7⟩
                  exact scalar_box_0695 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.5316796875 0.53540078125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0696 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.53540078125 0.54284296875 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.539121875
                · have hl7 : scalarOccupation x∈Set.Icc 0.53540078125 0.539121875 := ⟨hr6.1,h7⟩
                  exact scalar_box_0697 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.539121875 0.54284296875 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0698 x hx hr7
        · have hr3 : scalarOccupation x∈Set.Icc 0.54284296875 0.941 := ⟨(lt_of_not_ge h3).le,hr2.2⟩
          by_cases h4 : scalarOccupation x≤0.598659375
          · have hl4 : scalarOccupation x∈Set.Icc 0.54284296875 0.598659375 := ⟨hr3.1,h4⟩
            by_cases h5 : scalarOccupation x≤0.5614484375
            · have hl5 : scalarOccupation x∈Set.Icc 0.54284296875 0.5614484375 := ⟨hl4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.5465640625
              · have hl6 : scalarOccupation x∈Set.Icc 0.54284296875 0.5465640625 := ⟨hl5.1,h6⟩
                exact scalar_box_0699 x hx hl6
              · have hr6 : scalarOccupation x∈Set.Icc 0.5465640625 0.5614484375 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.55400625
                · have hl7 : scalarOccupation x∈Set.Icc 0.5465640625 0.55400625 := ⟨hr6.1,h7⟩
                  exact scalar_box_0700 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.55400625 0.5614484375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0701 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.5614484375 0.598659375 := ⟨(lt_of_not_ge h5).le,hl4.2⟩
              by_cases h6 : scalarOccupation x≤0.5763328125
              · have hl6 : scalarOccupation x∈Set.Icc 0.5614484375 0.5763328125 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.568890625
                · have hl7 : scalarOccupation x∈Set.Icc 0.5614484375 0.568890625 := ⟨hl6.1,h7⟩
                  exact scalar_box_0702 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.568890625 0.5763328125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0703 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.5763328125 0.598659375 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.583775
                · have hl7 : scalarOccupation x∈Set.Icc 0.5763328125 0.583775 := ⟨hr6.1,h7⟩
                  exact scalar_box_0704 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.583775 0.598659375 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0705 x hx hr7
          · have hr4 : scalarOccupation x∈Set.Icc 0.598659375 0.941 := ⟨(lt_of_not_ge h4).le,hr3.2⟩
            by_cases h5 : scalarOccupation x≤0.67308125
            · have hl5 : scalarOccupation x∈Set.Icc 0.598659375 0.67308125 := ⟨hr4.1,h5⟩
              by_cases h6 : scalarOccupation x≤0.628428125
              · have hl6 : scalarOccupation x∈Set.Icc 0.598659375 0.628428125 := ⟨hl5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.61354375
                · have hl7 : scalarOccupation x∈Set.Icc 0.598659375 0.61354375 := ⟨hl6.1,h7⟩
                  exact scalar_box_0706 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.61354375 0.628428125 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0707 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.628428125 0.67308125 := ⟨(lt_of_not_ge h6).le,hl5.2⟩
                by_cases h7 : scalarOccupation x≤0.6433125
                · have hl7 : scalarOccupation x∈Set.Icc 0.628428125 0.6433125 := ⟨hr6.1,h7⟩
                  exact scalar_box_0708 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.6433125 0.67308125 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0709 x hx hr7
            · have hr5 : scalarOccupation x∈Set.Icc 0.67308125 0.941 := ⟨(lt_of_not_ge h5).le,hr4.2⟩
              by_cases h6 : scalarOccupation x≤0.7623875
              · have hl6 : scalarOccupation x∈Set.Icc 0.67308125 0.7623875 := ⟨hr5.1,h6⟩
                by_cases h7 : scalarOccupation x≤0.70285
                · have hl7 : scalarOccupation x∈Set.Icc 0.67308125 0.70285 := ⟨hl6.1,h7⟩
                  exact scalar_box_0710 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.70285 0.7623875 := ⟨(lt_of_not_ge h7).le,hl6.2⟩
                  exact scalar_box_0711 x hx hr7
              · have hr6 : scalarOccupation x∈Set.Icc 0.7623875 0.941 := ⟨(lt_of_not_ge h6).le,hr5.2⟩
                by_cases h7 : scalarOccupation x≤0.821925
                · have hl7 : scalarOccupation x∈Set.Icc 0.7623875 0.821925 := ⟨hr6.1,h7⟩
                  exact scalar_box_0712 x hx hl7
                · have hr7 : scalarOccupation x∈Set.Icc 0.821925 0.941 := ⟨(lt_of_not_ge h7).le,hr6.2⟩
                  exact scalar_box_0713 x hx hr7

end HardCoreActivityThreshold
