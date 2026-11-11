import HarmonicBalls.FirstPass.Phase2.GFFExistsConstructed
import HarmonicBalls.LPStage.GFFCovPSD7

/-!
# Row 29 with the covariance positivity input proved (MQ-lh-25)

`wholePlaneGFFExistsFrozen_derived` takes the two named inputs `WholePlaneCovPSDStmt` (B2) and
`WholePlaneCovSymmStmt`. Both are now proved in `LPStage`: `LatticeProb.Gauss.wholePlaneCovPSD_proved`
(`LPStage/GFFCovPSD1.lean` to `GFFCovPSD7.lean`, route MQ-lh-25) and `LatticeProb.Gauss.wholePlaneCovSymm_proved`
(`LPStage/GFFCovSymm.lean`, theorem after `end GFFCovSymm`). No named input remains for row 29 in this file.
-/

namespace HarmonicBalls

universe u

/-- Row 29 in every universe, with `WholePlaneCovPSDStmt` proved (`wholePlaneCovPSD_proved`) and the symmetry input
discharged by `LatticeProb.Gauss.wholePlaneCovSymm_proved`. -/
theorem wholePlaneGFFExistsFrozen_derived' : WholePlaneGFFExistsFrozen.{u} :=
  wholePlaneGFFExistsFrozen_derived LatticeProb.Gauss.wholePlaneCovPSD_proved
    LatticeProb.Gauss.wholePlaneCovSymm_proved

end HarmonicBalls
