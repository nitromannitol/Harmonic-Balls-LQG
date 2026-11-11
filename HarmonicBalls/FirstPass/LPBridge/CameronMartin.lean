import HarmonicBalls.FirstPass.Frozen.S11aj
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.LPStage.CameronMartinDerived2

/-!
# Cameron-Martin frozen inputs from the LP stage (bridge, task fp-lpstage-cameron-martin-resume, worker z7)

Binder-free proofs of the two frozen Cameron-Martin Props of the Harmonic-balls draft, from the LP-stage theorems:

* `HarmonicBalls.LPBridge.cameronMartinGFFReweighting_of_lp` proves `HarmonicBalls.S11aj.CameronMartinGFFReweighting`
  (`HarmonicBalls/FirstPass/Frozen/S11aj.lean:33`) from `LatticeProb.Gauss.cameronMartinGFFReweighting_derived`;
* `HarmonicBalls.LPBridge.cameronMartinGFFMutualAbsCont_of_lp` proves `HarmonicBalls.CameronMartinGFFMutualAbsCont`
  (`HarmonicBalls/FirstPass/Frozen/S11d.lean:74`) from `LatticeProb.Gauss.cameronMartinGFFMutualAbsCont_derived`.

The two HB and LP copies of each Prop are definitionally equal (`HarmonicBalls.LPBridge.addFunPairing_eq`,
`distributionMeasurableSpace_eq`, both `rfl`), and the structures `IsWholePlaneGFF` are equivalent by
`HarmonicBalls.LPBridge.isWholePlaneGFF_iff` (`FirstPass/LPBridge/M1.lean`).
-/

namespace HarmonicBalls.LPBridge

open MeasureTheory

universe u

/-- The frozen reweighting Prop `HarmonicBalls.S11aj.CameronMartinGFFReweighting`, from the LP stage. -/
theorem cameronMartinGFFReweighting_of_lp : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u} := by
  intro Ω _ P _ hC hcirc hW f hf hc hAv
  obtain ⟨P', h1, h2, h3⟩ := LatticeProb.Gauss.cameronMartinGFFReweighting_derived.{u} Ω P hC hcirc
    ((isWholePlaneGFF_iff P hC hcirc).mp hW) f hf hc hAv
  exact ⟨P', h1, h2, (isWholePlaneGFF_iff P' _ _).mpr h3⟩

/-- The frozen mutual absolute continuity Prop `HarmonicBalls.CameronMartinGFFMutualAbsCont`, from the LP stage. -/
theorem cameronMartinGFFMutualAbsCont_of_lp : HarmonicBalls.CameronMartinGFFMutualAbsCont.{u} := by
  intro Ω _ P _ hC hcirc g hW hgC hgS hgc B hB
  exact LatticeProb.Gauss.cameronMartinGFFMutualAbsCont_derived.{u} Ω P hC hcirc g
    ((isWholePlaneGFF_iff P hC hcirc).mp hW) hgC hgS hgc B hB

end HarmonicBalls.LPBridge
