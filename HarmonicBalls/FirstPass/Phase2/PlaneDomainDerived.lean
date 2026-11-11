import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.LPStage.PlaneDomainConvexCompact

/-! # The plane-domain input of result 11.9 is derived (Phase 2, item B, module M0)

`PlaneDomainMinusConvexCompactPreconnectedFrozen` (`FirstPass/Frozen/S11d.lean:26`) is derived from the general plane
topology lemma `LatticeProb.Topology.isPreconnected_diff_of_convex_compact` (`LPStage/PlaneDomainConvexCompact.lean`):
for open connected `V ⊆ ℂ` and compact convex `K ⊆ V`, the set `V \ K` is preconnected. No hypothesis is added. The
frozen Prop itself is not edited. -/

namespace HarmonicBalls

/-- Derived theorem for the frozen Prop `PlaneDomainMinusConvexCompactPreconnectedFrozen` (result 11.9 input). -/
theorem planeDomainMinusConvexCompactPreconnected_derived :
    PlaneDomainMinusConvexCompactPreconnectedFrozen := by
  intro V K hVo hVc hKc hKcv hKV
  exact LatticeProb.Topology.isPreconnected_diff_of_convex_compact hVo hVc hKc hKcv hKV

end HarmonicBalls
