import HarmonicBalls.Audit.Section5ExhaustionCompatibility
import HarmonicBalls.Proofs.Potential.GreenRegularDomainExhaustion

/-! # Strong compatibility from volume growth

The regular-exhaustion construction uses the potential-theoretic infrastructure
of Leonardo Bonanno.
-/

namespace HarmonicBalls

universe u

/-- All-scales volume growth implies the frozen strong compatibility statement. -/
theorem clusterStrongCompatibilityStmt_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : ClusterStrongCompatibilityStmt.{u} := by
  apply clusterStrongCompatibility_of_regular_exhaustions hI2
  intro U hU hUb z hz
  exact exists_greenRegular_exhaustion hU hUb hz

#print axioms clusterStrongCompatibilityStmt_of_volumeGrowth

end HarmonicBalls
