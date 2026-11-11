import HarmonicBalls.Proofs.Sec5.ExhaustionClusterCompatibility
import HarmonicBalls.Proofs.Sec5.GreenRegularLQGCompatibility

/-! # Conditional exhaustion export for strong compatibility

The comparison uses the potential-theoretic infrastructure of Leonardo Bonanno.
The availability of a regular exhaustion remains an explicit hypothesis.
-/

namespace HarmonicBalls

open Filter MeasureTheory Set
open scoped Topology

universe u

/-- I2 and polewise regular exhaustions imply the exact frozen compatibility
statement. The exhaustion is chosen separately for each deterministic domain and pole. -/
theorem clusterStrongCompatibility_of_regular_exhaustions
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hexhaust : ∀ (U : Set ℂ), IsOpen U → Bornology.IsBounded U →
      ∀ z ∈ U, ∃ V : ℕ → Set ℂ,
        (∀ n, IsOpen (V n)) ∧ Monotone V ∧ (⋃ n, V n) = U ∧
        (∀ n, closure (V n) ⊆ U) ∧ (∀ n, z ∈ V n) ∧
        (∀ n y, y ∈ closure (V n) → y ∉ V n →
          Tendsto (greenFunction (V n) z) (𝓝[V n] y) (𝓝 0))) :
    ClusterStrongCompatibilityStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ Λhat hΛ U hU hUb
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hV, hΛ] with ω hω hfamily
  intro t ht z hz hcl
  obtain ⟨V, hopen, hmono, hcover, hsub, hzV, hboundary⟩ := hexhaust U hU hUb z hz
  exact regularizedFamily_closure_eq_clusterOn_of_regular_exhaustion
    hω.1 hω.2 hU hUb V hopen hmono hcover hsub hzV ht hboundary (hfamily z) hcl

end HarmonicBalls
