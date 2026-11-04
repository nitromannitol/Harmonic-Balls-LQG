import HarmonicBalls.Proofs.Sec6.OdometerPoleRemoval
import HarmonicBalls.Proofs.Sec6.GoodAnnulusDecayAssembly

/-! # The odometer comparison from compact-local subharmonic approximation -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology ZeroAtInfty

universe u

/-- Lemma 6.9 follows from volume growth and a compact-local approximation
principle for continuous subharmonic functions by functions with nonnegative
planar Brownian generator. The approximation principle remains a hypothesis. -/
theorem odometerHarmonicMeasureBoundStmt_of_local_subharmonic_approximation
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (happrox : ∀ (U : Set ℂ) (q : ℂ → ℝ), IsOpen U → ContinuousOn q U →
      IsSubharmonicOn U q → ∀ (V : Set ℂ), IsOpen V → IsCompact (closure V) →
      closure V ⊆ U → ∀ ε : ℝ, 0 < ε →
      ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ y ∈ closure V, |q y - (f : C₀(ℂ, ℝ)) y| ≤ ε) ∧
        ∀ y ∈ V, 0 ≤ (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) y) :
    OdometerHarmonicMeasureBoundStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hae] with ω hω
  intro z hz t ht A hA hAin hzA x hx Λx hΛx hfinite
  subst Λx
  have hcontsub := odometer_continuousOn_and_subharmonic hω.1 zero_lt_one
    (hω.2 1 zero_lt_one) hz ht
  apply odometer_le_harmonicMeasure_of_compact_local_approximation_and_finite_boundary
    hω.1 (hω.2 1 zero_lt_one) hz ht hA hAin hzA hx hfinite
  intro V hVo hVc hVY ε hε
  apply happrox (ball (0 : ℂ) 1 \ {z}) (odometer (μ ω) 1 z t)
    (isOpen_ball.sdiff isClosed_singleton) hcontsub.1 hcontsub.2 V hVo hVc _ ε hε
  intro y hy
  have hyA := ((connectedComponentIn_subset _ _).trans inter_subset_left) (hVY hy)
  exact ⟨hAin hyA, fun hyz => hzA (by simpa only [mem_singleton_iff] using hyz ▸ hyA)⟩

end HarmonicBalls.Section6
