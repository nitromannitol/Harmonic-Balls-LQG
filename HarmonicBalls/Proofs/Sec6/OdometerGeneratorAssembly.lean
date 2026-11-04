import HarmonicBalls.Proofs.Sec6.LaplacianConvolution
import HarmonicBalls.Proofs.Sec6.OdometerApproximationAssembly

/-! # The odometer comparison from the planar Brownian generator identity -/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Set Filter MarkovProcess Metric Laplacian
open scoped ContDiff ENNReal NNReal Topology ZeroAtInfty

universe u

/-- Lemma 6.9 follows from volume growth and identification of the planar
Brownian generator on smooth compactly supported functions. The generator
identity remains an explicit, unproved hypothesis. -/
theorem odometerHarmonicMeasureBoundStmt_of_planar_generator
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hgen : ∀ g : ℂ → ℝ, ContDiff ℝ ∞ g → HasCompactSupport g →
      ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
        (∀ z, (f : C₀(ℂ, ℝ)) z = g z) ∧
        ∀ z, (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z =
          (1 / 2 : ℝ) * Δ g z) : OdometerHarmonicMeasureBoundStmt.{u} := by
  apply odometerHarmonicMeasureBoundStmt_of_local_subharmonic_approximation hI2
  intro U q hU hq hsub V hV hVc hVU ε hε
  obtain ⟨g, hgs, hgc, hgq, hgΔ⟩ :=
    exists_compactlySupported_smooth_subharmonic_approximation hU hVc hVU hq hsub hε
  obtain ⟨f, hf, hfgen⟩ := hgen g hgs hgc
  refine ⟨f, ?_, ?_⟩
  · intro y hy
    rw [hf y, abs_sub_comm]
    exact hgq y hy
  · intro y hy
    rw [hfgen y]
    exact mul_nonneg (by norm_num) (hgΔ y (subset_closure hy))

end HarmonicBalls.Section6
