import HarmonicBalls.Proofs.Sec6.PlanarGaussianDecomposition
import HarmonicBalls.Proofs.Sec6.OdometerGeneratorAssembly
import HarmonicBalls.Proofs.Brownian.PlanarHeatFeller

/-! # Generator of planar Brownian motion on smooth compactly supported functions -/

namespace HarmonicBalls.Section6

open Filter MeasureTheory ProbabilityTheory Set Metric Laplacian MarkovProcess InnerProductSpace
open scoped ContDiff NNReal Topology ZeroAtInfty

/-- On smooth compactly supported functions the planar Brownian generator is
one half of the Laplacian. -/
theorem exists_planarBrownian_generator_eq_half_laplacian
    (g : ℂ → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
      (∀ z, (f : C₀(ℂ, ℝ)) z = g z) ∧
      ∀ z, (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z =
        (1 / 2 : ℝ) * Δ g z := by
  let f : C₀(ℂ, ℝ) := ⟨⟨g, hg.continuous⟩, hgc.is_zero_at_infty⟩
  let d : C₀(ℂ, ℝ) := ⟨⟨Δ g, continuous_laplacian_of_contDiff (hg.of_le (by norm_num))⟩,
    (hasCompactSupport_laplacian hgc).is_zero_at_infty⟩
  have hlim : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ •
      (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup t f - f))
      (𝓝[>] 0) (𝓝 ((2 : ℝ)⁻¹ • d)) := by
    rw [ZeroAtInftyContinuousMap.tendsto_iff_tendstoUniformly]
    have h := tendstoUniformly_planarGaussian_quotient hg hgc
    convert h using 1
    · funext t z
      simp only [ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, smul_eq_mul,
        ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply]
      rw [SubMarkovKernelSemigroup.IsFellerKernelSemigroup.c0Semigroup_apply_apply,
        kernelIntegral, planarHeatSemigroup_apply]
      rfl
    · funext z
      simp [d, div_eq_inv_mul]
  have hmem := isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.mem_generatorDomain_of_tendsto hlim
  refine ⟨⟨f, hmem⟩, fun _ => rfl, ?_⟩
  have hgen := isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator_mk_eq hlim
  intro z
  rw [hgen]
  simp [d, div_eq_inv_mul]

/-- Smooth harmonic functions have vanishing planar Brownian generator at
points where they are harmonic. -/
theorem exists_planarBrownian_generator_eq_zero_of_harmonic
    (g : ℂ → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ f : isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generatorDomain,
      (∀ z, (f : C₀(ℂ, ℝ)) z = g z) ∧
      ∀ z, HarmonicAt g z →
        (isFellerKernelSemigroup_planarHeatSemigroup.c0Semigroup.generator f) z = 0 := by
  obtain ⟨f, hf, hgen⟩ := exists_planarBrownian_generator_eq_half_laplacian g hg hgc
  refine ⟨f, hf, fun z hz => ?_⟩
  rw [hgen z, hz.2.eq_of_nhds]
  simp

universe u

/-- Lemma 6.9 follows from the all-scales LQG volume-growth statement. -/
theorem odometerHarmonicMeasureBoundStmt_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : OdometerHarmonicMeasureBoundStmt.{u} :=
  odometerHarmonicMeasureBoundStmt_of_planar_generator hI2
    exists_planarBrownian_generator_eq_half_laplacian

end HarmonicBalls.Section6
