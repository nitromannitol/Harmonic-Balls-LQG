import HarmonicBalls.Steps.Sec2.VolumeGrowth
import HarmonicBalls.Proofs.Sec6.FineSupportDisc
import HarmonicBalls.Proofs.Sec6.DiscPotentialTranslation

/-! # Positivity of disc potential ratios from volume growth -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped NNReal

universe u

/-- The fine-support disc ratio is positive simultaneously at all centres and
scales, using disc Green-potential regularity supplied by volume growth. -/
theorem ae_fineSupportDisc_ratio_pos_of_volumeGrowth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ sample ∂P, ∀ c : ℂ, ∀ r : ℝ, 0 < r →
      0 < greenPotentialExtremaRatio (ball c r) (sphere c (r / 4)) (μ sample) := by
  obtain ⟨βm, βp, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα hGFF hμ
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth
  filter_upwards [hV, hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with sample hV hsupport
  let : IsLocallyFiniteMeasure (μ sample) := hV.1
  intro c r hr
  obtain ⟨_, hk, hkne, hko, R, hR, hsub⟩ := fineSupportDisc_geometry c hr
  obtain ⟨hc, _⟩ := restricted_greenPotential_center_regular hV.1 hr
    (hV.2 R hR) hsub (Set.Subset.rfl : ball c r ⊆ ball c r)
  have hcont : ContinuousOn (greenPotential (ball c r) (μ sample)) (sphere c (r / 4)) := by
    have heq : (fun x => ∫ y in ball c r, greenFunction (ball c r) x y ∂(μ sample)) =
        greenPotential (ball c r) (μ sample) := by
      funext x
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy => greenFunction_of_notMem_right hy x)
    rw [heq] at hc
    exact hc.mono (hko.trans ball_subset_closedBall)
  exact greenPotential_extrema_ratio_pos_of_volumeGrowth hR isOpen_ball hsub (hV.2 R hR)
    hk hkne hko hcont (fun x hx => (hV.2 R hR).measure_singleton (hsub hx))
    (fun x _ s hs => hsupport (ball x s) isOpen_ball ⟨x, mem_ball_self hs⟩)

end HarmonicBalls.Section6
