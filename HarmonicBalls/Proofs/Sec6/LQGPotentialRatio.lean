import HarmonicBalls.Proofs.Sec6.GreenPotentialBound
import HarmonicBalls.Steps.Sec3.Basic
import HarmonicBalls.Proposed.LQG

/-!
# Positivity of LQG Green-potential ratios

On a single almost-sure event, the Green-potential extrema ratio is positive for every
smooth bounded domain inside a ball and every nonempty compact subset of the domain.
This supplies the positivity part of the fine-support argument in E19, Section 1.3(A).
-/


namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped NNReal

universe u

/-- Proposition 2.5, full support, non-atomicity and volume growth imply positivity
of the Green-potential ratio simultaneously for all admissible domains and compacts. -/
theorem ae_lqg_greenPotential_extrema_ratio_pos
    (hholder : GreenPotentialHolderStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hnonatom : LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ∀ᵐ ω ∂P, ∀ O : Set ℂ, IsSmoothBoundedOpen O → ∀ R : ℝ, 0 < R →
      O ⊆ ball (0 : ℂ) R → ∀ K : Set ℂ, IsCompact K → K.Nonempty → K ⊆ O →
      0 < ((⨅ z : K, ENNReal.ofReal (greenPotential O (μ ω) z)) /
        (⨆ z : O, ENNReal.ofReal (greenPotential O (μ ω) z))).toReal := by
  obtain ⟨βminus, βplus, hV⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hgrowth hγ hγ2 hα hGFF hμ
  filter_upwards [hV, hholder γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    hnonatom hGFF hγ hγ2 hα μ hμ] with ω hV hhold hsupport hatom
  let : IsLocallyFiniteMeasure (μ ω) := hV.1
  intro O hO R hR hsub K hK hKne hKO
  have hopen : IsOpen O := by
    obtain ⟨_, ρ, hρ, rfl, _⟩ := hO
    exact isOpen_lt hρ.continuous continuous_const
  obtain ⟨_, C, r, hr, hcont⟩ := hhold O hO (fun _ => 1) (memLp_top_const (1 : ℝ))
  have hcont' : ContinuousOn (greenPotential O (μ ω)) K := by
    apply (greenPotential_continuousOn_of_holder (μ ω) ?_).mono
      (hKO.trans subset_closure)
    refine ⟨C, r, hr, ?_⟩
    simpa only [mul_one] using hcont
  exact greenPotential_extrema_ratio_pos_of_volumeGrowth hR hopen hsub (hV.2 R hR)
    hK hKne hKO hcont' (fun x _ => hatom x)
    (fun x _ r hr => hsupport (ball x r) isOpen_ball ⟨x, mem_ball_self hr⟩)

end HarmonicBalls.Section6
