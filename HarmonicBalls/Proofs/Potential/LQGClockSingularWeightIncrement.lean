import HarmonicBalls.Proofs.Potential.BrownianSingularWeightEnvelope
import HarmonicBalls.Proofs.Potential.LQGClockArbitraryRadiusIncrement

/-! # Field increments with singular occupation weights

Singular Brownian occupation bounds supply the inputs to a field-increment estimate.
-/

open MeasureTheory Real Set ProbabilityTheory MarkovProcess
open scoped NNReal ENNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The field-increment estimate holds for all singularly dominated occupation weights. -/
theorem ae_brownian_singular_submeasure_field_increment_le
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x z : ℂ)
    {q q₂ β d : ℝ} (hq : 0 < q) (hqq : q < q₂) (hq₂ : q₂ < 1)
    (hβ : 0 < β) (hβ₂ : β < 2) (hd0 : 0 < d)
    (hd : d < β * (1 - q/q₂)) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ (g : ℂ → ℝ), Measurable g →
      (∀ y, ENNReal.ofReal |g y| ≤ (ENNReal.ofReal ‖y-z‖) ^ (-q)) →
      ∀ (μ : Measure ℂ), μ ≤ Measure.map (fun t => b t) ν →
      ∀ {R γ θ : ℝ}, 0 < R → γ ≤ θ → θ ≤ 2*γ →
      (∀ y, g y ≠ 0 → ‖y‖ ≤ R - 1/2) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
      (∫ ω, |∫ y, g y * ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) y-hcirc ω R 0)) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε y-hcirc ω R 0))) ∂μ| ∂P) ≤
      ((Real.exp (γ^2*Real.log 2)-1)*
        Real.exp (Real.log R * (2*γ^2-(2*γ-θ)^2/2))*
        (2^d * unitSingularPairAllRadiusEnvelope z q d b)+1)/2 *
        Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
      2*unitSingularOccupationEnvelope z q b *
        Real.exp (Real.log R * (γ^2/2-(θ-γ)^2/2))*
        Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [planarBrownianMotion_ae_unit_singular_weighted_submeasure_integrable
      x z hq (by linarith),
    planarBrownianMotion_ae_unit_singular_weighted_submeasure_le
      x z hq hqq hq₂ hβ hβ₂ hd0 hd] with b hfirst hpair
  intro g hg hgq μ hμ R γ θ hR hγθ hθ hgs ε hε hεhalf
  let ρ : Measure ℂ := Measure.map (fun t => b t) ν
  let : IsProbabilityMeasure ρ := inferInstance
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le ρ hμ
  obtain ⟨hgi, hA⟩ := hfirst g hg hgq μ hμ
  obtain ⟨_, hI⟩ := hpair g hg hgq μ hμ (2*ε) (by positivity)
  have hI' : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤
      (2^d * unitSingularPairAllRadiusEnvelope z q d b) * Real.exp (Real.log ε*d) := by
    have hhI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
        (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤
        unitSingularPairAllRadiusEnvelope z q d b * (2*ε)^d := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hI
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le,
      Real.rpow_def_of_pos hε] at hhI
    convert hhI using 1; ring
  exact field_increment_le_rate_of_radius hh hε hR μ hg hgi
    (fun y hy => by linarith [hgs y hy]) hγθ hθ hA hI'

end HarmonicBalls
