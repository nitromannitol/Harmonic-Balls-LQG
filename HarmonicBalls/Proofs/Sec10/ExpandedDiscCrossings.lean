import HarmonicBalls.Proofs.Sec10.CrossingScaling
import HarmonicBalls.Proofs.Sec10.SharpLocalizationMargins
import HarmonicBalls.Proofs.Sec10.JordanScaling
import HarmonicBalls.Proofs.Sec5.SupersolutionScaling
import HarmonicBalls.Proofs.Sec10.CompactCenterCrossings

/-!
# Crossing bounds from a larger disc

Scaling the disc of radius two to the unit disc removes the boundary margin
for clusters compactly contained in the original unit disc. The pole margin
remains, and the lower endpoint of the radius interval becomes `ε / 2`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped Pointwise

/-- The deterministic scaling and compatibility step for one choice of scale. -/
theorem crossings_of_larger_disc_normalization
    (μ ν : Measure ℂ) (a α ε : ℝ) (ha : 0 < a) (hε : 0 < ε) (hεsmall : ε < 1 / 16)
    (hunit : ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt (ε / 4)),
      ∃ ρ ∈ Icc (ε / 4) (Real.sqrt (ε / 4)),
        ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
          dist w 0 + (ρ + ρ / 50) < 1 → ρ + ρ / 50 < dist z w →
          (crossingComponents (cluster ν 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard ≤ ⌈1 / α⌉₊)
    (hscale : ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      cluster ν 1 z t = (2 : ℝ)⁻¹ • cluster μ 2 ((2 : ℝ) • z) (a * t))
    (hcompat : ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      closure (cluster μ 1 z t) ⊆ ball 0 1 → cluster μ 2 z t = cluster μ 1 z t) :
    ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc (ε / 2) (Real.sqrt ε), ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        closure (cluster μ 1 z t) ⊆ ball 0 1 → ρ + ρ / 50 < dist z w →
        (crossingComponents (cluster μ 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  have hhalf (x y : ℂ) : dist ((2 : ℝ)⁻¹ • x) ((2 : ℝ)⁻¹ • y) = dist x y / 2 := by
    rw [dist_smul₀]
    norm_num [Real.norm_eq_abs, div_eq_mul_inv, mul_comm]
  have hsqrt : Real.sqrt (ε / 4) = Real.sqrt ε / 2 := by
    rw [Real.sqrt_div hε.le]
    norm_num
  have hsqrtsmall : Real.sqrt ε < 1 / 4 := by
    have h := Real.sqrt_lt_sqrt hε.le hεsmall
    norm_num at h
    exact h
  intro w hw
  have hw' : (2 : ℝ)⁻¹ • w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt (ε / 4)) := by
    have hd : dist ((2 : ℝ)⁻¹ • w) 0 = dist w 0 / 2 := by simpa using hhalf w 0
    have hwd : dist w 0 < 1 := mem_ball.mp hw.1
    have hwa : 20 * Real.sqrt ε ≤ dist w 0 := by simpa [mem_ball, not_lt] using hw.2
    constructor
    · exact mem_ball.mpr (by linarith)
    · rw [mem_ball, not_lt, hsqrt, hd]
      linarith
  obtain ⟨r, hr, hbound⟩ := hunit _ hw'
  refine ⟨2 * r, ⟨by linarith [hr.1], by rw [hsqrt] at hr; linarith [hr.2]⟩, ?_⟩
  intro z hz t ht hcl hpole
  have hz' : (2 : ℝ)⁻¹ • z ∈ ball (0 : ℂ) 1 := by
    have hd : dist ((2 : ℝ)⁻¹ • z) 0 = dist z 0 / 2 := by simpa using hhalf z 0
    exact mem_ball.mpr (by rw [hd]; linarith [mem_ball.mp hz])
  have hd : dist ((2 : ℝ)⁻¹ • w) 0 = dist w 0 / 2 := by simpa using hhalf w 0
  have hdzw := hhalf z w
  have hboundary : dist ((2 : ℝ)⁻¹ • w) 0 + (r + r / 50) < 1 := by
    rw [hd, hsqrt] at *
    linarith [mem_ball.mp hw.1, hr.2]
  have hpole' : r + r / 50 < dist ((2 : ℝ)⁻¹ • z) ((2 : ℝ)⁻¹ • w) := by
    rw [hdzw]
    linarith
  have ht' : 0 < t / a := div_pos ht ha
  have hscale' := hscale ((2 : ℝ)⁻¹ • z) hz' (t / a) ht'
  have hzscale : (2 : ℝ) • ((2 : ℝ)⁻¹ • z) = z := by simp
  have htscale : a * (t / a) = t := by field_simp
  rw [hzscale, htscale] at hscale'
  have hcount := hbound ((2 : ℝ)⁻¹ • z) hz' (t / a) ht' hboundary hpole'
  have htrans := encard_ball_crossings_of_cluster_scale μ ν z w t (t / a) (2 * r) 2
    (by norm_num) hscale'
  have hcompat' := hcompat z hz t ht hcl
  rw [hcompat'] at htrans
  have hrscale : 2 * r / 2 = r := by ring
  rw [hrscale] at htrans
  exact htrans.trans_le hcount

universe u

/-- After enlargement to the disc of radius two, the crossing estimate holds
at all admissible unit-disc centers without a boundary margin. The affine
invariance and coordinate-change hypotheses are staged inputs. -/
theorem ae_crossings_without_boundary_margin_of_scaledField
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc (ε / 2) (Real.sqrt ε), ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 → ρ + ρ / 50 < dist z w →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ := ae_eventually_crossings_with_sharp_margins hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  let hC' := affinePairing hC hcirc (2 : ℂ) 0
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
    hcirc ω (2 * r) ((2 : ℝ) • z) - hcirc ω 2 0
  have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
    have hcirc_eq : hcirc' = affineCircle hcirc (2 : ℂ) 0 := by
      funext ω r z
      simp [hcirc', affineCircle, Complex.real_smul]
    rw [hcirc_eq]
    exact hAff Ω P hC hcirc hGFF (2 : ℂ) (by norm_num) 0
  have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) := by
    exact isLQGMeasureOfField_normalizedPullback (hCC Ω P γ α₀ hC hcirc)
      hGFF hγ hγ2 hα₀ hμ (by norm_num)
  have hunit := hbound α₀ hα₀ Ω P hC' hcirc'
    (fun ω => normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) hGFF' hμ'
  have hscale := clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ 2 (by norm_num)
  have hcompat := clusterCompatibility_proved hI2 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ 2 (by norm_num)
  filter_upwards [hunit, hscale, hcompat] with ω hunit hscale hcompat
  have htend : Tendsto (fun ε : ℝ => ε / 4) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa using (continuous_id.div_const 4).tendsto (0 : ℝ) |>.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      change 0 < ε / 4
      exact div_pos (show 0 < ε from hε) (by norm_num)
  filter_upwards [htend.eventually hunit,
    (eventually_lt_nhds (show (0 : ℝ) < 1 / 16 by norm_num)).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hunit hεsmall hε
  apply crossings_of_larger_disc_normalization (μ ω)
    (normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω))
    (Real.exp (γ * (lqgQ γ * Real.log 2 + fieldCircleAverage α₀ (hcirc ω) 2 0)))
    α ε (Real.exp_pos _) hε hεsmall hunit hscale
  intro z hz t ht hcl
  have heq := hcompat t ht 1 (by norm_num) z hz 1 (by norm_num) hcl 2 (by norm_num)
  exact heq

/-- The same boundary-free estimate holds for all poles, since clusters
whose pole lies outside the unit disc are empty. -/
theorem ae_crossings_without_boundary_margin_all_poles
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∀ w ∈ ball (0 : ℂ) 1 \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc (ε / 2) (Real.sqrt ε), ∀ z : ℂ, ∀ t : ℝ, 0 < t →
        closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 → ρ + ρ / 50 < dist z w →
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hbound⟩ :=
    ae_crossings_without_boundary_margin_of_scaledField hI2 h6 hAff hCC γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hbound α₀ hα₀ Ω P hC hcirc μ hGFF hμ] with ω hω
  filter_upwards [hω] with ε hε
  intro w hw
  obtain ⟨ρ, hρ, hρbound⟩ := hε w hw
  refine ⟨ρ, hρ, ?_⟩
  intro z t ht hcl hpole
  by_cases hz : z ∈ ball (0 : ℂ) 1
  · exact hρbound z hz t ht hcl hpole
  · rw [cluster_eq_empty_of_pole_not_mem hz ht.le]
    simp [crossingComponents, connectedComponentsIn]

end HarmonicBalls
