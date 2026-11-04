import HarmonicBalls.Proofs.Sec5.ClusterMeasurability

/-! # Simultaneous scaling in the center and time -/

namespace HarmonicBalls

universe u

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped Pointwise

/-- Joint measurability in the center and time upgrades the normalized
measure law to a simultaneous cluster-family scaling law. -/
theorem jointClusterScaleInvariance_of_measurable
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hmeas : AEMeasurable
      (fun ν : Measure ℂ => fun p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ) =>
        cluster ν 1 p.1 p.2) (Measure.map μ P))
    {k : ℝ} (hk : 0 < k) :
    IdentDistrib
      (fun ω (p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ)) => cluster (μ ω) 1 p.1 p.2)
      (fun ω (p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ)) =>
        k⁻¹ • cluster (μ ω) k (k • (p.1 : ℂ))
          (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * p.2)) P P := by
  have hd := (h.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ hk).comp_of_aemeasurable hmeas
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ k hk] with ω hω
  funext p
  exact hω p.1 p.1.property p.2 p.2.property

/-- Measurability of all least-supersolution evaluations suffices for joint
measurability of the cluster family in center and time. -/
theorem measurable_jointClusterFamily_of_leastSupersolution
    (hv : ∀ z ∈ ball (0 : ℂ) 1, ∀ (t : Ioi (0 : ℝ)) (x : ℂ),
      Measurable (fun ν : Measure ℂ => leastSupersolution ν 1 z t x)) :
    Measurable (fun ν : Measure ℂ => fun p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ) =>
      cluster ν 1 p.1 p.2) := by
  apply Measurable.of_eval
  intro p
  have h := measurable_cluster_family_of_measurable_leastSupersolution id 1 p.1 (hv p.1 p.1.property)
  exact (measurable_pi_apply p.2).comp h

/-- The simultaneous center-and-time scaling law also holds for regularized
clusters, when both joint measurability and cluster openness are available. -/
theorem jointRegularizedClusterScaleInvariance_of_measurable
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hmeas : AEMeasurable
      (fun ν : Measure ℂ => fun p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ) =>
        cluster ν 1 p.1 p.2) (Measure.map μ P))
    (hopen : ClusterOpenLaplacianStmt.{u}) {k : ℝ} (hk : 0 < k) :
    IdentDistrib
      (fun ω (p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ)) =>
        regularizedCluster (μ ω) 1 p.1 p.2)
      (fun ω (p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ)) =>
        k⁻¹ • regularizedCluster (μ ω) k (k • (p.1 : ℂ))
          (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * p.2)) P P := by
  have hd := jointClusterScaleInvariance_of_measurable h hAff hCC hγ hγ2 hα hμ hmeas hk
  have hX : ∀ᵐ ω ∂P, ∀ p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ),
      IsOpen (cluster (μ ω) 1 p.1 p.2) := by
    filter_upwards [hopen γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ] with ω hω p
    exact (hω p.2 1 p.2.property zero_lt_one p.1 p.1.property).1
  have hY : ∀ᵐ ω ∂P, ∀ p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ),
      IsOpen (k⁻¹ • cluster (μ ω) k (k • (p.1 : ℂ))
        (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * p.2)) := by
    filter_upwards [hopen γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ] with ω hω p
    have hz' : k • (p.1 : ℂ) ∈ ball (0 : ℂ) k := by
      have hz := p.1.property
      simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hk] at hz ⊢
      nlinarith
    have ht : 0 < Real.exp (γ * (lqgQ γ * Real.log k +
        fieldCircleAverage α₀ (hcirc ω) k 0)) * (p.2 : ℝ) := mul_pos (Real.exp_pos _) p.2.property
    exact (hω _ k ht hk _ hz').1.smul₀ (inv_ne_zero hk.ne')
  have hreg := identDistrib_regularized_family hd hX hY
  simpa only [regularizedCluster, closure_smul₀' (inv_ne_zero hk.ne'),
    interior_smul₀ (inv_ne_zero hk.ne')] using hreg

end HarmonicBalls
