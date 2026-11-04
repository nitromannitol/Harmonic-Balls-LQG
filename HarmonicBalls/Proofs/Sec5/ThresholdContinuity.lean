import HarmonicBalls.Proofs.Sec5.FiniteContainmentThreshold
import HarmonicBalls.Proofs.Sec5.MassSaturationContinuity

/-! # Cluster continuity through the uniform containment threshold -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Pointwise Topology

universe u

/-- There is a positive finite field-local containment threshold such that
all half-disc-centred clusters are Hausdorff continuous at every positive
time up to and including that threshold. At the threshold the conclusion also
holds if the cluster touches the unit circle. The field locality, affine
invariance and coordinate-change inputs are proposed and await source review. -/
theorem exists_fieldLocal_threshold_with_hausdorff_continuity
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) :
    ∃ H : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] H ∧
      ∀ᵐ ω ∂P, 0 < H ω ∧ H ω ≤ μ ω (ball 0 1) ∧ H ω < ⊤ ∧
        (∀ t : ℝ, 0 < t → (ENNReal.ofReal t < H ω ↔
          ∃ T : ℝ, t < T ∧ μ ω ∈ unitClusterContainmentUntil T)) ∧
        (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioc (0 : ℝ) (H ω).toReal,
          μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t ∧
          ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ s in 𝓝[Ioi (0 : ℝ)] t,
            hausdorffEDist (cluster (μ ω) 1 z s) (cluster (μ ω) 1 z t) < ε) ∧
        ∀ T : ℝ, 0 < T → ENNReal.ofReal T < H ω →
          ∀ z ∈ ball (0 : ℂ) (1 / 2),
            SatisfiesHarmonicBallConditionsOn (μ ω) (regularizedCluster (μ ω) 1 z) z T := by
  obtain ⟨H, hH, hthreshold⟩ := exists_fieldLocal_finite_containment_threshold
    hI2 h53 h54 h71 hγ hγ2 hα hGFF hμ hloc
  have hcont := ae_cluster_hausdorff_continuity_of_mass_eq hI2 h72 hAff hCC
    hγ hγ2 hα hGFF hμ
  have hmass := clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hboundary := h53 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  refine ⟨H, hH, ?_⟩
  filter_upwards [hthreshold, hcont, hmass, hboundary] with ω hthr hcontω hmassω hboundaryω
  rcases hthr with ⟨hpos, hbound, hfinite, hchar, hcontactmass, hproperties⟩
  have hrealpos : 0 < (H ω).toReal := ENNReal.toReal_pos hpos.ne' hfinite.ne
  refine ⟨hpos, hbound, hfinite, hchar, ?_, ?_⟩
  · intro z hz t ht
    have hz1 : z ∈ ball (0 : ℂ) 1 := ball_subset_ball (by norm_num) hz
    have heq : μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t := by
      rcases lt_or_eq_of_le ht.2 with hlt | rfl
      · have htH : ENNReal.ofReal t < H ω := by
          rw [← ENNReal.ofReal_toReal hfinite.ne]
          exact (ENNReal.ofReal_lt_ofReal_iff hrealpos).mpr hlt
        obtain ⟨T, htT, hc⟩ := (hchar t ht.1).mp htH
        have hcl := hc z hz t ⟨ht.1, htT⟩
        exact (hmassω 1 t zero_lt_one ht.1 z hz1).2.2 hcl
          (hboundaryω z hz1 t ht.1 hcl)
      · simpa [ENNReal.ofReal_toReal hfinite.ne] using hcontactmass z hz
    exact ⟨heq, hcontω z hz1 t ht.1 heq⟩
  · intro T hT hTH z hz
    exact (hproperties T hT hTH z hz).1

end HarmonicBalls
