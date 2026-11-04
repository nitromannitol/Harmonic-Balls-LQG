import HarmonicBalls.Proofs.Sec5.ExactContainmentHorizon
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec5.ContactMassContinuity

/-! # Mass bound for the exact containment threshold -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- The exact all-centre containment threshold is finite and bounded by the
mass of the unit disc. Mass conservation holds at the threshold, and every
earlier interval carries the regularized harmonic-ball properties,
simultaneously for all centres in the half-disc.
The proposed LQG measure locality input is explicit. -/
theorem exists_fieldLocal_finite_containment_threshold
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) :
    ∃ H : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] H ∧
      ∀ᵐ ω ∂P, 0 < H ω ∧ H ω ≤ μ ω (ball 0 1) ∧ H ω < ⊤ ∧
        (∀ t : ℝ, 0 < t → (ENNReal.ofReal t < H ω ↔
          ∃ T : ℝ, t < T ∧ μ ω ∈ unitClusterContainmentUntil T)) ∧
        (∀ z ∈ ball (0 : ℂ) (1 / 2), μ ω (cluster (μ ω) 1 z (H ω).toReal) = H ω) ∧
        ∀ T : ℝ, 0 < T → ENNReal.ofReal T < H ω →
          ∀ z ∈ ball (0 : ℂ) (1 / 2),
            SatisfiesHarmonicBallConditionsOn (μ ω) (regularizedCluster (μ ω) 1 z) z T ∧
            ∀ t ∈ Ioo (0 : ℝ) T, closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 ∧
              μ ω (frontier (cluster (μ ω) 1 z t)) = 0 := by
  obtain ⟨H, hH, hthreshold⟩ := exists_fieldLocal_exact_containment_threshold
    hI2 h71 hγ hγ2 hα hGFF hμ hloc
  obtain ⟨βm, βp, hlocfin⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hmass := clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hmono := clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hboundary := h53 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hproperties := ae_uniformLocalClusterProperties_of_containment hGFF hγ hγ2 hα hμ
    (clusterOpenLaplacian_proved hI2) h53 h54
  refine ⟨H, hH, ?_⟩
  filter_upwards [hthreshold, hlocfin, hmass, hmono, hboundary, hproperties] with ω hthr hfin hm hmon hb hp
  let : IsLocallyFiniteMeasure (μ ω) := hfin.1
  have hμfin : μ ω (ball (0 : ℂ) 1) < ⊤ :=
    lt_of_le_of_lt (measure_mono ball_subset_closedBall)
      ((isCompact_closedBall (0 : ℂ) 1).measure_lt_top)
  have hbound : H ω ≤ μ ω (ball (0 : ℂ) 1) := by
    by_contra hn
    have hlt : μ ω (ball (0 : ℂ) 1) < H ω := lt_of_not_ge hn
    obtain ⟨q, hqlo, hqhi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hlt
    have hqpos : 0 < (q : ℝ) := by
      have hqpos' : 0 < (q : ℝ≥0∞) := lt_of_le_of_lt bot_le hqlo
      exact_mod_cast hqpos'
    have hqhi' : ENNReal.ofReal (q : ℝ) < H ω := by simpa using hqhi
    obtain ⟨T, hqT, hc⟩ := (hthr.2 q hqpos).mp hqhi'
    have hz : (0 : ℂ) ∈ ball (0 : ℂ) (1 / 2) := by norm_num
    have hz1 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by norm_num
    have hcl := hc 0 hz q ⟨hqpos, hqT⟩
    have heq := (hm 1 q zero_lt_one hqpos 0 hz1).2.2 hcl (hb 0 hz1 q hqpos hcl)
    have hle : ENNReal.ofReal (q : ℝ) ≤ μ ω (ball (0 : ℂ) 1) := by
      rw [← heq]
      exact measure_mono cluster_subset_ball
    have hqlo' : μ ω (ball (0 : ℂ) 1) < ENNReal.ofReal (q : ℝ) := by simpa using hqlo
    exact (not_lt_of_ge hle) hqlo'
  have hHfin : H ω ≠ ⊤ := (lt_of_le_of_lt hbound hμfin).ne
  have hHreal : 0 < (H ω).toReal := ENNReal.toReal_pos hthr.1.ne' hHfin
  have hHmass : ∀ z ∈ ball (0 : ℂ) (1 / 2),
      μ ω (cluster (μ ω) 1 z (H ω).toReal) = H ω := by
    intro z hz
    have hz1 : z ∈ ball (0 : ℂ) 1 := ball_subset_ball (by norm_num) hz
    have heq : μ ω (cluster (μ ω) 1 z (H ω).toReal) = ENNReal.ofReal (H ω).toReal := by
      apply cluster_measure_eq_of_earlier_mass_eq (μ ω) 1 z hHreal
      · intro s hs
        exact hmon s (H ω).toReal 1 hs.1 hs.2.le zero_lt_one z hz1
      · exact (hm 1 (H ω).toReal zero_lt_one hHreal z hz1).1
      · intro s hs
        have hsH : ENNReal.ofReal s < H ω := by
          rw [← ENNReal.ofReal_toReal hHfin]
          exact (ENNReal.ofReal_lt_ofReal_iff hHreal).mpr hs.2
        obtain ⟨T, hsT, hc⟩ := (hthr.2 s hs.1).mp hsH
        have hcl := hc z hz s ⟨hs.1, hsT⟩
        exact (hm 1 s zero_lt_one hs.1 z hz1).2.2 hcl (hb z hz1 s hs.1 hcl)
    simpa [ENNReal.ofReal_toReal hHfin] using heq
  refine ⟨hthr.1, hbound, lt_of_le_of_lt hbound hμfin, hthr.2, hHmass, ?_⟩
  intro T hT hTH
  obtain ⟨S, hTS, hc⟩ := (hthr.2 T hT).mp hTH
  apply hp T hT
  intro z hz t ht
  exact hc z hz t ⟨ht.1, lt_trans ht.2 hTS⟩

end HarmonicBalls
