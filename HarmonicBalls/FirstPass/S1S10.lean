import HarmonicBalls.Assembly.ExistenceUniqueness
import HarmonicBalls.Assembly.Novelty
import HarmonicBalls.Proofs.Sec1.LocalityCompatibilityAssembly
import HarmonicBalls.Proofs.Sec10.PrevalenceCrossingAssembly
import HarmonicBalls.Proofs.Sec10.ScalingAssembly
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.Draft.Section2
import HarmonicBalls.Draft.Section5
import HarmonicBalls.Draft.Section10
import HarmonicBalls.Draft.Section11
import HarmonicBalls.Draft.Section3
import HarmonicBalls.FirstPass.Frozen.S1S10
import HarmonicBalls.FirstPass.S1S10.CrossingLemma

/-!
# Sections 1 and 10

Each theorem `firstPass_<section>_<number>` has as conclusion the Draft statement of the numbered result
(or its corrected form) and as hypotheses only:
* Draft statements of other numbered results used by the printed proof (`Draft/Section*.lean`), and
* external inputs: the Proposed statements of `Proposed/LQG.lean` (pending source-check).

No new mathematics is proved in this file for the results below: each is a composition of committed reductions
(`Assembly/`, `Proofs/Sec1`, `Proofs/Sec10`). Hypotheses are kept at the printed quantifier order and carrier.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology

universe u

/-- Theorem 1.1 (theorem:harmonic-balls). Existence (Theorem 5.5) and uniqueness (Proposition 5.6) of
the family of harmonic balls, assembled by `existenceUniquenessHarmonicBallsStmt_of_sec5`. -/
theorem firstPass_1_1
    (h55 : ExistenceHarmonicBallsStmt.{u}) (h56 : UniquenessHarmonicBallsStmt.{u}) :
    ExistenceUniquenessHarmonicBallsStmt.{u} :=
  existenceUniquenessHarmonicBallsStmt_of_sec5 h55 h56

/-- Theorem 1.2 (theorem:harmonic-balls-properties). The Jordan clause is Proposition 10.7; the
non-Lipschitz and non-metric-ball clauses are the Section 11 statements, taken as hypotheses. The family at the
origin is extended to all centres through Theorem 1.1 (`harmonicBallNoveltyStmt_of_existence_and_results`). -/
theorem firstPass_1_2
    (h55 : ExistenceHarmonicBallsStmt.{u}) (h56 : UniquenessHarmonicBallsStmt.{u})
    (hjordan : HarmonicBallComplementBoundaryJordanStmt.{u})
    (hlip : HarmonicBallNotLipschitzStmt.{u})
    (hmetric : HarmonicBallNotMetricBallStmt.{u}) :
    HarmonicBallNoveltyStmt.{u} :=
  harmonicBallNoveltyStmt_of_existence_and_results (firstPass_1_1 h55 h56) hjordan hlip hmetric

/-- Proposition 1.3 (prop:locally-determined). Closed harmonic balls are local sets for the field,
from volume growth (Section 2), Theorem 5.5, Proposition 5.6 and locality of the LQG measure (Proposed input). -/
theorem firstPass_1_3
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h55 : ExistenceHarmonicBallsStmt.{u}) (h56 : UniquenessHarmonicBallsStmt.{u})
    (hmeasure : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureLocality P γ α₀ hC hcirc) :
    HarmonicBallLocalSetStmt.{u} :=
  harmonicBallLocalSet_of_volumeGrowth_existence_uniqueness_and_measureLocality hI2 h55 h56 hmeasure

/-- Lemma 10.1 (lemma:cannot-cross). Deterministic bound `⌈1/α⌉` on the number of crossing components,
from the volume growth of Section 2 and zero-strength existence of the LQG measure (Proposed input). -/
theorem firstPass_10_1
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hE0 : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ 0 hC hcirc) :
    ClusterBoundedCrossingsStmt.{u} :=
  clusterBoundedCrossings_of_volumeGrowth_and_zero_existence hI2 hE0

/-- Proposition 10.7 (prop:boundary-simple-loop-full-cluster), corrected as [C50]: pathwise dyadic
rescaling of Proposition 10.6 (`harmonicBallComplementBoundaryJordan_of_proved_scaling`). The affine invariance
and coordinate-change inputs are Proposed. -/
theorem firstPass_10_7
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h55 : ExistenceHarmonicBallsStmt.{u})
    (h10 : ComplementComponentBoundarySimpleLoopStmt.{u})
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    HarmonicBallComplementBoundaryJordanStmt.{u} :=
  harmonicBallComplementBoundaryJordan_of_proved_scaling hI2 h55 h10 hAff hCC

/-- Lemma 10.6 (prop:boundary-simple-loop), corrected as [C49]: the components of `ℂ \ closure Λ_t(z)`
(not of `B_1 \ closure Λ_t(z)`) have simple-loop boundaries. Proof: almost surely the cluster is open and connected
(Lemma 3.2, `ClusterOpenLaplacianStmt`) and each boundary point `p ≠ 0` has arbitrarily small crossing scales
(Lemma 10.1, `ClusterBoundedCrossingsStmt`); then `firstPass_10_5_corrected` with `E = {0}`. -/
theorem firstPass_10_6
    (h10 : ClusterBoundedCrossingsStmt.{u}) (h32 : ClusterOpenLaplacianStmt.{u})
    (hTor : TorhorstSimpleLoopFrozen) :
    ComplementComponentBoundarySimpleLoopStmt.{u} := by
  intro γ α₀ hγ0 hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨α, -, hA⟩ := h10 γ hγ0 hγ2
  have hA' := hA α₀ hα Ω P hC hcirc μ hGFF hμ
  have hO := h32 γ α₀ hγ0 hγ2 hα Ω P hC hcirc μ hGFF hμ
  filter_upwards [hA', hO] with ω hω hωO
  intro t ht z hz hcl
  obtain ⟨hopen, hconn, -⟩ := hωO t 1 ht one_pos z hz
  have hGb : Bornology.IsBounded (cluster (μ ω) 1 z t) :=
    Metric.isBounded_ball.subset (fun x hx => hx.1)
  have hcross : ∀ p ∈ frontier (cluster (μ ω) 1 z t) \ {0}, ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < δ ∧
      (crossingComponents (cluster (μ ω) 1 z t ∩ ball p (2 * r)) p (r / 3) (2 * r)).Finite := by
    rintro p ⟨hpf, hp0⟩ δ hδ
    have hpB : p ∈ ball (0 : ℂ) 1 := hcl hpf.1
    have hpn : p ≠ 0 := fun h => hp0 (mem_singleton_iff.mpr h)
    have hpnorm : 0 < ‖p‖ := norm_pos_iff.mpr hpn
    have hmpos : 0 < min (δ ^ 2) ((‖p‖ / 20) ^ 2) := lt_min (by positivity) (by positivity)
    obtain ⟨ε, hεP, hεm⟩ := (hω.and (Ioo_mem_nhdsGT hmpos)).exists
    have hε0 : 0 < ε := hεm.1
    have hεδ : ε < δ ^ 2 := lt_of_lt_of_le hεm.2 (min_le_left _ _)
    have hεp : ε ≤ (‖p‖ / 20) ^ 2 := le_of_lt (lt_of_lt_of_le hεm.2 (min_le_right _ _))
    have hsq : Real.sqrt ε ≤ ‖p‖ / 20 := by
      have h := Real.sqrt_le_sqrt hεp
      rwa [Real.sqrt_sq (by positivity)] at h
    have hε20 : 20 * Real.sqrt ε ≤ ‖p‖ := by linarith
    obtain ⟨ρ, ⟨hερ, hρs⟩, hbound⟩ :=
      hεP p ⟨hpB, fun h => absurd (mem_ball_zero_iff.mp h) (not_lt.mpr hε20)⟩
    have hρδ : ρ < δ := lt_of_le_of_lt hρs ((Real.sqrt_lt' hδ).mpr hεδ)
    exact ⟨ρ, lt_of_lt_of_le hε0 hερ, hρδ, Set.finite_of_encard_le_coe (hbound t ht z hcl)⟩
  exact (firstPass_10_5_corrected (G := cluster (μ ω) 1 z t) hconn.nonempty hGb hopen hconn
    ⟨{0}, Set.finite_singleton 0, hcross⟩ hTor).2.2


end HarmonicBalls
