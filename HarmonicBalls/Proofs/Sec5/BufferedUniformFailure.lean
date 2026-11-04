import HarmonicBalls.Proofs.Sec5.ObstacleCentreContinuity
import HarmonicBalls.Proofs.Sec3.OpenLaplacian
import HarmonicBalls.Proofs.Sec5.ContainmentEventLaw

/-! # A measurable buffered horizon and uniform failure estimates -/

namespace HarmonicBalls

open MeasureTheory Metric Set ProbabilityTheory Filter TopologicalSpace
open scoped ENNReal

universe u

/-- A measurable countable-test horizon controls all centres with a fixed
buffer from the boundary, for every admissible measure. -/
theorem exists_measurable_bufferedClusterHorizon :
    ∃ (e : ℕ → {z // z ∈ ball (0 : ℂ) (1 / 2)}) (H : Measure ℂ → ℝ),
      DenseRange e ∧ Measurable H ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βm βp, VolumeGrowth ν 1 βm βp) →
      (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t : ℝ, 0 < t → IsOpen (cluster ν 1 z t)) →
      (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ s t : ℝ, 0 < s → s ≤ t →
        cluster ν 1 z s ⊆ cluster ν 1 z t) →
      (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) (H ν),
        closure (cluster ν 1 z t) ⊆ closedBall 0 (3 / 4)) ∧
      H ν = realDenseSequenceBallHorizon (3 / 4) (fun i t => cluster ν 1 (e i) t) := by
  let J := {z // z ∈ ball (0 : ℂ) (1 / 2)}
  let : Nonempty J := ⟨⟨0, by norm_num⟩⟩
  let e : ℕ → J := denseSeq J
  let e' : ℕ → ball (0 : ℂ) 1 := fun i =>
    ⟨e i, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) (e i).property⟩
  obtain ⟨H, hH, hHgood⟩ := exists_measurable_countableClusterHorizon_of_volumeGrowth
    zero_lt_one e' (3 / 4)
  refine ⟨e, H, denseRange_denseSeq J, hH, ?_⟩
  intro ν hloc hvol hopen hmono
  have hEq : H ν = realDenseSequenceBallHorizon (3 / 4) (fun i t => cluster ν 1 (e i) t) :=
    hHgood ν hloc hvol
  have hcover : ∀ (j : J) n, cluster ν 1 j (reciprocalTime n) ⊆
      closure (⋃ i, cluster ν 1 (e i) (reciprocalTime n)) := by
    apply countableCentres_coverage_of_dense_point_sections e (denseRange_denseSeq J)
      (fun j t => cluster ν 1 j t)
    · intro j n
      exact hopen j j.property _ (reciprocalTime n).property
    · intro n m
      let f : J → ball (0 : ℂ) 1 := fun j =>
        ⟨j, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) j.property⟩
      have hf : Continuous f := continuous_subtype_val.subtype_mk _
      obtain ⟨βm, βp, hv⟩ := hvol
      exact (isOpen_cluster_centre_section hloc zero_lt_one hv
        (reciprocalTime n).property (denseSeq ℂ m)).preimage hf
  constructor
  · intro z hz t ht
    have hc := closure_subset_closedBall_of_countable_centres_at_tests
      (F := fun (j : J) (s : Ioi (0 : ℝ)) => cluster ν 1 j s) e
      (fun i s => hopen (e i) (e i).property s s.property)
      (fun j s s' hss => hmono j j.property s s' s.property hss) hcover
      (t := ⟨t, ht.1⟩) (by simpa [hEq] using ht.2) ⟨z, hz⟩
    exact hc
  · exact hEq

/-- The deterministic buffered-horizon property holds simultaneously for
all centres and times under the LQG volume-growth and cluster inputs. -/
theorem ae_bufferedClusterHorizon_of_volumeGrowth
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h32 : ClusterOpenLaplacianStmt.{u})
    (h33 : ClusterMonotoneStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (e : ℕ → {z // z ∈ ball (0 : ℂ) (1 / 2)}) (H : Measure ℂ → ℝ)
    (hH : ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βm βp, VolumeGrowth ν 1 βm βp) →
      (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t : ℝ, 0 < t → IsOpen (cluster ν 1 z t)) →
      (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ s t : ℝ, 0 < s → s ≤ t →
        cluster ν 1 z s ⊆ cluster ν 1 z t) →
      (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) (H ν),
        closure (cluster ν 1 z t) ⊆ closedBall 0 (3 / 4)) ∧
      H ν = realDenseSequenceBallHorizon (3 / 4) (fun i t => cluster ν 1 (e i) t)) :
    ∀ᵐ ω ∂P,
      (∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) (H (μ ω)),
        closure (cluster (μ ω) 1 z t) ⊆ closedBall 0 (3 / 4)) ∧
      H (μ ω) = realDenseSequenceBallHorizon (3 / 4) (fun i t => cluster (μ ω) 1 (e i) t) := by
  obtain ⟨βm, βp, hvol⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  filter_upwards [hvol, h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    h33 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hv hopen hmono
  apply hH (μ ω) hv.1 ⟨βm, βp, hv.2 1 zero_lt_one⟩
  · intro z hz t ht
    exact (hopen t 1 ht zero_lt_one z (ball_subset_ball (by norm_num) hz)).1
  · intro z hz s t hs hst
    exact hmono s t 1 hs hst zero_lt_one z (ball_subset_ball (by norm_num) hz)

/-- Uniform outer-failure estimates follow from the measurable buffered
horizon, without assuming measurability of the all-centre containment event. -/
theorem uniformDyadicFailureBounds_of_bufferedHorizon
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h32 : ClusterOpenLaplacianStmt.{u})
    (h33 : ClusterMonotoneStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∃ b : ℕ → ℝ≥0∞, (⨅ m, b m) = 0 ∧ ∀ m n,
      P (normalizedDyadicContainmentEvent γ α₀ hcirc μ m n)ᶜ ≤ b m := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  obtain ⟨e, H, he, hHmeas, hH⟩ := exists_measurable_bufferedClusterHorizon
  have hbase := ae_bufferedClusterHorizon_of_volumeGrowth hI2 h32 h33 hγ hγ2 hα h hμ e H hH
  have hpos : ∀ᵐ ω ∂P, 0 < H (μ ω) := by
    filter_upwards [hbase, ae_countableCentresHorizon_pos_of_upperBound h hγ hγ2 hα hμ h71 e]
      with ω hω hp
    rwa [hω.2]
  let B : ℕ → Set Ω := fun m => {ω | H (μ ω) ≤ (2 : ℝ)⁻¹ ^ m}
  let b : ℕ → ℝ≥0∞ := fun m => P (B m)
  have hT : AEMeasurable (fun ω => H (μ ω)) P :=
    hHmeas.comp_aemeasurable (h.aemeasurable_lqgMeasure hμ)
  have hB (m : ℕ) : NullMeasurableSet (B m) P :=
    hT.nullMeasurableSet_preimage measurableSet_Iic
  have hanti : Antitone B := by
    intro i j hij ω hω
    change H (μ ω) ≤ (2 : ℝ)⁻¹ ^ j at hω
    change H (μ ω) ≤ (2 : ℝ)⁻¹ ^ i
    exact hω.trans (pow_le_pow_of_le_one (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by norm_num)
      (show (2 : ℝ)⁻¹ ≤ 1 by norm_num) hij)
  have hzero : (⨅ m, b m) = 0 := by
    change (⨅ m, P (B m)) = 0
    rw [← hanti.measure_iInter hB ⟨0, measure_ne_top P _⟩]
    apply measure_mono_null _ (ae_iff.mp hpos)
    intro ω hω hp
    have hall : ∀ m, H (μ ω) ≤ (2 : ℝ)⁻¹ ^ m := Set.mem_iInter.mp hω
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hp (by norm_num : (2 : ℝ)⁻¹ < 1)
    exact (not_le_of_gt hm) (hall m)
  refine ⟨b, hzero, ?_⟩
  intro m n
  let k : ℝ := (2 : ℝ) ^ n
  have hk : 0 < k := by positivity
  let C := fun (ω : Ω) (φ : ℂ → ℝ) => (k ^ 2)⁻¹ * hC ω (fun y => φ (y / (k : ℂ))) -
    hcirc ω k 0 * ∫ x, φ x
  let circ := fun ω r z => hcirc ω (k * r) (k • z) - hcirc ω k 0
  let ν := fun ω => normalizedPullbackMeasure γ α₀ k (hcirc ω) (μ ω)
  have hGFFscaled : IsWholePlaneGFF P C circ := by
    have hh := hAff h (k : ℂ) (by exact_mod_cast hk.ne') 0
    simpa only [C, circ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hk, Complex.real_smul, add_zero, sub_zero] using hh
  have hν : IsLQGMeasureOfField P γ α₀ circ ν :=
    isLQGMeasureOfField_normalizedPullback hCC h hγ hγ2 hα hμ hk
  have hscaled := ae_bufferedClusterHorizon_of_volumeGrowth hI2 h32 h33 hγ hγ2 hα
    hGFFscaled hν e H hH
  have hd := (h.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ hk).comp hHmeas
  calc
    P (normalizedDyadicContainmentEvent γ α₀ hcirc μ m n)ᶜ ≤
        P {ω | H (ν ω) ≤ (2 : ℝ)⁻¹ ^ m} := by
      apply measure_mono_ae
      filter_upwards [hscaled] with ω hω hbad
      by_contra hnot
      have hp : (2 : ℝ)⁻¹ ^ m < H (ν ω) := lt_of_not_ge hnot
      apply hbad
      intro z hz t ht
      have hc := hω.1 z hz t ⟨ht.1, ht.2.trans hp⟩
      exact hc.trans (closedBall_subset_ball (by norm_num))
    _ = b m := (hd.measure_mem_eq measurableSet_Iic).symm

/-- Cofinal regularized intervals from the uniform outer-failure route. -/
theorem cofinalRegularizedClusterIntervals_of_bufferedHorizon
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h32 : ClusterOpenLaplacianStmt.{u})
    (h33 : ClusterMonotoneStmt.{u}) (h53 : ClusterBoundaryMeasureZeroStmt.{u})
    (h54 : RegularizedClusterHarmonicBallsStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) :
    CofinalRegularizedClusterIntervalsStep.{u} := by
  apply cofinalRegularizedClusterIntervals_of_uniformFailure h32 h53 h54 hAff hCC
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ h hμ
  exact uniformDyadicFailureBounds_of_bufferedHorizon hI2 h32 h33 h71 h
    (hAff P hC hcirc) (hCC P γ α₀ hC hcirc) hγ hγ2 hα hμ

/-- The cluster openness and monotonicity inputs follow from volume growth. -/
theorem uniformDyadicFailureBounds_of_volumeGrowth
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∃ b : ℕ → ℝ≥0∞, (⨅ m, b m) = 0 ∧ ∀ m n,
      P (normalizedDyadicContainmentEvent γ α₀ hcirc μ m n)ᶜ ≤ b m :=
  uniformDyadicFailureBounds_of_bufferedHorizon hI2 (clusterOpenLaplacian_proved hI2)
    (clusterMonotone_proved hI2) h71 h hAff hCC hγ hγ2 hα hμ

end HarmonicBalls
