import HarmonicBalls.Proofs.Sec5.ObstaclePotentialStability
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import HarmonicBalls.Proofs.Sec5.CofinalFromCountableTests

/-! # A measurable decoder for Green potentials of good measures -/

namespace HarmonicBalls

open MeasureTheory Metric Set TopologicalSpace ProbabilityTheory Filter
open scoped Pointwise

universe u

/-- The continuous Green potential can be recovered measurably from any
measure for which the potential is continuous on the closed disc. -/
theorem exists_measurable_greenPotentialBall_decoder {R : ℝ} (hR : 0 < R) :
    ∃ Q : Measure ℂ → C(closedBall (0 : ℂ) R, ℝ), Measurable Q ∧
      ∀ ν : Measure ℂ, ContinuousOn (greenPotentialBall ν R) (closedBall 0 R) →
        ∀ y, Q ν y = greenPotentialBall ν R y := by
  classical
  let X := closedBall (0 : ℂ) R
  let : Nonempty X := ⟨⟨0, by change (0 : ℂ) ∈ closedBall 0 R; simpa using hR.le⟩⟩
  let e : ℕ → X := denseSeq X
  let enc : C(X, ℝ) → ℕ → ℝ := fun f n => f (e n)
  have henc : Measurable enc := by
    apply Measurable.of_eval
    intro n
    exact ContinuousMap.measurable_eval (e n)
  have hinj : Function.Injective enc := by
    intro f g hfg
    apply ContinuousMap.ext
    intro x
    have hfun : (f : X → ℝ) = g := (denseRange_denseSeq X).equalizer f.continuous g.continuous (by
      funext n
      exact congrFun hfg n)
    exact congrFun hfun x
  have hemb : MeasurableEmbedding enc := henc.measurableEmbedding hinj
  let q : Measure ℂ → ℕ → ℝ := fun ν n => greenPotentialBall ν R (e n)
  have hq : Measurable q := by
    apply Measurable.of_eval
    intro n
    exact measurable_greenPotentialBall_measure R (e n)
  refine ⟨fun ν => hemb.invFun (q ν), hemb.measurable_invFun.comp hq, ?_⟩
  intro ν hcont y
  let f : C(X, ℝ) := ⟨fun x => greenPotentialBall ν R x, hcont.domRestrict⟩
  have heq : q ν = enc f := rfl
  change hemb.invFun (q ν) y = _
  rw [heq, hemb.leftInverse_invFun f]
  rfl

/-- A single Borel event represents fixed-point cluster membership for every
locally finite measure satisfying volume growth on the disc. -/
theorem exists_measurableSet_mem_cluster_of_volumeGrowth
    {R t : ℝ} {z x : ℂ} (hR : 0 < R) (hz : z ∈ ball (0 : ℂ) R) (ht : 0 < t) :
    ∃ E : Set (Measure ℂ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βminus βplus, VolumeGrowth ν R βminus βplus) →
        (ν ∈ E ↔ x ∈ cluster ν R z t) := by
  classical
  by_cases hx : x ∈ ball (0 : ℂ) R
  · by_cases hxz : x = z
    · refine ⟨univ, MeasurableSet.univ, ?_⟩
      intro ν _ _
      constructor
      · intro _
        exact ⟨hx, Or.inl hxz⟩
      · intro _
        trivial
    · let A := {ν : Measure ℂ // IsLocallyFiniteMeasure ν ∧
          ∃ βminus βplus, VolumeGrowth ν R βminus βplus}
      obtain ⟨Q, hQ, hQeq⟩ := exists_measurable_greenPotentialBall_decoder hR
      have hcont : ∀ a : A, ContinuousOn (greenPotentialBall a.1 R) (closedBall 0 R) := by
        intro a
        obtain ⟨βminus, βplus, hv⟩ := a.2.2
        exact greenPotentialBallContinuousStep_holds a.1 a.2.1 R βminus βplus hR hv
      have hclass : ∀ a : A, (shiftedSupersolutions a.1 R z t).Nonempty := by
        intro a
        obtain ⟨βminus, βplus, hv⟩ := a.2.2
        refine ⟨greenPotentialBall a.1 R, greenPotentialBall_mem_shiftedSupersolutions
          ht.le (hcont a) ?_⟩
        exact (greenPotentialBallLaplacianStep_holds a.1 a.2.1 R βminus βplus hR hv).laplacianLE
      let q : A → C(closedBall (0 : ℂ) R, ℝ) := fun a => Q a.1
      let f : A → ℝ := fun a => shiftedOdometer a.1 R z t x
      have hdist : ∀ a b, dist (f a) (f b) ≤ (2 : NNReal) * dist (q a) (q b) := by
        intro a b
        rw [Real.dist_eq]
        apply abs_shiftedOdometer_sub_le_of_greenPotentialBall (hclass a) (hclass b) ?_
          (ball_subset_closedBall hx) hxz
        intro y hy
        have h := ContinuousMap.dist_apply_le_dist (f := q a) (g := q b) ⟨y, hy⟩
        simpa only [Real.dist_eq, q, hQeq _ (hcont a), hQeq _ (hcont b)] using h
      obtain ⟨g, hg, hgf⟩ := exists_lipschitz_factor_of_dist_le q f 2 hdist
      refine ⟨{ν | 0 < g (Q ν)}, measurableSet_lt measurable_const (hg.continuous.measurable.comp hQ), ?_⟩
      intro ν hloc hvol
      let a : A := ⟨ν, hloc, hvol⟩
      obtain ⟨βminus, βplus, hv⟩ := hvol
      have heq := (obstacleCompatibilityShiftStep_holds ν hloc R βminus βplus hR hv z hz t ht).2.2.1
      change (0 < g (Q ν)) ↔ x ∈ cluster ν R z t
      rw [heq, mem_nonCoincidenceSet_iff]
      have hgfeq : shiftedOdometer ν R z t x = g (Q ν) := hgf a
      simp only [hx, hxz, false_or, true_and, hgfeq]
  · refine ⟨∅, MeasurableSet.empty, ?_⟩
    intro ν _ _
    constructor
    · intro h
      exact False.elim h
    · intro h
      exact False.elim (hx h.1)

/-- A Borel horizon agrees with the countable cluster horizon on all
locally finite measures with volume growth. -/
theorem exists_measurable_countableClusterHorizon_of_volumeGrowth
    {ι : Type*} [Countable ι] {R : ℝ} (hR : 0 < R)
    (e : ι → ball (0 : ℂ) R) (r : ℝ) :
    ∃ H : Measure ℂ → ℝ, Measurable H ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βminus βplus, VolumeGrowth ν R βminus βplus) →
      H ν = realDenseSequenceBallHorizon r (fun i t => cluster ν R (e i) t) := by
  classical
  choose E hE hcorrect using fun (i : ι) (n m : ℕ) =>
    exists_measurableSet_mem_cluster_of_volumeGrowth hR (e i).property
      (reciprocalTime n).property (x := denseSeq ℂ m)
  let profile : Measure ℂ → ι → ℕ → ℕ → Prop := fun ν i n m => ν ∈ E i n m
  have hm : Measurable profile := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro n
    apply Measurable.of_eval
    intro m
    exact measurableSet_setOfPred.mp (hE i n m)
  refine ⟨fun ν => realCountableTestHorizon r (profile ν),
    (measurable_realCountableTestHorizon r).comp hm, ?_⟩
  intro ν hloc hv
  simp only [realCountableTestHorizon, realDenseSequenceBallHorizon,
    denseSequenceBallHorizon, denseSequenceBallTest, profile]
  congr 2
  funext n
  have heq : (∀ i m, ν ∈ E i n m → denseSeq ℂ m ∈ closedBall (0 : ℂ) r) ↔
      (∀ i m, denseSeq ℂ m ∈ cluster ν R (e i) (reciprocalTime n) →
        denseSeq ℂ m ∈ closedBall (0 : ℂ) r) := by
    simp only [hcorrect _ _ _ ν hloc hv]
  rw [propext heq]
  rfl

/-- Cofinal local intervals follow from centre coverage and the numbered
inputs, without assuming countable cluster-test measurability. The affine
and coordinate-change inputs are staged separately. -/
theorem cofinalRegularizedClusterIntervals_of_volumeGrowth_and_countableCentres
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc)
    (e : ℕ → {z // z ∈ ball (0 : ℂ) (1 / 2)})
    (hcover : ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        ∀ᵐ ω ∂P, ∀ (j : {z // z ∈ ball (0 : ℂ) (1 / 2)}) (n : ℕ),
          cluster (μ ω) 1 j (reciprocalTime n) ⊆
            closure (⋃ i, cluster (μ ω) 1 (e i) (reciprocalTime n))) :
    CofinalRegularizedClusterIntervalsStep.{u} := by
  apply cofinalRegularizedClusterIntervals_of_normalizedDyadicEstimates
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ h hμ
  let e' : ℕ → ball (0 : ℂ) 1 := fun i =>
    ⟨e i, ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) (e i).property⟩
  obtain ⟨H, hHmeas, hHgood⟩ :=
    exists_measurable_countableClusterHorizon_of_volumeGrowth zero_lt_one e' (3 / 4)
  let ν : ℕ → Ω → Measure ℂ := fun n ω =>
    normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)
  let T : ℕ → Ω → ℝ := fun n ω => H (ν n ω)
  have hlaw : ∀ n, IdentDistrib (fun ω => H (μ ω)) (T n) P P := by
    intro n
    exact (h.identDistrib_normalizedPullback (hAff P hC hcirc) (hCC P γ α₀ hC hcirc)
      hγ hγ2 hα hμ (k := (2 : ℝ) ^ n) (by positivity)).comp hHmeas
  have hbase : ∀ᵐ ω ∂P, H (μ ω) = realDenseSequenceBallHorizon (3 / 4)
      (fun i t => cluster (μ ω) 1 (e i) t) := by
    obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα h hμ
    filter_upwards [hae] with ω hω
    exact hHgood (μ ω) hω.1 ⟨βm, βp, hω.2 1 zero_lt_one⟩
  refine ⟨T, fun n => (hlaw n).symm.trans (hlaw 0), ?_, ?_⟩
  · apply (hlaw 0).ae_snd measurableSet_Ioi
    filter_upwards [ae_countableCentresHorizon_pos_of_upperBound h hγ hγ2 hα hμ h71 e,
      hbase] with ω hpos heq
    rwa [heq]
  · apply ae_all_iff.mpr
    intro n
    let k : ℝ := (2 : ℝ) ^ n
    have hk : 0 < k := by positivity
    let C := fun (ω : Ω) (φ : ℂ → ℝ) => (k ^ 2)⁻¹ * hC ω (fun y => φ (y / (k : ℂ))) -
      hcirc ω k 0 * ∫ x, φ x
    let circ := fun ω r z => hcirc ω (k * r) (k • z) - hcirc ω k 0
    have hGFFscaled : IsWholePlaneGFF P C circ := by
      have hh := hAff P hC hcirc h (k : ℂ) (by exact_mod_cast hk.ne') 0
      simpa only [C, circ, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hk, Complex.real_smul, add_zero, sub_zero] using hh
    have hν : IsLQGMeasureOfField P γ α₀ circ (ν n) :=
      isLQGMeasureOfField_normalizedPullback (hCC P γ α₀ hC hcirc) h hγ hγ2 hα hμ hk
    have hp := ae_uniformLocalProperties_of_countableHorizon hGFFscaled hγ hγ2 hα hν
      h32 h33 h53 h54 h71 e (hcover γ α₀ hγ hγ2 hα Ω P C circ (ν n) hGFFscaled hν)
    obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFFscaled hν
    filter_upwards [hp, hae] with ω hω hv
    have heq := hHgood (ν n ω) hv.1 ⟨βm, βp, hv.2 1 zero_lt_one⟩
    change ∀ z ∈ ball (0 : ℂ) (1 / 2), _
    rw [show T n ω = _ from heq]
    exact hω.2

/-- A Borel decoder represents the entire positive-time cluster family on
every locally finite measure with volume growth. The function space carries
the pointwise evaluation sigma algebra. -/
theorem exists_measurable_clusterFamily_of_volumeGrowth {R : ℝ} (hR : 0 < R) :
    ∃ F : Measure ℂ → (ball (0 : ℂ) R × Ioi (0 : ℝ) → Set ℂ),
      Measurable F ∧ ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        (∃ βminus βplus, VolumeGrowth ν R βminus βplus) →
        F ν = fun p => cluster ν R p.1 p.2 := by
  classical
  choose E hE hcorrect using fun (p : ball (0 : ℂ) R × Ioi (0 : ℝ)) (x : ℂ) =>
    exists_measurableSet_mem_cluster_of_volumeGrowth hR p.1.property p.2.property (x := x)
  let F : Measure ℂ → (ball (0 : ℂ) R × Ioi (0 : ℝ) → Set ℂ) :=
    fun ν p => {x | ν ∈ E p x}
  have hF : Measurable F := by
    apply Measurable.of_eval
    intro p
    apply Measurable.of_eval
    intro x
    exact measurableSet_setOfPred.mp (hE p x)
  refine ⟨F, hF, ?_⟩
  intro ν hloc hv
  funext p
  ext x
  exact hcorrect p x ν hloc hv

/-- Joint scaling of all clusters follows from volume growth and the two
staged field inputs, without a cluster-family measurability hypothesis. -/
theorem jointClusterScaleInvariance_of_volumeGrowth
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {k : ℝ} (hk : 0 < k) :
    IdentDistrib
      (fun ω (p : ball (0 : ℂ) 1 × Ioi (0 : ℝ)) => cluster (μ ω) 1 p.1 p.2)
      (fun ω (p : ball (0 : ℂ) 1 × Ioi (0 : ℝ)) =>
        k⁻¹ • cluster (μ ω) k (k • (p.1 : ℂ))
          (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * p.2)) P P := by
  obtain ⟨F, hF, hFgood⟩ := exists_measurable_clusterFamily_of_volumeGrowth zero_lt_one
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
  have hfirst : (fun ω => F (μ ω)) =ᵐ[P]
      (fun ω p => cluster (μ ω) 1 p.1 p.2) := by
    obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα h hμ
    filter_upwards [hae] with ω hv
    exact hFgood (μ ω) hv.1 ⟨βm, βp, hv.2 1 zero_lt_one⟩
  have hsecond : (fun ω => F (ν ω)) =ᵐ[P]
      (fun ω p => k⁻¹ • cluster (μ ω) k (k • (p.1 : ℂ))
        (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * p.2)) := by
    obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFFscaled hν
    filter_upwards [hae, clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ k hk] with ω hv hscale
    rw [hFgood (ν ω) hv.1 ⟨βm, βp, hv.2 1 zero_lt_one⟩]
    funext p
    exact hscale p.1 p.1.property p.2 p.2.property
  have hd := (h.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ hk).comp hF
  exact (IdentDistrib.of_ae_eq hd.aemeasurable_fst hfirst).symm.trans
    (hd.trans (IdentDistrib.of_ae_eq hd.aemeasurable_snd hsecond))

/-- Lemma 5.7 follows from volume growth and the staged affine and
coordinate-change inputs. -/
theorem clusterScaleInvariance_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hAff : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureCoordChange P γ α₀ hC hcirc) : ClusterScaleInvarianceStmt.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ h hμ k hk z hz
  have hd := jointClusterScaleInvariance_of_volumeGrowth h hI2 (hAff P hC hcirc)
    (hCC P γ α₀ hC hcirc) hγ hγ2 hα hμ hk
  have hm : Measurable (fun F : (ball (0 : ℂ) 1 × Ioi (0 : ℝ) → Set ℂ) =>
      fun t : Ioi (0 : ℝ) => F (⟨z, hz⟩, t)) := by
    apply Measurable.of_eval
    intro t
    exact measurable_pi_apply ((⟨z, hz⟩ : ball (0 : ℂ) 1), t)
  exact hd.comp hm

/-- Joint scaling also holds for the regularized clusters. -/
theorem jointRegularizedClusterScaleInvariance_of_volumeGrowth
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hopen : ClusterOpenLaplacianStmt.{u}) {k : ℝ} (hk : 0 < k) :
    IdentDistrib
      (fun ω (p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ)) =>
        regularizedCluster (μ ω) 1 p.1 p.2)
      (fun ω (p : {z // z ∈ ball (0 : ℂ) 1} × Ioi (0 : ℝ)) =>
        k⁻¹ • regularizedCluster (μ ω) k (k • (p.1 : ℂ))
          (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * p.2)) P P := by
  have hd := jointClusterScaleInvariance_of_volumeGrowth h hI2 hAff hCC hγ hγ2 hα hμ hk
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
