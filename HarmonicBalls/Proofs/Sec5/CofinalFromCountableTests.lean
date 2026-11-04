import HarmonicBalls.Proofs.Sec5.DyadicGeometricScaling
import HarmonicBalls.Proofs.Sec5.HorizonPositivity
import HarmonicBalls.Proofs.Sec5.UniformContainment
import HarmonicBalls.Proofs.Sec5.ScalingMeasure

/-! # Cofinal intervals from countable tests and centre coverage -/

namespace HarmonicBalls

universe u

open MeasureTheory Metric Set ProbabilityTheory TopologicalSpace Filter

/-- Coverage at the tested reciprocal times suffices for every earlier
positive time below the countable horizon. -/
theorem closure_subset_closedBall_of_countable_centres_at_tests
    {ι J : Type*} {r : ℝ} {F : J → Ioi (0 : ℝ) → Set ℂ} (e : ι → J)
    (hopen : ∀ i t, IsOpen (F (e i) t)) (hmono : ∀ j, Monotone (F j))
    (hcover : ∀ j n, F j (reciprocalTime n) ⊆
      closure (⋃ i, F (e i) (reciprocalTime n)))
    {t : Ioi (0 : ℝ)}
    (ht : (t : ℝ) < realDenseSequenceBallHorizon r (fun i => F (e i)))
    (j : J) : closure (F j t) ⊆ closedBall (0 : ℂ) r := by
  classical
  have hfinite : denseSequenceBallHorizon r (fun i => F (e i)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp) (denseSequenceBallHorizon_le_one _ _)
  have hrealpos : 0 < (denseSequenceBallHorizon r (fun i => F (e i))).toReal :=
    lt_trans t.property ht
  have hlt : ENNReal.ofReal (t : ℝ) < denseSequenceBallHorizon r (fun i => F (e i)) := by
    rw [← ENNReal.ofReal_toReal hfinite]
    exact (ENNReal.ofReal_lt_ofReal_iff hrealpos).mpr ht
  change ENNReal.ofReal (t : ℝ) < ⨆ n,
    if denseSequenceBallTest r (fun i => F (e i)) n then
      ENNReal.ofReal (reciprocalTime n) else 0 at hlt
  obtain ⟨n, hn⟩ := lt_iSup_iff.mp hlt
  have htest : denseSequenceBallTest r (fun i => F (e i)) n := by
    by_contra htest
    simp only [htest, ↓reduceIte, not_lt_zero] at hn
  have htime : t ≤ reciprocalTime n := by
    have hn' : ENNReal.ofReal (t : ℝ) < ENNReal.ofReal (reciprocalTime n) := by
      simpa only [htest, ↓reduceIte] using hn
    exact le_of_lt ((ENNReal.ofReal_lt_ofReal_iff (reciprocalTime n).property).mp hn')
  have hsub : (⋃ i, F (e i) (reciprocalTime n)) ⊆ closedBall (0 : ℂ) r := by
    apply iUnion_subset
    intro i
    exact subset_closure.trans
      (closure_subset_closedBall_of_denseSequenceBallTest htest (fun i => hopen i _) i)
  exact closure_minimal (((hmono j htime).trans (hcover j n)).trans
    (closure_minimal hsub isClosed_closedBall)) isClosed_closedBall

/-- At the tested times, openness of the centre sections is needed only at
the countably many dense spatial points to obtain centre coverage. -/
theorem countableCentres_coverage_of_dense_point_sections
    {ι J : Type*} [TopologicalSpace J] (e : ι → J) (he : DenseRange e)
    (F : J → Ioi (0 : ℝ) → Set ℂ)
    (hopen : ∀ j n, IsOpen (F j (reciprocalTime n)))
    (hcentres : ∀ n m, IsOpen {j | denseSeq ℂ m ∈ F j (reciprocalTime n)}) :
    ∀ j n, F j (reciprocalTime n) ⊆
      closure (⋃ i, F (e i) (reciprocalTime n)) := by
  intro j n
  apply subset_closure.trans
  rw [closure_eq_closure_inter_denseSeq (hopen j n)]
  apply closure_mono
  rintro x ⟨hx, m, rfl⟩
  obtain ⟨i, hi⟩ := he.exists_mem_open (hcentres n m) ⟨j, hx⟩
  exact mem_iUnion.mpr ⟨i, hi⟩

/-- A positive countable-centre horizon and centre coverage yield the local
cluster conditions; no measurability of the horizon is needed here. -/
theorem ae_uniformLocalProperties_of_countableHorizon
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    {ι : Type*} (e : ι → {z // z ∈ ball (0 : ℂ) (1 / 2)})
    (hcover : ∀ᵐ ω ∂P, ∀ (j : {z // z ∈ ball (0 : ℂ) (1 / 2)}) (n : ℕ),
      cluster (μ ω) 1 j (reciprocalTime n) ⊆
        closure (⋃ i, cluster (μ ω) 1 (e i) (reciprocalTime n))) :
    ∀ᵐ ω ∂P,
      let H := realDenseSequenceBallHorizon (3 / 4) (fun i t => cluster (μ ω) 1 (e i) t)
      0 < H ∧ ∀ z ∈ ball (0 : ℂ) (1 / 2),
        SatisfiesHarmonicBallConditionsOn (μ ω) (regularizedCluster (μ ω) 1 z) z H ∧
        ∀ t ∈ Ioo 0 H, closure (cluster (μ ω) 1 z t) ⊆ ball 0 1 ∧
          μ ω (frontier (cluster (μ ω) 1 z t)) = 0 := by
  filter_upwards [ae_countableCentresHorizon_pos_of_upperBound h hγ hγ2 hα hμ h71 e,
    hcover, h32 γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ,
    h33 γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ,
    ae_uniformLocalClusterProperties_of_containment h hγ hγ2 hα hμ h32 h53 h54] with ω hpos hcov hopen hmono hlocal
  dsimp only
  refine ⟨hpos, hlocal _ hpos ?_⟩
  intro z hz t ht
  have hop : ∀ i (s : Ioi (0 : ℝ)), IsOpen (cluster (μ ω) 1 (e i) s) := by
    intro i s
    exact (hopen s 1 s.property zero_lt_one (e i)
      (ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) (e i).property)).1
  have hmon : ∀ j : {z // z ∈ ball (0 : ℂ) (1 / 2)},
      Monotone (fun s : Ioi (0 : ℝ) => cluster (μ ω) 1 j s) := by
    intro j s s' hss'
    exact hmono s s' 1 s.property hss' zero_lt_one j
      (ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) j.property)
  have hc := closure_subset_closedBall_of_countable_centres_at_tests
    (F := fun (j : {z // z ∈ ball (0 : ℂ) (1 / 2)}) s => cluster (μ ω) 1 j s)
    e hop hmon hcov (t := ⟨t, ht.1⟩) ht.2 ⟨z, hz⟩
  exact hc.trans (closedBall_subset_ball (by norm_num))

/-- Cofinal intervals follow from only the countable membership tests used by
the horizon, together with countable-centre coverage. The affine field and
coordinate-change assumptions are staged inputs. -/
theorem cofinalRegularizedClusterIntervals_of_countableTests
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
    (htests : ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
        (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        ∀ i n m, AEMeasurable (fun ν : Measure ℂ =>
          denseSeq ℂ m ∈ cluster ν 1 (e i) (reciprocalTime n)) (Measure.map μ P))
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
  let H : Measure ℂ → ℝ := fun ν => realDenseSequenceBallHorizon (3 / 4)
    (fun i t => cluster ν 1 (e i) t)
  let ν : ℕ → Ω → Measure ℂ := fun n ω =>
    normalizedPullbackMeasure γ α₀ ((2 : ℝ) ^ n) (hcirc ω) (μ ω)
  let T : ℕ → Ω → ℝ := fun n ω => H (ν n ω)
  have hH : AEMeasurable H (Measure.map μ P) :=
    aemeasurable_realDenseSequenceBallHorizon_of_tests (Measure.map μ P) (3 / 4)
      (fun ν i t => cluster ν 1 (e i) t) (htests γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ)
  have hlaw : ∀ n, IdentDistrib (fun ω => H (μ ω)) (T n) P P := by
    intro n
    exact (h.identDistrib_normalizedPullback (hAff P hC hcirc) (hCC P γ α₀ hC hcirc)
      hγ hγ2 hα hμ (k := (2 : ℝ) ^ n) (by positivity)).comp_of_aemeasurable hH
  refine ⟨T, fun n => (hlaw n).symm.trans (hlaw 0), ?_, ?_⟩
  · exact (hlaw 0).ae_snd measurableSet_Ioi
      (ae_countableCentresHorizon_pos_of_upperBound h hγ hγ2 hα hμ h71 e)
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
    filter_upwards [hp] with ω hω
    exact hω.2

end HarmonicBalls
