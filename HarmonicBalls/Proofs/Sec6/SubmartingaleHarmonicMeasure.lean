import HarmonicBalls.Proofs.Sec6.StoppedSubmartingale
import HarmonicBalls.Proofs.Sec10.PoleAvoidingGoodAnnulusDecay

/-! # Harmonic measure bounds from stopped submartingales

A nonnegative function vanishing on the interior part of a component's boundary
is bounded by its boundary supremum times the probability of exiting the ambient
domain before hitting the component complement.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology

/-- Boundary domination for a nonnegative bounded function whose values stopped
on leaving an open subdomain form a submartingale. -/
theorem ofReal_le_boundary_mul_harmonicMeasure_of_submartingale
    {A Y : Set ℂ} (hA : IsOpen A) (hY : IsOpen Y) (hAb : Bornology.IsBounded A)
    (hYA : Y ⊆ A) {q : ℂ → ℝ} (hqmeas : Measurable q)
    (hqnonneg : ∀ y, 0 ≤ q y) {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M)
    {B : ℝ≥0∞}
    (hzero : ∀ y ∈ A ∩ frontier Y, q y = 0)
    (hbound : ∀ y ∈ frontier A ∩ closure Y, ENNReal.ofReal (q y) ≤ B)
    {x : ℂ} (hx : x ∈ Y)
    (ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ContinuousPath ℂ)))
    (hsub : Submartingale (fun (n : ℕ) (ω : ContinuousPath ℂ) =>
      q (ω (ContinuousPath.exitTimeTrunc Y n ω))) ℱ (planarBrownianMotion x)) :
    ENNReal.ofReal (q x) ≤ B * planarBrownianMotion x
      {ω | ContinuousPath.exitTime A ω ≤ hittingTime (A \ Y) ω} := by
  let E : Set (ContinuousPath ℂ) :=
    {ω | ContinuousPath.exitTime A ω ≤ ContinuousPath.exitTime Y ω}
  have hYb := hAb.subset hYA
  have hrep := le_integral_exitTime_of_submartingale hY hYb hqmeas hM x ℱ hsub
  have hint := integrable_at_exitTime_of_bounded_measurable hY hYb hqmeas hM x
  have hlin : ENNReal.ofReal (q x) ≤ ∫⁻ ω : ContinuousPath ℂ,
      ENNReal.ofReal (q (ω ((ContinuousPath.exitTime Y ω).toNNReal)))
        ∂(planarBrownianMotion x) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω => hqnonneg _)]
    exact ENNReal.ofReal_le_ofReal hrep
  have hpoint : ∀ᵐ ω ∂(planarBrownianMotion x),
      ENNReal.ofReal (q (ω ((ContinuousPath.exitTime Y ω).toNNReal))) ≤
        E.indicator (fun _ => B) ω := by
    filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hYb,
      ae_planarBrownianMotion_eval_zero x] with ω hfin hstart
    have hstartY : ω 0 ∈ Y := hstart ▸ hx
    have hfrontY := ContinuousPath.coordinate_exitTime_mem_frontier Y hY ω hstartY (ne_top_of_lt hfin)
    by_cases he : ω ∈ E
    · have hle : ContinuousPath.exitTime Y ω ≤ ContinuousPath.exitTime A ω :=
        ContinuousPath.exitTime_mono hYA ω
      have heq : ContinuousPath.exitTime A ω = ContinuousPath.exitTime Y ω := le_antisymm he hle
      have hfrontA := ContinuousPath.coordinate_exitTime_mem_frontier A hA ω
        (hYA hstartY) (by rw [heq]; exact ne_top_of_lt hfin)
      rw [heq] at hfrontA
      simpa only [indicator_of_mem he] using hbound _ ⟨hfrontA, frontier_subset_closure hfrontY⟩
    · have hlt : ContinuousPath.exitTime Y ω < ContinuousPath.exitTime A ω := lt_of_not_ge he
      have hmemA : ω ((ContinuousPath.exitTime Y ω).toNNReal) ∈ A := by
        apply ContinuousPath.mem_of_lt_exitTime
        simpa only [ENNReal.coe_toNNReal (ne_top_of_lt hfin)] using hlt
      simp only [indicator_of_notMem he, hzero _ ⟨hmemA, hfrontY⟩, ENNReal.ofReal_zero, le_refl]
  have hresult := hlin.trans ((lintegral_mono_ae hpoint).trans (lintegral_indicator_const_le E B))
  have heq : E = {ω | ContinuousPath.exitTime A ω ≤ hittingTime (A \ Y) ω} := by
    ext ω
    exact exitTime_le_exitTime_iff_le_hittingTime_sdiff ω
  simpa only [heq] using hresult

/-- A pole-avoiding component satisfies the odometer harmonic-measure bound
whenever its stopped odometer is a submartingale. -/
theorem odometer_le_harmonicMeasure_of_submartingale
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βminus βplus : ℝ} (hV : VolumeGrowth μ 1 βminus βplus)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t)
    {A : Set ℂ} (hA : IsOpen A)
    (hAsub : closure A ⊆ ball (0 : ℂ) 1 \ {z})
    {x : ℂ} (hx : x ∈ A ∩ cluster μ 1 z t)
    (ℱ : Filtration ℕ (inferInstance : MeasurableSpace (ContinuousPath ℂ)))
    (hsub : Submartingale (fun (n : ℕ) (ω : ContinuousPath ℂ) =>
      (closure A).indicator (fun y => max 0 (odometer μ 1 z t y))
        (ω (ContinuousPath.exitTimeTrunc
          (connectedComponentIn (A ∩ cluster μ 1 z t) x) n ω))) ℱ (planarBrownianMotion x)) :
    odometerExt μ z t x ≤
      (⨆ y ∈ frontier A ∩ closure (connectedComponentIn (A ∩ cluster μ 1 z t) x),
        odometerExt μ z t y) *
        planarBrownianMotion x {ω | ContinuousPath.exitTime A ω ≤
          hittingTime (A \ connectedComponentIn (A ∩ cluster μ 1 z t) x) ω} := by
  classical
  have hAb : Bornology.IsBounded A :=
    isBounded_ball.subset (subset_closure.trans (hAsub.trans sdiff_subset))
  let Y := connectedComponentIn (A ∩ cluster μ 1 z t) x
  let q := (closure A).indicator (fun y => max 0 (odometer μ 1 z t y))
  have hωcluster := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ zero_lt_one hV hz ht).1
  have hYopen : IsOpen Y := (hA.inter hωcluster).connectedComponentIn
  have hYsub : Y ⊆ A ∩ cluster μ 1 z t := connectedComponentIn_subset _ _
  have hxY : x ∈ Y := mem_connectedComponentIn hx
  have hYcomp : ∀ y ∈ Y, connectedComponentIn (A ∩ cluster μ 1 z t) y ⊆ Y := by
    intro y hy
    exact (connectedComponentIn_eq hy).symm.subset
  have hdis : Disjoint (frontier Y) (A ∩ cluster μ 1 z t) :=
    frontier_union_components_disjoint (hA.inter hωcluster) hYsub hYcomp
  have hc := (odometer_continuousOn_and_subharmonic hμ zero_lt_one hV hz ht).1.mono hAsub
  have hqc : ContinuousOn q (closure A) := by
    apply hc.congr
    intro y hy
    have hyunit := hAsub hy
    have hnonneg := odometer_nonneg (μ := μ) ht.le (ball_subset_closedBall hyunit.1) hyunit.2
    simp [q, hy, max_eq_right hnonneg]
  have hqzero : ∀ y ∉ closure A, q y = 0 := by intro y hy; simp [q, hy]
  have hqmeas : Measurable q := measurable_of_continuousOn_closure_of_zero hqc hqzero
  have hqnonneg : ∀ y, 0 ≤ q y := by
    intro y
    by_cases hy : y ∈ closure A
    · simp only [q, indicator_of_mem hy]; exact le_max_left _ _
    · simp [q, hy]
  obtain ⟨M, hM⟩ := hAb.isCompact_closure.exists_bound_of_continuousOn hqc
  have hM' : ∀ y, ‖q y‖ ≤ max M 0 := by
    intro y
    by_cases hy : y ∈ closure A
    · exact (hM y hy).trans (le_max_left _ _)
    · rw [hqzero y hy, norm_zero]; exact le_max_right _ _
  have hzero : ∀ y ∈ A ∩ frontier Y, q y = 0 := by
    intro y hy
    have hyoutside : y ∉ cluster μ 1 z t := by
      intro hycluster
      exact disjoint_left.mp hdis hy.2 ⟨hy.1, hycluster⟩
    have hyunit := hAsub (subset_closure hy.1)
    have hyz : y ≠ z := by simpa using hyunit.2
    have hnonneg := odometer_nonneg (μ := μ) ht.le (ball_subset_closedBall hyunit.1) hyunit.2
    have hnonpos : odometer μ 1 z t y ≤ 0 := by
      apply le_of_not_gt
      intro hpos
      exact hyoutside (mem_cluster_iff.mpr ⟨hyunit.1, Or.inr hpos⟩)
    have hz' : odometer μ 1 z t y = 0 := le_antisymm hnonpos hnonneg
    simp [q, subset_closure hy.1, hz']
  have hbound : ∀ y ∈ frontier A ∩ closure Y,
      ENNReal.ofReal (q y) ≤ ⨆ y ∈ frontier A ∩ closure Y, odometerExt μ z t y := by
    intro y hy
    have hycl := frontier_subset_closure hy.1
    have hyunit := hAsub hycl
    have hyz : y ≠ z := by simpa using hyunit.2
    have hnonneg := odometer_nonneg (μ := μ) ht.le (ball_subset_closedBall hyunit.1) hyunit.2
    have heq : ENNReal.ofReal (q y) = odometerExt μ z t y := by
      simp [q, hycl, max_eq_right hnonneg, odometerExt, hyz]
    rw [heq]
    exact le_iSup₂_of_le y hy le_rfl
  have hxunit := hAsub (subset_closure hx.1)
  have hxz : x ≠ z := by simpa using hxunit.2
  have hxnonneg := odometer_nonneg (μ := μ) ht.le (ball_subset_closedBall hxunit.1) hxunit.2
  have hxq : ENNReal.ofReal (q x) = odometerExt μ z t x := by
    simp [q, subset_closure hx.1, max_eq_right hxnonneg, odometerExt, hxz]
  rw [← hxq]
  exact ofReal_le_boundary_mul_harmonicMeasure_of_submartingale hA hYopen hAb
    (hYsub.trans inter_subset_left) hqmeas hqnonneg hM' hzero hbound hxY ℱ hsub

end HarmonicBalls.Section6
