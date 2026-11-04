import HarmonicBalls.Proofs.Sec5.OdometerTimeContinuity
import HarmonicBalls.Proofs.Sec6.TruncatedOdometerDomination
import Mathlib.MeasureTheory.Measure.Support

/-! # Local mass growth away from an existing cluster

Riesz domination and time stability of the odometer bound the mass of a
later cluster against a test function supported away from the earlier one.
The estimate remains valid after the cluster reaches the disc boundary.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian Section6 Filter
open scoped Topology

/-- A fixed nonnegative test function supported away from the present cluster
sees at most a linear increase of cluster mass in time. -/
theorem cluster_test_mass_le_time_increment
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    (hdis : Disjoint U (cluster μ R z t))
    {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) (hφ0 : 0 ≤ φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, t ≤ s →
      ∫ x, φ x ∂(μ.restrict (U ∩ cluster μ R z s)) ≤ C * (s - t) := by
  classical
  let K := tsupport φ
  have hKR : K ⊆ closedBall (0 : ℂ) R := fun x hx =>
    ball_subset_closedBall (hUsub (hφ.2.2 hx)).1
  have hKz : z ∉ K := fun hzK => (hUsub (hφ.2.2 hzK)).2 (by simp)
  obtain ⟨A, hA, hLip⟩ := odometer_uniform_lipschitz_time_on_compact hμ hR hV hz
    hφ.2.1 hKR hKz
  have hΔi : Integrable (Δ φ) :=
    (continuous_laplacian_of_contDiff (hφ.1.of_le (by norm_cast))).integrable_of_hasCompactSupport
      (hasCompactSupport_laplacian hφ.2.1)
  refine ⟨A * ∫ x, |Δ φ x|, mul_nonneg hA (integral_nonneg fun _ => abs_nonneg _), ?_⟩
  intro s hts
  have hs : 0 < s := ht.trans_le hts
  let Λ := U ∩ cluster μ R z s
  have hge := odometer_indicator_union_components_laplacianGE_restrict hμ hR hV hz hs hU hUsub
    (Λ := Λ) (Subset.rfl) (fun x hx => connectedComponentIn_subset _ _)
  have hint := integrable_mul_laplacian_of_test hge.1 hφ
  have hbound : ∀ x : ℂ, Λ.indicator (odometer μ R z s) x * Δ φ x ≤
      (A * (s - t)) * |Δ φ x| := by
    intro x
    by_cases hx : x ∈ K
    · have hxU := hφ.2.2 hx
      have hxz : x ≠ z := by simpa using (hUsub hxU).2
      have hnot : x ∉ cluster μ R z t := fun h => disjoint_left.mp hdis hxU h
      have hzero : odometer μ R z t x = 0 := by
        have hnonneg := odometer_nonneg (μ := μ) ht.le (hKR hx) hxz
        have hnotpos : ¬ 0 < odometer μ R z t x := fun hp =>
          hnot (mem_cluster_iff.mpr ⟨(hUsub hxU).1, Or.inr hp⟩)
        exact le_antisymm (le_of_not_gt hnotpos) hnonneg
      have hL := hLip x hx t s ht hs
      rw [hzero, sub_zero, abs_of_nonneg (sub_nonneg.mpr hts)] at hL
      have hnonneg := odometer_nonneg (μ := μ) hs.le (hKR hx) hxz
      have hB : |Λ.indicator (odometer μ R z s) x| ≤ A * (s - t) := by
        by_cases hxΛ : x ∈ Λ
        · simpa [hxΛ, abs_of_nonneg hnonneg] using hL
        · simp [hxΛ, mul_nonneg hA (sub_nonneg.mpr hts)]
      calc
        Λ.indicator (odometer μ R z s) x * Δ φ x ≤
            |Λ.indicator (odometer μ R z s) x * Δ φ x| := le_abs_self _
        _ = |Λ.indicator (odometer μ R z s) x| * |Δ φ x| := abs_mul _ _
        _ ≤ (A * (s - t)) * |Δ φ x| :=
          mul_le_mul_of_nonneg_right hB (abs_nonneg _)
    · have hΔzero : Δ φ x = 0 := laplacian_eq_zero_of_notMem_tsupport hx
      simp [hΔzero]
  have h := (hge.2 φ hφ hφ0).2
  calc
    ∫ x, φ x ∂(μ.restrict Λ) ≤ ∫ x, Λ.indicator (odometer μ R z s) x * Δ φ x := h
    _ ≤ ∫ x, (A * (s - t)) * |Δ φ x| := integral_mono hint (hΔi.abs.const_mul _) hbound
    _ = (A * ∫ x, |Δ φ x|) * (s - t) := by rw [integral_const_mul]; ring

/-- Every nonnegative test function supported away from the present cluster
has zero integral over points belonging to every cluster along a sequence of
future times tending to the present time. -/
theorem integral_future_cluster_eq_zero_of_test
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    (hdis : Disjoint U (cluster μ R z t))
    {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) (hφ0 : 0 ≤ φ)
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (ha0 : ∀ n, 0 ≤ a n) :
    ∫ x, φ x ∂(μ.restrict (U ∩ ⋂ n, cluster μ R z (t + a n))) = 0 := by
  let : IsLocallyFiniteMeasure μ := hμ
  obtain ⟨C, hC, hbound⟩ := cluster_test_mass_le_time_increment hμ hR hV hz ht
    hU hUsub hdis hφ hφ0
  let ν := μ.restrict (U ∩ ⋂ n, cluster μ R z (t + a n))
  have hlim : Tendsto (fun n => C * a n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul ha)
  apply le_antisymm
  · apply ge_of_tendsto' hlim
    intro n
    have hle : ν ≤ μ.restrict (U ∩ cluster μ R z (t + a n)) :=
      Measure.restrict_mono_set μ (fun x hx => ⟨hx.1, mem_iInter.mp hx.2 n⟩)
    have hi : Integrable φ (μ.restrict (U ∩ cluster μ R z (t + a n))) :=
      (hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1).mono_measure Measure.restrict_le_self
    calc
      ∫ x, φ x ∂ν ≤ ∫ x, φ x ∂(μ.restrict (U ∩ cluster μ R z (t + a n))) :=
        integral_mono_measure hle (Eventually.of_forall hφ0) hi
      _ ≤ C * ((t + a n) - t) := hbound _ (le_add_of_nonneg_right (ha0 n))
      _ = C * a n := by ring
  · exact integral_nonneg hφ0

/-- No mass can appear immediately in an open region disjoint from the
present cluster and the pole. -/
theorem measure_future_cluster_inter_eq_zero
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    {U : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    (hdis : Disjoint U (cluster μ R z t))
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (ha0 : ∀ n, 0 ≤ a n) :
    μ (U ∩ ⋂ n, cluster μ R z (t + a n)) = 0 := by
  let : IsLocallyFiniteMeasure μ := hμ
  let ν := μ.restrict (U ∩ ⋂ n, cluster μ R z (t + a n))
  have hsupport : U ⊆ ν.supportᶜ := by
    intro x hx hxmem
    obtain ⟨r, hr, hrsub⟩ := Metric.isOpen_iff.mp hU x hx
    obtain ⟨φ, hφ, hφ0, hφx⟩ := IsTestFunction.exists_ne_zero hr hrsub
    have hi : Integrable φ ν :=
      (hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1).mono_measure Measure.restrict_le_self
    have heq : ∫ x, φ x ∂ν = 0 :=
      integral_future_cluster_eq_zero_of_test hμ hR hV hz ht hU hUsub hdis hφ hφ0 ha ha0
    have hae : ∀ᵐ y ∂ν, φ y = 0 := (integral_eq_zero_iff_of_nonneg hφ0 hi).mp heq
    have hclosed : IsClosed {y | φ y = 0} := isClosed_eq hφ.1.continuous continuous_const
    have := Measure.support_subset_of_isClosed hclosed hae hxmem
    simp only [mem_ofPred_eq, hφx, one_ne_zero] at this
  have hnull : ν U = 0 := measure_mono_null hsupport Measure.measure_compl_support
  rw [show ν = μ.restrict (U ∩ ⋂ n, cluster μ R z (t + a n)) from rfl,
    Measure.restrict_apply hU.measurableSet] at hnull
  have hset : U ∩ (U ∩ ⋂ n, cluster μ R z (t + a n)) =
      U ∩ ⋂ n, cluster μ R z (t + a n) := by ext x; simp
  simpa only [hset] using hnull

/-- If the interior boundary of the present cluster has zero mass, then no
positive mass is added at the present time, including after boundary contact. -/
theorem measure_future_cluster_sdiff_eq_zero
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) {t : ℝ} (ht : 0 < t)
    (hboundary : μ (frontier (cluster μ R z t) ∩ ball 0 R) = 0)
    {a : ℕ → ℝ} (ha : Tendsto a atTop (𝓝 0)) (ha0 : ∀ n, 0 ≤ a n) :
    μ ((⋂ n, cluster μ R z (t + a n)) \ cluster μ R z t) = 0 := by
  let A := cluster μ R z t
  let U := ball (0 : ℂ) R \ closure A
  have hAopen : IsOpen A := (cluster_open_laplacian_of_general greenFunctionBall
    obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hR hV hz ht).1
  have hzA : z ∈ A := self_mem_cluster hz
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_closure
  have hUsub : U ⊆ ball (0 : ℂ) R \ {z} := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    intro heq
    have : x = z := by simpa using heq
    exact hx.2 (this ▸ subset_closure hzA)
  have hdis : Disjoint U A := disjoint_left.mpr fun x hx hxA => hx.2 (subset_closure hxA)
  have hzero := measure_future_cluster_inter_eq_zero hμ hR hV hz ht hU hUsub hdis ha ha0
  have hsubset : (⋂ n, cluster μ R z (t + a n)) \ A ⊆
      (U ∩ ⋂ n, cluster μ R z (t + a n)) ∪ (frontier A ∩ ball 0 R) := by
    intro x hx
    have hxball : x ∈ ball (0 : ℂ) R := cluster_subset_ball (mem_iInter.mp hx.1 0)
    by_cases hxcl : x ∈ closure A
    · right
      refine ⟨?_, hxball⟩
      rw [frontier, hAopen.interior_eq]
      exact ⟨hxcl, hx.2⟩
    · left
      exact ⟨⟨hxball, hxcl⟩, hx.1⟩
  exact measure_mono_null hsubset (measure_union_null hzero hboundary)

end HarmonicBalls
