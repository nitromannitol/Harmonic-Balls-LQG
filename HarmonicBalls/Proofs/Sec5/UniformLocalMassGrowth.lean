import HarmonicBalls.Proofs.Sec5.LocalMassGrowth
import HarmonicBalls.Proofs.Sec5.CountableTimeMeasurability

/-! # Uniform local mass growth in time -/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian Section6 Filter
open scoped Topology ENNReal

/-- One constant works at every positive time when the test-function domain is
disjoint from the current cluster. -/
theorem cluster_test_mass_le_time_increment_uniform
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R)
    {U : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) (hφ0 : 0 ≤ φ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      Disjoint U (cluster μ R z t) → ∀ s : ℝ, t ≤ s →
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
  intro t ht hdis s hts
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


/-- On a fixed closed ball, the linear growth constant is independent of the
initial time while the surrounding region stays disjoint from the cluster. -/
theorem cluster_closedBall_mass_le_time_increment_uniform
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R)
    {U : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    {w : ℂ} {ρ : ℝ}
    (hρ : 0 < ρ) (hball : closedBall w (2 * ρ) ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      Disjoint U (cluster μ R z t) → ∀ s : ℝ, t ≤ s →
      μ (closedBall w ρ ∩ cluster μ R z s) ≤ ENNReal.ofReal (C * (s - t)) := by
  let : IsLocallyFiniteMeasure μ := hμ
  let φ : ContDiffBump w := ⟨ρ, 2 * ρ, hρ, by linarith⟩
  have hφ : IsTestFunction U φ := by
    refine ⟨φ.contDiff, φ.hasCompactSupport, ?_⟩
    rw [φ.tsupport_eq]
    exact hball
  have hφ0 : 0 ≤ (φ : ℂ → ℝ) := fun _ => φ.nonneg
  obtain ⟨C, hC, hbound⟩ := cluster_test_mass_le_time_increment_uniform hμ hR hV hz
    hU hUsub hφ hφ0
  refine ⟨C, hC, ?_⟩
  intro t ht hdis s hs
  let ν := μ.restrict (U ∩ cluster μ R z s)
  have hi : Integrable (φ : ℂ → ℝ) ν :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).mono_measure Measure.restrict_le_self
  have hballsub : closedBall w ρ ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hball
  have hmeasure := measure_le_ofReal_integral (σ := ν) measurableSet_closedBall hi hφ0
    (fun x hx => by rw [φ.one_of_mem_closedBall hx])
  have heq : ν (closedBall w ρ) = μ (closedBall w ρ ∩ cluster μ R z s) := by
    rw [show ν = μ.restrict (U ∩ cluster μ R z s) from rfl,
      Measure.restrict_apply measurableSet_closedBall]
    congr 1
    ext x
    simp only [mem_inter_iff]
    constructor
    · rintro ⟨hx, _, hxs⟩
      exact ⟨hx, hxs⟩
    · rintro ⟨hx, hxs⟩
      exact ⟨hx, hballsub hx, hxs⟩
  rw [heq] at hmeasure
  exact hmeasure.trans (ENNReal.ofReal_le_ofReal (hbound t ht hdis s hs))


/-- Compact subsets of a fixed test region have a common linear growth
constant for all positive starting times at which the region is disjoint. -/
theorem cluster_compact_mass_le_time_increment_uniform
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R)
    {U K : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      Disjoint U (cluster μ R z t) → ∀ s : ℝ, t ≤ s →
      μ (K ∩ cluster μ R z s) ≤ ENNReal.ofReal (C * (s - t)) := by
  classical
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let ρ : ℝ := δ / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hball (x : K) : closedBall (x : ℂ) (2 * ρ) ⊆ U := by
    apply (closedBall_subset_closedBall (show 2 * ρ ≤ δ by dsimp [ρ]; linarith)).trans
    exact (closedBall_subset_cthickening x.property δ).trans hδU
  have hcover : K ⊆ ⋃ x : K, ball (x : ℂ) ρ := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self hρ⟩
  obtain ⟨F, hF⟩ := hK.elim_finite_subcover (fun x : K => ball (x : ℂ) ρ)
    (fun _ => isOpen_ball) hcover
  have hex (x : K) := cluster_closedBall_mass_le_time_increment_uniform hμ hR hV hz
    hU hUsub hρ (hball x)
  let C : K → ℝ := fun x => Classical.choose (hex x)
  have hC (x : K) : 0 ≤ C x := (Classical.choose_spec (hex x)).1
  have hbound (x : K) := (Classical.choose_spec (hex x)).2
  refine ⟨∑ x ∈ F, C x, Finset.sum_nonneg (fun x _ => hC x), ?_⟩
  intro t ht hdis s hs
  have hsub : K ∩ cluster μ R z s ⊆
      ⋃ x ∈ F, (closedBall (x : ℂ) ρ ∩ cluster μ R z s) := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hF hx.1)
    obtain ⟨hiF, hxi⟩ := mem_iUnion.mp hi
    exact mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hiF, ball_subset_closedBall hxi, hx.2⟩⟩
  calc
    μ (K ∩ cluster μ R z s) ≤
        μ (⋃ x ∈ F, (closedBall (x : ℂ) ρ ∩ cluster μ R z s)) := measure_mono hsub
    _ ≤ ∑ x ∈ F, μ (closedBall (x : ℂ) ρ ∩ cluster μ R z s) :=
      measure_biUnion_finset_le F _
    _ ≤ ∑ x ∈ F, ENNReal.ofReal (C x * (s - t)) :=
      Finset.sum_le_sum fun x _ => hbound x t ht hdis s hs
    _ = ENNReal.ofReal ((∑ x ∈ F, C x) * (s - t)) := by
      rw [Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg]
      intro x hx
      exact mul_nonneg (hC x) (sub_nonneg.mpr hs)


/-- If a region was unvisited before a positive time, its compact subsets
acquire at most linear mass after that time. The constant is independent of
the time and applies even when it is the first time of contact. -/
theorem cluster_compact_mass_le_after_no_entry_uniform
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R)
    {U K : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) R \ {z})
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 < t →
      (∀ r ∈ Ioo (0 : ℝ) t, Disjoint U (cluster μ R z r)) →
      ∀ s : ℝ, t ≤ s → μ (K ∩ cluster μ R z s) ≤ ENNReal.ofReal (C * (s - t)) := by
  obtain ⟨C, hC, hb⟩ := cluster_compact_mass_le_time_increment_uniform hμ hR hV hz
    hU hUsub hK hKU
  refine ⟨C, hC, ?_⟩
  intro t ht hbefore s hs
  have hdis : Disjoint U (cluster μ R z t) := by
    apply disjoint_left.mpr
    intro x hx hxcluster
    obtain ⟨q, hq0, hqt, hqx⟩ := mem_cluster_exists_earlier_rat ht hxcluster
    exact disjoint_left.mp (hbefore q ⟨hq0, hqt⟩) hx hqx
  exact hb t ht hdis s hs

end HarmonicBalls
