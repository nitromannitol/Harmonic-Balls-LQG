import HarmonicBalls.Proofs.Sec5.JointTimeMeasurableDecoder
import HarmonicBalls.Proofs.Sec5.QuasiInvariantTimeContinuity
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-! # Countable tests for right discontinuity -/

namespace HarmonicBalls

open MeasureTheory Metric Set TopologicalSpace Filter
open scoped Pointwise

/-- Right discontinuity of an increasing bounded open family is equivalent to
countable tests for future dense points separated from all present dense points. -/
theorem not_right_continuous_iff_dense_tests
    {F : ℝ → Set ℂ} {t : ℝ} (ht : 0 < t)
    (hopen : ∀ s, 0 < s → IsOpen (F s))
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s')
    (hbound : ∀ s, 0 < s → F s ⊆ ball (0 : ℂ) 1) :
    (¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc t (t + δ), closure (F s) ⊆ F t + ball (0 : ℂ) ε) ↔
    ∃ k : ℕ, ∀ n : ℕ, ∃ i : ℕ,
      denseSeq ℂ i ∈ F (t + (2 : ℝ)⁻¹ ^ n) ∧
      ∀ j : ℕ, denseSeq ℂ j ∈ F t →
        1 / ((k : ℝ) + 1) ≤ dist (denseSeq ℂ i) (denseSeq ℂ j) := by
  classical
  constructor
  · intro hfail
    have hnot : ¬ (⋂ n : ℕ, closure (F (t + (2 : ℝ)⁻¹ ^ n))) ⊆ closure (F t) := by
      intro hsub
      exact hfail ((closure_dyadic_iInter_subset_iff_right_continuous ht hmono hbound).mp hsub)
    obtain ⟨x, hx, hxt⟩ := Set.not_subset.mp hnot
    rw [Metric.mem_closure_iff] at hxt
    push Not at hxt
    obtain ⟨ε, hε, hsep⟩ := hxt
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (show 0 < ε / 4 by positivity)
    refine ⟨k, ?_⟩
    intro n
    have hfut : x ∈ closure (F (t + (2 : ℝ)⁻¹ ^ n)) := Set.mem_iInter.mp hx n
    obtain ⟨i, hi, hxi⟩ := (mem_closure_iff_denseSeq (hopen _ (by positivity)) x).mp hfut k
    refine ⟨i, hi, ?_⟩
    intro j hj
    have hxy := hsep (denseSeq ℂ j) hj
    have htri := dist_triangle x (denseSeq ℂ i) (denseSeq ℂ j)
    linarith
  · rintro ⟨k, htest⟩ hcont
    let r : ℝ := 1 / ((k : ℝ) + 1)
    have hr : 0 < r := by dsimp [r]; positivity
    obtain ⟨δ, hδ, hδsub⟩ := hcont (r / 4) (by positivity)
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hδ (by norm_num : (2 : ℝ)⁻¹ < 1)
    obtain ⟨i, hi, hdist⟩ := htest n
    have hi' : denseSeq ℂ i ∈ closure (F (t + (2 : ℝ)⁻¹ ^ n)) := subset_closure hi
    have hi'' := hδsub (t + (2 : ℝ)⁻¹ ^ n)
      ⟨le_add_of_nonneg_right (by positivity), by linarith⟩ hi'
    obtain ⟨y, hy, w, hw, hi_eq⟩ := hi''
    have hiy : dist (denseSeq ℂ i) y < r / 4 := by
      rw [← hi_eq]
      simpa [mem_ball, dist_eq_norm] using hw
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (show 0 < r / 4 by positivity)
    obtain ⟨j, hj, hyj⟩ := (mem_closure_iff_denseSeq (hopen t ht) y).mp (subset_closure hy) m
    have htri := dist_triangle (denseSeq ℂ i) y (denseSeq ℂ j)
    have hseparate : r ≤ dist (denseSeq ℂ i) (denseSeq ℂ j) := hdist j hj
    linarith

/-- A Borel event represents right discontinuity jointly in measure and time
for locally finite measures satisfying volume growth. -/
theorem exists_measurableSet_right_discontinuity_joint_time_of_volumeGrowth
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ∃ E : Set (Measure ℂ × ℝ), MeasurableSet E ∧ ∀ ν : Measure ℂ,
      IsLocallyFiniteMeasure ν → (∃ βminus βplus, VolumeGrowth ν 1 βminus βplus) →
      ∀ t : ℝ, 0 < t → ((ν, t) ∈ E ↔
        ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
          ∀ s ∈ Icc t (t + δ), closure (cluster ν 1 z s) ⊆
            cluster ν 1 z t + ball (0 : ℂ) ε) := by
  classical
  obtain ⟨F, hF, hcorrect⟩ :=
    exists_measurable_cluster_joint_time_of_volumeGrowth (R := 1) zero_lt_one hz
  let E : Set (Measure ℂ × ℝ) := {p | 0 < p.2 ∧ ∃ k : ℕ, ∀ n : ℕ, ∃ i : ℕ,
    denseSeq ℂ i ∈ F (p.1, p.2 + (2 : ℝ)⁻¹ ^ n) ∧
    ∀ j : ℕ, denseSeq ℂ j ∈ F p →
      1 / ((k : ℝ) + 1) ≤ dist (denseSeq ℂ i) (denseSeq ℂ j)}
  have hE : MeasurableSet E := by
    apply Measurable.setOf
    apply (measurable_const.lt measurable_snd).and
    apply Measurable.exists
    intro k
    apply Measurable.forall
    intro n
    apply Measurable.exists
    intro i
    apply Measurable.and
    · exact (measurable_pi_apply (denseSeq ℂ i)).comp
        (hF.comp (measurable_fst.prodMk (measurable_snd.add_const _)))
    · apply Measurable.forall
      intro j
      exact ((measurable_pi_apply (denseSeq ℂ j)).comp hF).imp measurable_const
  refine ⟨E, hE, ?_⟩
  intro ν hloc hvol t ht
  obtain ⟨βminus, βplus, hv⟩ := hvol
  have hopen : ∀ s, 0 < s → IsOpen (cluster ν 1 z s) := by
    intro s hs
    rw [(obstacleCompatibilityShiftStep_holds ν hloc 1 βminus βplus zero_lt_one hv z hz s hs).2.2.1]
    exact isOpen_nonCoincidenceSet_of obstacleLeastSuperharmonicMajorantGeneral_holds
      hloc zero_lt_one hv hz hs
  have hmono : ∀ s s', 0 < s → s ≤ s' → cluster ν 1 z s ⊆ cluster ν 1 z s' := by
    intro s s' hs hss'
    exact cluster_subset_of_general obstacleMonotoneGeneral_holds
      obstacleCompatibilityShiftStep_holds hloc zero_lt_one hv hz hs hss'
  have htest := not_right_continuous_iff_dense_tests ht hopen hmono (fun _ _ => cluster_subset_ball)
  change (0 < t ∧ ∃ k : ℕ, ∀ n : ℕ, ∃ i : ℕ,
    denseSeq ℂ i ∈ F (ν, t + (2 : ℝ)⁻¹ ^ n) ∧
    ∀ j : ℕ, denseSeq ℂ j ∈ F (ν, t) →
      1 / ((k : ℝ) + 1) ≤ dist (denseSeq ℂ i) (denseSeq ℂ j)) ↔ _
  have hfuture : ∀ n : ℕ, F (ν, t + (2 : ℝ)⁻¹ ^ n) =
      cluster ν 1 z (t + (2 : ℝ)⁻¹ ^ n) := fun n =>
    hcorrect ν hloc ⟨βminus, βplus, hv⟩ _ (by positivity)
  simp only [ht, true_and, hcorrect ν hloc ⟨βminus, βplus, hv⟩ t ht, hfuture]
  exact htest.symm

/-- For a measurable random measure supported on locally finite volume-growth
measures, quasi-invariance and covariance imply right continuity at every
fixed positive time. The covariance and quasi-invariance premises remain
explicit. -/
theorem ae_cluster_right_continuous_at_fixed_time_of_quasiInvariant_scaling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : Measurable μ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1)
    (hgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) 1 βminus βplus)
    (T : ℝ → Ω → Ω)
    (hquasi : ∀ c : ℝ, 0 < c → Measure.QuasiMeasurePreserving (T c) P P)
    (hscale : ∀ c : ℝ, 0 < c → ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
      cluster (μ (T c ω)) 1 z (c * s) = cluster (μ ω) 1 z s)
    {t : ℝ} (ht : 0 < t) : ∀ᵐ ω ∂P,
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc t (t + δ), closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  obtain ⟨A, hA, hAeq⟩ := exists_measurableSet_right_discontinuity_joint_time_of_volumeGrowth hz
  let E : Set (Ω × ℝ) := {p | 0 < p.2 ∧ (μ p.1, p.2) ∈ A}
  have hE : MeasurableSet E := (measurableSet_lt measurable_const measurable_snd).inter
    (hA.preimage ((hμ.comp measurable_fst).prodMk measurable_snd))
  have hcount : ∀ᵐ ω ∂P, {s : ℝ | (ω, s) ∈ E}.Countable := by
    filter_upwards [hgood] with ω hω
    obtain ⟨hloc, βminus, βplus, hv⟩ := hω
    have hm : ∀ s s', 0 < s → s ≤ s' → cluster (μ ω) 1 z s ⊆ cluster (μ ω) 1 z s' := by
      intro s s' hs hss'
      exact cluster_subset_of_general obstacleMonotoneGeneral_holds
        obstacleCompatibilityShiftStep_holds hloc zero_lt_one hv hz hs hss'
    apply (countable_not_rightContinuous_of_monotone hm (fun _ _ => cluster_subset_ball)).mono
    intro s hs
    exact ⟨hs.1, (hAeq (μ ω) hloc ⟨βminus, βplus, hv⟩ s hs.1).mp hs.2⟩
  have htransport : ∀ c : ℝ, 0 < c → ∀ᵐ ω ∂P, ∀ s : ℝ,
      (ω, s) ∈ E → (T c ω, c * s) ∈ E := by
    intro c hc
    filter_upwards [hgood, (hquasi c hc).ae hgood, hscale c hc] with ω hω hTω hsc s hs
    have hspos : 0 < s := hs.1
    have hcsp : 0 < c * s := mul_pos hc hspos
    have hbad := (hAeq (μ ω) hω.1 hω.2 s hspos).mp hs.2
    refine ⟨hcsp, (hAeq (μ (T c ω)) hTω.1 hTω.2 (c * s) hcsp).mpr ?_⟩
    intro hcont
    exact hbad (right_continuity_of_time_rescaling hc hspos hsc hcont)
  have h := ae_not_mem_of_countable_time_sections_and_quasiInvariant_scaling
    P E hE hcount T hquasi htransport ht
  filter_upwards [hgood, h] with ω hω hωnot
  by_contra hfail
  exact hωnot ⟨ht, (hAeq (μ ω) hω.1 hω.2 t ht).mpr hfail⟩

/-- The fixed-time criterion also applies to almost-everywhere measurable
random measures, as supplied by the LQG measure construction. -/
theorem ae_cluster_right_continuous_at_fixed_time_of_aemeasurable_quasiInvariant_scaling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1)
    (hgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) 1 βminus βplus)
    (T : ℝ → Ω → Ω)
    (hquasi : ∀ c : ℝ, 0 < c → Measure.QuasiMeasurePreserving (T c) P P)
    (hscale : ∀ c : ℝ, 0 < c → ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
      cluster (μ (T c ω)) 1 z (c * s) = cluster (μ ω) 1 z s)
    {t : ℝ} (ht : 0 < t) : ∀ᵐ ω ∂P,
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc t (t + δ), closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  let ν := hμ.mk μ
  have hνgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) ∧
      ∃ βminus βplus, VolumeGrowth (ν ω) 1 βminus βplus := by
    filter_upwards [hgood, hμ.ae_eq_mk] with ω hg he
    simpa only [ν, ← he] using hg
  have hνscale : ∀ c : ℝ, 0 < c → ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
      cluster (ν (T c ω)) 1 z (c * s) = cluster (ν ω) 1 z s := by
    intro c hc
    filter_upwards [hμ.ae_eq_mk, (hquasi c hc).ae hμ.ae_eq_mk, hscale c hc] with ω he heT hs
    intro s hspos
    simpa only [ν, ← he, ← heT] using hs s hspos
  have h := ae_cluster_right_continuous_at_fixed_time_of_quasiInvariant_scaling
    P ν hμ.measurable_mk hz hνgood T hquasi hνscale ht
  filter_upwards [hμ.ae_eq_mk, h] with ω he hω
  simpa only [ν, ← he] using hω

universe u

/-- For an LQG measure, volume growth and measurability discharge the random
measure premises of the fixed-time criterion. The time-scaling covariance and
quasi-invariance assumptions are stated separately. -/
theorem ae_lqg_cluster_right_continuous_at_fixed_time_of_quasiInvariant_scaling
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1)
    (T : ℝ → Ω → Ω)
    (hquasi : ∀ c : ℝ, 0 < c → Measure.QuasiMeasurePreserving (T c) P P)
    (hscale : ∀ c : ℝ, 0 < c → ∀ᵐ ω ∂P, ∀ s : ℝ, 0 < s →
      cluster (μ (T c ω)) 1 z (c * s) = cluster (μ ω) 1 z s)
    {t : ℝ} (ht : 0 < t) : ∀ᵐ ω ∂P,
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc t (t + δ), closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  obtain ⟨βm, βp, hvol⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) 1 βminus βplus := by
    filter_upwards [hvol] with ω hω
    exact ⟨hω.1, βm, βp, hω.2 1 zero_lt_one⟩
  exact ae_cluster_right_continuous_at_fixed_time_of_aemeasurable_quasiInvariant_scaling
    P μ (hGFF.aemeasurable_lqgMeasure hμ) hz hgood T hquasi hscale ht

end HarmonicBalls
