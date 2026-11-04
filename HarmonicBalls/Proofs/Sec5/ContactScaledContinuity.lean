import HarmonicBalls.Proofs.Sec5.ContactDiscComparison
import HarmonicBalls.Proofs.Sec5.ClusterLeftContinuity
import HarmonicBalls.Steps.Sec5.CompactContinuity
import HarmonicBalls.Proofs.Sec5.SupersolutionScaling
import HarmonicBalls.Proofs.Sec5.ScalingMeasure

/-! # Right continuity at first contact via a larger disc

A compact cluster in a larger disc can be rescaled to use unit-disc compact
right continuity. The field invariance and LQG coordinate change are explicit
inputs pending source checking.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise ENNReal Topology

universe u

/-- A pathwise scaling identity transports compact right continuity from the
unit disc to a larger disc, with its mass parameter rescaled. -/
theorem cluster_compact_right_continuity_of_scale
    {μ ν : Measure ℂ} {k A t : ℝ} {z : ℂ} (hk : 0 < k) (hA : 0 < A) (ht : 0 < t)
    (hscale : ∀ s : ℝ, 0 < s → cluster ν 1 (k⁻¹ • z) s =
      k⁻¹ • cluster μ k z (A * s))
    (hunit : closure (cluster ν 1 (k⁻¹ • z) (t / A)) ⊆ ball 0 1 →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc (t / A) (t / A + δ),
        closure (cluster ν 1 (k⁻¹ • z) s) ⊆
          cluster ν 1 (k⁻¹ • z) (t / A) + ball (0 : ℂ) ε)
    (hcompact : closure (cluster μ k z t) ⊆ ball 0 k) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (cluster μ k z s) ⊆ cluster μ k z t + ball (0 : ℂ) ε := by
  have hmul : A * (t / A) = t := by field_simp
  have heq := hscale (t / A) (div_pos ht hA)
  rw [hmul] at heq
  have hball : (k⁻¹ : ℝ) • ball (0 : ℂ) k = ball 0 1 := by
    rw [_root_.smul_ball (inv_ne_zero hk.ne')]
    simp [Real.norm_eq_abs, abs_of_pos hk, hk.ne']
  have hcompact' : closure (cluster ν 1 (k⁻¹ • z) (t / A)) ⊆ ball 0 1 := by
    rw [heq, closure_smul₀' (inv_ne_zero hk.ne'), ← hball]
    exact smul_set_mono hcompact
  intro ε hε
  obtain ⟨d, hd, hbound⟩ := hunit hcompact' (ε / k) (div_pos hε hk)
  refine ⟨A * d, mul_pos hA hd, ?_⟩
  intro s hs x hx
  have hspos : 0 < s := ht.trans_le hs.1
  have hsdiv : s / A ∈ Icc (t / A) (t / A + d) := by
    constructor
    · exact div_le_div_of_nonneg_right hs.1 hA.le
    · apply (div_le_iff₀ hA).2
      calc
        s ≤ t + A * d := hs.2
        _ = (t / A + d) * A := by field_simp
  have hes := hscale (s / A) (div_pos hspos hA)
  have hsMul : A * (s / A) = s := by field_simp
  rw [hsMul] at hes
  have hx' : k⁻¹ • x ∈ closure (cluster ν 1 (k⁻¹ • z) (s / A)) := by
    rw [hes, closure_smul₀' (inv_ne_zero hk.ne')]
    exact smul_mem_smul_set hx
  obtain ⟨y, hy, w, hw, hsum⟩ := hbound (s / A) hsdiv hx'
  have hy' : k • y ∈ cluster μ k z t := by
    rw [heq] at hy
    obtain ⟨v, hv, rfl⟩ := hy
    simpa [smul_smul, hk.ne'] using hv
  have hw' : k • w ∈ ball (0 : ℂ) ε := by
    rw [mem_ball_zero_iff] at hw ⊢
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk]
    have : k * (ε / k) = ε := by field_simp
    nlinarith
  refine ⟨k • y, hy', k • w, hw', ?_⟩
  have h := congrArg (fun a : ℂ => k • a) hsum
  simpa [smul_add, smul_smul, hk.ne'] using h

/-- At first boundary contact, the unit-disc cluster is right-continuous.
The affine invariance and coordinate-change inputs are explicit and are
pending source review. -/
theorem ae_cluster_right_continuity_at_first_contact
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      (∀ s ∈ Ioo (0 : ℝ) t, closure (cluster (μ ω) 1 z s) ⊆ ball 0 1) →
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  let hC' := affinePairing hC hcirc (2 : ℂ) 0
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
    hcirc ω (2 * r) ((2 : ℝ) • z) - hcirc ω 2 0
  have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
    have hcirc_eq : hcirc' = affineCircle hcirc (2 : ℂ) 0 := by
      funext ω r z
      simp [hcirc', affineCircle, Complex.real_smul]
    rw [hcirc_eq]
    exact hAff hGFF (2 : ℂ) (by norm_num) 0
  have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) := by
    exact isLQGMeasureOfField_normalizedPullback hCC hGFF hγ hγ2 hα hμ (by norm_num)
  have hcompact := clusterCompactRightContinuity_of_steps (clusterMonotone_proved hI2) h72
    γ α₀ hγ hγ2 hα Ω P hC' hcirc'
    (fun ω => normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) hGFF' hμ'
  have hscale := clusterPathwiseScaleStep_proved γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
    2 (by norm_num)
  filter_upwards [hcompact, hscale,
    ae_cluster_eq_larger_disc_at_first_contact hI2 hγ hγ2 hα hGFF hμ (R := 2) (by norm_num)]
    with ω hunit hsc heq
  intro z hz t ht hbefore
  have hz' : ((2 : ℝ)⁻¹ • z) ∈ ball (0 : ℂ) (1 / 2) := by
    rw [mem_ball_zero_iff] at hz ⊢
    rw [norm_smul, Real.norm_eq_abs]
    norm_num at *
    linarith
  have hz1 : ((2 : ℝ)⁻¹ • z) ∈ ball (0 : ℂ) 1 :=
    ball_subset_ball (by norm_num : (1 : ℝ) / 2 ≤ 1) hz'
  let A := Real.exp (γ * (lqgQ γ * Real.log 2 + fieldCircleAverage α₀ (hcirc ω) 2 0))
  have hA : 0 < A := Real.exp_pos _
  have hsc' : ∀ s : ℝ, 0 < s →
      cluster (normalizedPullbackMeasure γ α₀ 2 (hcirc ω) (μ ω)) 1 ((2 : ℝ)⁻¹ • z) s =
        (2 : ℝ)⁻¹ • cluster (μ ω) 2 z (A * s) := by
    intro s hs
    simpa [A, smul_smul] using hsc ((2 : ℝ)⁻¹ • z) hz1 s hs
  have hclusters := heq z hz t ht hbefore
  have hcontained := cluster_closure_subset_larger_disc_of_eq (by norm_num : (1 : ℝ) < 2) hclusters
  have hright := cluster_compact_right_continuity_of_scale (by norm_num : (0 : ℝ) < 2)
    hA ht hsc' (hunit ((2 : ℝ)⁻¹ • z) hz' (t / A) (div_pos ht hA)) hcontained
  exact cluster_right_continuity_of_larger_disc (by norm_num : (1 : ℝ) < 2)
    hz ht.le hclusters hright

/-- The cluster is Hausdorff-continuous at first boundary contact, under the
same explicit inputs as the one-sided result. -/
theorem ae_cluster_hausdorff_continuity_at_first_contact
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      (∀ s ∈ Ioo (0 : ℝ) t, closure (cluster (μ ω) 1 z s) ⊆ ball 0 1) →
      ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ s in 𝓝[Ioi (0 : ℝ)] t,
        hausdorffEDist (cluster (μ ω) 1 z s) (cluster (μ ω) 1 z t) < ε := by
  filter_upwards [ae_cluster_right_continuity_at_first_contact hI2 h72 hAff hCC
    hγ hγ2 hα hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hright hmono
  intro z hz t ht hbefore
  exact cluster_hausdorffContinuousWithinAt_of_right_continuity ht
    (fun s s' hs hss => hmono s s' 1 hs hss (by norm_num) z hz)
    (hright z hz t ht hbefore)

end HarmonicBalls
