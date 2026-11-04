import HarmonicBalls.Proofs.Sec5.ClusterLeftContinuity
import HarmonicBalls.Proofs.Sec5.SupersolutionScaling

/-! # Continuity at fixed time under mass scaling

Scaling a measure by a positive constant reparametrizes cluster time. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Pointwise

/-- Rescaling a measure rescales the cluster time, with no spatial dilation. -/
theorem cluster_smul_measure {μ : Measure ℂ} {R t c : ℝ} {z : ℂ}
    (hc : 0 < c) (ht : 0 ≤ t) :
    cluster (ENNReal.ofReal c • μ) R z t = cluster μ R z (c⁻¹ * t) := by
  have h := cluster_scaled_measure (μ := μ) (R := R) (z := z)
    (k := 1) (c := c) (t := t) zero_lt_one hc ht
  simp only [inv_one, one_smul, one_mul] at h
  change cluster (ENNReal.ofReal c • Measure.map id μ) R z t =
    cluster μ R z (c⁻¹ * t) at h
  simpa only [Measure.map_id] using h

/-- A positive linear reparametrization preserves right continuity. -/
theorem right_continuous_cluster_smul_measure
    {μ : Measure ℂ} {R t c : ℝ} {z : ℂ} (hc : 0 < c) (ht : 0 < t)
    (hcont : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc (c⁻¹ * t) (c⁻¹ * t + δ),
        closure (cluster μ R z s) ⊆ cluster μ R z (c⁻¹ * t) + ball (0 : ℂ) ε) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
      closure (cluster (ENNReal.ofReal c • μ) R z s) ⊆
        cluster (ENNReal.ofReal c • μ) R z t + ball (0 : ℂ) ε := by
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hcont ε hε
  refine ⟨c * δ, mul_pos hc hδ, ?_⟩
  intro s hs
  rw [cluster_smul_measure hc (le_of_lt ht),
    cluster_smul_measure hc (le_of_lt (lt_of_lt_of_le ht hs.1))]
  apply hbound
  constructor
  · exact mul_le_mul_of_nonneg_left hs.1 (inv_nonneg.mpr hc.le)
  · have h := mul_le_mul_of_nonneg_left hs.2 (inv_nonneg.mpr hc.le)
    simpa only [mul_add, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul] using h

/-- For a fixed centre and time, at most countably many positive scalings of a
measure can produce a right-continuity failure, provided the original cluster
family is monotone. -/
theorem countable_bad_mass_scalings
    {μ : Measure ℂ} {t : ℝ} {z : ℂ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ 1 z s ⊆ cluster μ 1 z s') :
    {c : ℝ | 0 < c ∧ ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ s ∈ Icc t (t + δ), closure (cluster (ENNReal.ofReal c • μ) 1 z s) ⊆
        cluster (ENNReal.ofReal c • μ) 1 z t + ball (0 : ℂ) ε}.Countable := by
  let E : Set ℝ := {s : ℝ | 0 < s ∧ ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ s' ∈ Icc s (s + δ), closure (cluster μ 1 z s') ⊆ cluster μ 1 z s + ball (0 : ℂ) ε}
  have hE : E.Countable := countable_not_rightContinuous_of_monotone hmono
    (fun _ _ => cluster_subset_ball)
  let B : Set ℝ := {c : ℝ | 0 < c ∧ ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
    ∀ s ∈ Icc t (t + δ), closure (cluster (ENNReal.ofReal c • μ) 1 z s) ⊆
      cluster (ENNReal.ofReal c • μ) 1 z t + ball (0 : ℂ) ε}
  change B.Countable
  apply (show MapsTo (fun c : ℝ => c⁻¹ * t) B E from ?_).countable_of_injOn ?_ hE
  · intro c hc
    refine ⟨mul_pos (inv_pos.mpr hc.1) ht, ?_⟩
    intro hcont
    exact hc.2 (right_continuous_cluster_smul_measure hc.1 ht hcont)
  · intro a ha b hb hab
    have h := mul_right_cancel₀ ht.ne' hab
    exact inv_injective h

/-- A generic positive mass scaling gives right continuity at any prescribed
countable collection of centres and positive times. -/
theorem ae_mass_scaling_right_continuous_at_countably_many_times
    {ι κ : Type*} [Countable ι] [Countable κ]
    (μ : Measure ℂ) (centres : ι → ℂ) (times : κ → ℝ)
    (ht : ∀ j, 0 < times j)
    (hmono : ∀ i s s', 0 < s → s ≤ s' →
      cluster μ 1 (centres i) s ⊆ cluster μ 1 (centres i) s') :
    ∀ᵐ c ∂(volume : Measure ℝ), 0 < c → ∀ i j ε, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc (times j) (times j + δ),
        closure (cluster (ENNReal.ofReal c • μ) 1 (centres i) s) ⊆
          cluster (ENNReal.ofReal c • μ) 1 (centres i) (times j) + ball (0 : ℂ) ε := by
  have hbad : ∀ i j, ∀ᵐ c ∂(volume : Measure ℝ),
      c ∉ {c : ℝ | 0 < c ∧ ¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc (times j) (times j + δ),
          closure (cluster (ENNReal.ofReal c • μ) 1 (centres i) s) ⊆
            cluster (ENNReal.ofReal c • μ) 1 (centres i) (times j) + ball (0 : ℂ) ε} :=
    fun i j => (countable_bad_mass_scalings (ht j) (hmono i)).ae_notMem volume
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hbad i))] with c hc
  intro hcpos i j
  by_contra h
  exact hc i j ⟨hcpos, h⟩

universe u

/-- For an LQG measure satisfying I2, almost every mass scaling gives right
continuity simultaneously at prescribed countably many centres and times. -/
theorem ae_lqg_mass_scaling_right_continuous_at_countably_many_times
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    {ι κ : Type*} [Countable ι] [Countable κ]
    (centres : ι → ball (0 : ℂ) 1) (times : κ → ℝ) (ht : ∀ j, 0 < times j)
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ᵐ c ∂(volume : Measure ℝ), 0 < c → ∀ i j ε, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc (times j) (times j + δ),
        closure (cluster (ENNReal.ofReal c • μ ω) 1 (centres i) s) ⊆
          cluster (ENNReal.ofReal c • μ ω) 1 (centres i) (times j) + ball (0 : ℂ) ε := by
  filter_upwards [clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hmono
  apply ae_mass_scaling_right_continuous_at_countably_many_times
    (μ ω) (fun i => (centres i : ℂ)) times ht
  intro i s s' hs hss'
  exact hmono s s' 1 hs hss' zero_lt_one (centres i) (centres i).property

end HarmonicBalls

