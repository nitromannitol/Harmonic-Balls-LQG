import HarmonicBalls.Proofs.Sec5.ContinuityUnderMassScaling
import HarmonicBalls.Proofs.Sec5.RightDiscontinuityMeasurability
import HarmonicBalls.Proofs.Sec5.GeneralDomainMeasureLocality

/-! # Local mass scaling and fixed-time continuity -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

/-- Multiplying a measure on the disc scales the cluster time, regardless of
how the measure changes outside the disc. -/
theorem cluster_eq_of_restrict_eq_smul
    {μ ν : Measure ℂ} {R c t : ℝ} {z : ℂ}
    (hR : 0 < R) (hc : 0 < c) (ht : 0 ≤ t)
    (hlocal : ν.restrict (ball (0 : ℂ) R) =
      (ENNReal.ofReal c • μ).restrict (ball (0 : ℂ) R)) :
    cluster ν R z (c * t) = cluster μ R z t := by
  have heq := clusterOn_eq_of_restrict_eq measurableSet_ball hlocal z (c * t)
  have heq' : cluster ν R z (c * t) = cluster (ENNReal.ofReal c • μ) R z (c * t) := by
    simpa only [clusterOn_ball ν hR.ne', clusterOn_ball (ENNReal.ofReal c • μ) hR.ne'] using heq
  rw [heq', cluster_smul_measure hc (mul_nonneg hc.le ht), ← mul_assoc,
    inv_mul_cancel₀ hc.ne', one_mul]

/-- A quasi-invariant action that scales a random measure on the unit disc
implies continuity of its cluster at each fixed positive time. -/
theorem ae_cluster_right_continuous_of_quasiInvariant_local_mass_scaling
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1)
    (hgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) 1 βminus βplus)
    (T : ℝ → Ω → Ω)
    (hquasi : ∀ c : ℝ, 0 < c → Measure.QuasiMeasurePreserving (T c) P P)
    (hlocal : ∀ c : ℝ, 0 < c → ∀ᵐ ω ∂P,
      (μ (T c ω)).restrict (ball (0 : ℂ) 1) =
        (ENNReal.ofReal c • μ ω).restrict (ball (0 : ℂ) 1))
    {t : ℝ} (ht : 0 < t) : ∀ᵐ ω ∂P,
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc t (t + δ), closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  apply ae_cluster_right_continuous_at_fixed_time_of_aemeasurable_quasiInvariant_scaling
    P μ hμ hz hgood T hquasi _ ht
  intro c hc
  filter_upwards [hlocal c hc] with ω hω s hs
  exact cluster_eq_of_restrict_eq_smul zero_lt_one hc hs.le hω

universe u

/-- The LQG version requires I2 and a quasi-invariant action on the underlying
probability space which scales the measure on the unit disc. -/
theorem ae_lqg_cluster_right_continuous_of_quasiInvariant_local_mass_scaling
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1)
    (T : ℝ → Ω → Ω)
    (hquasi : ∀ c : ℝ, 0 < c → Measure.QuasiMeasurePreserving (T c) P P)
    (hlocal : ∀ c : ℝ, 0 < c → ∀ᵐ ω ∂P,
      (μ (T c ω)).restrict (ball (0 : ℂ) 1) =
        (ENNReal.ofReal c • μ ω).restrict (ball (0 : ℂ) 1))
    {t : ℝ} (ht : 0 < t) : ∀ᵐ ω ∂P,
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ s ∈ Icc t (t + δ), closure (cluster (μ ω) 1 z s) ⊆
          cluster (μ ω) 1 z t + ball (0 : ℂ) ε := by
  apply ae_lqg_cluster_right_continuous_at_fixed_time_of_quasiInvariant_scaling
    hI2 hγ hγ2 hα hGFF hμ hz T hquasi _ ht
  intro c hc
  filter_upwards [hlocal c hc] with ω hω s hs
  exact cluster_eq_of_restrict_eq_smul zero_lt_one hc hs.le hω

/-- A quasi-invariant transformation cannot shift the normalized unit-circle
average by a nonzero deterministic constant. This is an obstruction to using
a global additive field shift as the quasi-invariant action above. -/
theorem IsWholePlaneGFF.eq_zero_of_quasiInvariant_circleAverage_shift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (T : Ω → Ω)
    (hT : Measure.QuasiMeasurePreserving T P P) {a : ℝ}
    (hshift : ∀ᵐ ω ∂P, hcirc (T ω) 1 0 = hcirc ω 1 0 + a) : a = 0 := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have ha : ∀ᵐ ω ∂P, a = 0 := by
    filter_upwards [hGFF.ae_circleAverage_one_zero,
      hT.ae hGFF.ae_circleAverage_one_zero, hshift] with ω h0 hT0 hs
    linarith
  exact ha.exists.choose_spec

/-- The normalization also prevents a nonzero deterministic shift of every
concentric circle average inside the unit disc under a quasi-invariant map. -/
theorem IsWholePlaneGFF.eq_zero_of_quasiInvariant_inner_circleAverage_shift
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (T : Ω → Ω)
    (hT : Measure.QuasiMeasurePreserving T P P) {a : ℝ}
    (hshift : ∀ᵐ ω ∂P, ∀ r ∈ Ioo (0 : ℝ) 1,
      hcirc (T ω) r 0 = hcirc ω r 0 + a) : a = 0 := by
  apply hGFF.eq_zero_of_quasiInvariant_circleAverage_shift T hT
  filter_upwards [hGFF.ae_continuousOn_circle,
    hT.ae hGFF.ae_continuousOn_circle, hshift] with ω hcont hcontT hs
  have hc (ω' : Ω)
      (h : ContinuousOn (fun p : ℝ × ℂ => hcirc ω' p.1 p.2) (Ioi 0 ×ˢ univ)) :
      ContinuousOn (fun r : ℝ => hcirc ω' r 0) (Ioc 0 1) := by
    apply h.comp (continuous_id.prodMk continuous_const).continuousOn
    intro r hr
    exact ⟨hr.1, trivial⟩
  have heq : Set.EqOn (fun r : ℝ => hcirc (T ω) r 0)
      (fun r : ℝ => hcirc ω r 0 + a) (Ioo 0 1) := hs
  have heq' := heq.of_subset_closure (hc _ hcontT) ((hc _ hcont).add continuousOn_const)
    Ioo_subset_Ioc_self (by rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]; exact Ioc_subset_Icc_self)
  exact heq' ⟨zero_lt_one, le_rfl⟩

end HarmonicBalls
