import HarmonicBalls.Defs.Annuli
import Mathlib.MeasureTheory.Integral.Indicator

/-! # Continuity of annulus mass

Moving an annulus changes its mass continuously at a centre and radius whose
boundary circles carry no mass. This is the mass comparison needed when
examining stability of a good annulus under displacement of its centre.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology

/-- Annular mass is continuous along a countably generated filter of centres and
radii when the limiting boundary circles are null. -/
theorem tendsto_annulus_mass_of_null_boundary
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {z : ℂ} {r : ℝ} {zs : ι → ℂ} {rs : ι → ℝ}
    (hz : Tendsto zs L (𝓝 z)) (hr : Tendsto rs L (𝓝 r))
    (hinner : μ (sphere z (3 * r)) = 0)
    (houter : μ (sphere z (5 * r)) = 0) :
    Tendsto (fun n => μ (annulus (zs n) (3 * rs n) (5 * rs n)))
      L (𝓝 (μ (annulus z (3 * r) (5 * r)))) := by
  classical
  apply tendsto_measure_of_ae_tendsto_indicator L
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
    (fun _ => (isOpen_ball.sdiff isClosed_closedBall).measurableSet)
    (B := ball z (5 * |r| + 6)) isOpen_ball.measurableSet
    (measure_ball_ne_top (μ := μ))
  · have hz' : ∀ᶠ n in L, dist (zs n) z < 1 :=
      hz.eventually (ball_mem_nhds z zero_lt_one)
    have hr' : ∀ᶠ n in L, rs n < r + 1 :=
      hr.eventually (Iio_mem_nhds (by linarith))
    filter_upwards [hz', hr'] with n hnz hnr x hx
    have hx' : dist x (zs n) < 5 * rs n := hx.1
    have ht := dist_triangle x (zs n) z
    have ha := le_abs_self r
    change dist x z < 5 * |r| + 6
    linarith
  · have hi : ∀ᵐ x ∂μ, x ∉ sphere z (3 * r) := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using hinner
    have ho : ∀ᵐ x ∂μ, x ∉ sphere z (5 * r) := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using houter
    filter_upwards [hi, ho] with x hxi hxo
    have hdi : dist x z ≠ 3 * r := hxi
    have hdo : dist x z ≠ 5 * r := hxo
    have hd : Tendsto (fun n => dist x (zs n)) L (𝓝 (dist x z)) :=
      tendsto_const_nhds.dist hz
    have h3 : Tendsto (fun n => 3 * rs n) L (𝓝 (3 * r)) :=
      tendsto_const_nhds.mul hr
    have h5 : Tendsto (fun n => 5 * rs n) L (𝓝 (5 * r)) :=
      tendsto_const_nhds.mul hr
    rcases lt_or_gt_of_ne hdi with hi | hi <;>
      rcases lt_or_gt_of_ne hdo with ho | ho
    · filter_upwards [hd.eventually_lt h3 hi, hd.eventually_lt h5 ho] with n hn3 hn5
      simp only [Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
      constructor <;> intro h <;> rcases h with ⟨h₁, h₂⟩ <;> constructor <;> linarith
    · filter_upwards [hd.eventually_lt h3 hi, h5.eventually_lt hd ho] with n hn3 hn5
      simp only [Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
      constructor <;> intro h <;> rcases h with ⟨h₁, h₂⟩ <;> constructor <;> linarith
    · filter_upwards [h3.eventually_lt hd hi, hd.eventually_lt h5 ho] with n hn3 hn5
      simp only [Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
      constructor <;> intro h <;> rcases h with ⟨h₁, h₂⟩ <;> constructor <;> linarith
    · filter_upwards [h3.eventually_lt hd hi, h5.eventually_lt hd ho] with n hn3 hn5
      simp only [Set.mem_sdiff, mem_ball, mem_closedBall, not_le]
      constructor <;> intro h <;> rcases h with ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- At a null boundary, any strict upper and lower bounds for the mass of an
annulus persist for all sufficiently small changes of its centre and radius. -/
theorem eventually_annulus_mass_bounds_of_null_boundary
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ]
    {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {z : ℂ} {r : ℝ} {zs : ι → ℂ} {rs : ι → ℝ}
    (hz : Tendsto zs L (𝓝 z)) (hr : Tendsto rs L (𝓝 r))
    (hinner : μ (sphere z (3 * r)) = 0)
    (houter : μ (sphere z (5 * r)) = 0)
    {m M : ℝ≥0∞} (hm : m < μ (annulus z (3 * r) (5 * r)))
    (hM : μ (annulus z (3 * r) (5 * r)) < M) :
    ∀ᶠ i in L, m < μ (annulus (zs i) (3 * rs i) (5 * rs i)) ∧
      μ (annulus (zs i) (3 * rs i) (5 * rs i)) < M := by
  have h := tendsto_annulus_mass_of_null_boundary μ hz hr hinner houter
  filter_upwards [tendsto_const_nhds.eventually_lt h hm,
    h.eventually_lt tendsto_const_nhds hM] with i hi hj
  exact ⟨hi, hj⟩

end HarmonicBalls.Section6
