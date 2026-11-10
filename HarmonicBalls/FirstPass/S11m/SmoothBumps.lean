import HarmonicBalls.FirstPass.S11d.SmoothCutoff
import HarmonicBalls.FirstPass.S11h.Faithful

/-!
# Smooth pinch bumps and the smooth shift weight (fp-S11m, owner z4)

Route: `notes/fp-gaps/CHATGPT-z4-11-12-local-certificate.md` section 6.2 (bumps `φ_Q`, `φ_0`, weight
`ξ⁻¹ (log b_Q φ_Q + log b φ_0)`) and paper `lem:E1` (`paper/lqg_harmonic_ball-corrected.tex`, lines 3661-3700).
The bumps of `E1Event.lean` are continuous; the Cameron-Martin transfer
(`CameronMartinMetricEventTransferMeasurableFrozen`, `FirstPass/Frozen/S11j.lean`) needs smooth, compactly supported
shifts vanishing on the unit circle. Deterministic.
-/

namespace HarmonicBalls

open Set Metric

/-- A smooth cutoff equal to `1` on a compact `K` and vanishing off a bounded open `U ⊇ K`, with values in `[0,1]`. -/
theorem exists_smooth_bump_on {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (hUb : Bornology.IsBounded U) :
    ∃ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ (∀ z ∈ K, φ z = 1) ∧
      (∀ z, z ∉ U → φ z = 0) ∧ (∀ z, φ z ∈ Icc (0 : ℝ) 1) := by
  obtain ⟨φ, hf, hcs, hts, hI, h1⟩ := exists_smooth_cutoff hK hU hKU hUb
  refine ⟨φ, hf, hcs, h1, fun z hz => ?_, fun z => Set.mem_Icc.2 (hI z)⟩
  by_contra h
  exact hz (hts (subset_tsupport φ (Function.mem_support.2 h)))

/-- The smooth pinch bumps of paper `lem:E1` (smooth version of `exists_pinch_bumps`): `φ_Q = 1` on `Q̄`,
`φ_Q = 0` off `B_δ(Q)`; `φ_0 = 1` on `B̄_{δ/2}`, `φ_0 = 0` off `B_δ(0)`; both smooth with compact support. -/
theorem exists_smooth_pinch_bumps {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) :
    ∃ φQ φ0 : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φQ ∧ HasCompactSupport φQ ∧
      (∀ z ∈ closure Q, φQ z = 1) ∧ (∀ z, z ∉ thickening δ Q → φQ z = 0) ∧ (∀ z, φQ z ∈ Icc (0 : ℝ) 1) ∧
      ContDiff ℝ (⊤ : ℕ∞) φ0 ∧ HasCompactSupport φ0 ∧
      (∀ z ∈ closedBall (0 : ℂ) (δ / 2), φ0 z = 1) ∧ (∀ z, z ∉ ball (0 : ℂ) δ → φ0 z = 0) ∧
      (∀ z, φ0 z ∈ Icc (0 : ℝ) 1) := by
  have hδ := hgeo.delta_pos
  have hQb : Bornology.IsBounded (closure Q) :=
    (Metric.isBounded_ball : Bornology.IsBounded (ball (0 : ℂ) 5)).subset fun z hz =>
      ((hgeo.closure_Q_subset hz).1 : z ∈ ball (0 : ℂ) 5 \ closedBall (0 : ℂ) 4).1
  obtain ⟨φQ, h1, h2, h3, h4, h5⟩ :=
    exists_smooth_bump_on (Metric.isCompact_of_isClosed_isBounded isClosed_closure hQb) isOpen_thickening
      (closure_subset_thickening hδ Q) ((hQb.subset subset_closure).thickening)
  obtain ⟨φ0, k1, k2, k3, k4, k5⟩ :=
    exists_smooth_bump_on (isCompact_closedBall (0 : ℂ) (δ / 2)) isOpen_ball
      (closedBall_subset_ball (show δ / 2 < δ by linarith)) Metric.isBounded_ball
  exact ⟨φQ, φ0, h1, h2, h3, h4, h5, k1, k2, k3, k4, k5⟩

/-- The unit circle misses the supports of the pinch bumps: `δ < 1/1000` and `closure Q ⊆ annulus 0 4 5`. -/
theorem pinch_bumps_vanish_on_circle {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {φQ φ0 : ℂ → ℝ} (hQ0 : ∀ z, z ∉ thickening δ Q → φQ z = 0) (h00 : ∀ z, z ∉ ball (0 : ℂ) δ → φ0 z = 0)
    (z : ℂ) (hz : ‖z‖ = 1) : φQ z = 0 ∧ φ0 z = 0 := by
  have hδ1 : δ < 1 := by linarith [hgeo.delta_lt]
  refine ⟨?_, h00 z ?_⟩
  · apply hQ0 z
    intro h
    obtain ⟨w, hwQ, hzw⟩ := mem_thickening_iff.1 h
    have hw4 : (4 : ℝ) < ‖w‖ := by
      have hw : w ∉ closedBall (0 : ℂ) 4 :=
        ((hgeo.closure_Q_subset (subset_closure hwQ)).1 : w ∈ ball (0 : ℂ) 5 \ closedBall (0 : ℂ) 4).2
      simpa using hw
    have hab := abs_norm_sub_norm_le z w
    rw [← dist_eq_norm] at hab
    have hb := abs_le.1 (hab.trans hzw.le)
    linarith [hb.1, hb.2]
  · intro h
    rw [mem_ball_zero_iff, hz] at h
    linarith

/-- The shift weight `f = ξ⁻¹ (log b_Q φ_Q + log b φ_0)` of paper `lem:E1`. -/
noncomputable def shiftWeight (ξ b bQ : ℝ) (φQ φ0 : ℂ → ℝ) : ℂ → ℝ :=
  fun z => ξ⁻¹ * (Real.log bQ * φQ z + Real.log b * φ0 z)

/-- The shift weight is smooth and compactly supported, vanishes on the unit circle, has zero circle average on the
unit circle, and satisfies `ξ f = log b_Q φ_Q + log b φ_0` (the hypothesis `hfsum` of
`pinchFirstEventLocal_weylScaling`). -/
theorem shiftWeight_props {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {ξ b bQ : ℝ} (hξ : 0 < ξ) {φQ φ0 : ℂ → ℝ} (hφQ : ContDiff ℝ (⊤ : ℕ∞) φQ) (hφQc : HasCompactSupport φQ)
    (hQ0 : ∀ z, z ∉ thickening δ Q → φQ z = 0) (hφ0 : ContDiff ℝ (⊤ : ℕ∞) φ0) (hφ0c : HasCompactSupport φ0)
    (h00 : ∀ z, z ∉ ball (0 : ℂ) δ → φ0 z = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (shiftWeight ξ b bQ φQ φ0) ∧ HasCompactSupport (shiftWeight ξ b bQ φQ φ0) ∧
      (∀ z : ℂ, ‖z‖ = 1 → shiftWeight ξ b bQ φQ φ0 z = 0) ∧
      Real.circleAverage (shiftWeight ξ b bQ φQ φ0) 0 1 = 0 ∧
      (∀ z, ξ * shiftWeight ξ b bQ φQ φ0 z = Real.log bQ * φQ z + Real.log b * φ0 z) := by
  have key : ∀ g : ℂ → ℝ, ∀ z, z ∉ tsupport g → g z = 0 := fun g z hz =>
    by_contra fun h => hz (subset_tsupport g (Function.mem_support.2 h))
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞) (shiftWeight ξ b bQ φQ φ0) := by
    unfold shiftWeight
    exact contDiff_const.mul ((contDiff_const.mul hφQ).add (contDiff_const.mul hφ0))
  have hcs : HasCompactSupport (shiftWeight ξ b bQ φQ φ0) := by
    refine HasCompactSupport.intro (hφQc.isCompact.union hφ0c.isCompact) fun z hz => ?_
    have h1 : φQ z = 0 := key φQ z (fun h => hz (Or.inl h))
    have h2 : φ0 z = 0 := key φ0 z (fun h => hz (Or.inr h))
    simp [shiftWeight, h1, h2]
  have hcirc0 : ∀ z : ℂ, ‖z‖ = 1 → shiftWeight ξ b bQ φQ φ0 z = 0 := fun z hz => by
    have h := pinch_bumps_vanish_on_circle hgeo hQ0 h00 z hz
    simp [shiftWeight, h.1, h.2]
  refine ⟨hsmooth, hcs, hcirc0, ?_, fun z => ?_⟩
  · unfold Real.circleAverage
    simp [hcirc0]
  · exact mul_inv_cancel_left₀ hξ.ne' _

end HarmonicBalls
