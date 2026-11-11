import HarmonicBalls.Proofs.Sec11.CorrectedPinchUniformFirstShift
import HarmonicBalls.Proofs.Sec11.CorrectedPinchOpenThresholds

/-! A deterministic smooth shift enforcing the first pinch event. -/

namespace HarmonicBalls

open Set Metric
open scoped ENNReal ContDiff

/-- For fixed thresholds, one smooth compactly supported nonnegative shift
forces the first auxiliary event simultaneously for every pair of metrics
satisfying the forward and reverse Weyl identities and the four bounds. -/
theorem IsPinchPointProofConfiguration.exists_uniform_open_first_event_shift
    {U V W T Q' Q : Set ℂ} {δ ξ : ℝ}
    (h : IsPinchPointProofConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    (n m k l : ℕ) (hn : 0 < n) (hk : 0 < k) :
    ∃ f : ℂ → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
      (∀ x, 0 ≤ f x) ∧
      (∀ x ∉ thickening δ Q ∪ ball 0 δ, f x = 0) ∧
      ∀ D E : ℂ → ℂ → ℝ, IsEuclideanLengthMetric D → IsEuclideanLengthMetric E →
        (∀ x y, 0 ≤ E x y) →
        (∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y) →
        (∀ x y, ENNReal.ofReal (D x y) = weylScaling E ξ (fun z => -f z) x y) →
        (n : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (setDist D Q' (frontier Q)) →
        (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric D
          (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
            closure (thickening (2 * δ) W))) 0 y) ≤ m →
        (k : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (setDist D {0} (sphere 0 (δ / 2))) →
        internalDiam D δ (T \ thickening (3 * δ) W) ≤ l →
        pinchFirstEvent E W T Q' Q δ ∧
        (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric E
          (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
            closure (thickening (2 * δ) W))) 0 y) <
          ENNReal.ofReal (setDist E Q' (frontier Q)) := by
  obtain ⟨a, b, ha, hb, hnumQ, hnum0⟩ :=
    exists_first_pinch_weyl_heights hξ n m k l hn hk
  obtain ⟨f, hsm, hcomp, hnonneg, hcorridor, hQ, hroot, houter, hsupport⟩ :=
    h.exists_first_buffered_weight_corridor_bound hξ.le ha hb
  refine ⟨f, hsm, hcomp, hnonneg, hsupport, ?_⟩
  intro D E hD hE hEnonneg hforward hreverse hgapQ hpath hgap0 hdiam
  constructor
  · exact h.first_event_of_thresholds hD hE hEnonneg hforward hreverse
      hcorridor hQ hroot houter hgapQ hpath hgap0 hdiam hnumQ hnum0
  · let F : Set ℂ := ball 0 6 \ (closure (thickening (2 * δ) Q) ∪
      closure (thickening (2 * δ) W))
    change (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric D F 0 y) ≤ m at hpath
    have hopen : IsOpen F := isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)
    have hub : (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric E F 0 y) ≤
        ENNReal.ofReal (Real.exp (ξ * b)) * m := by
      apply iSup_le
      intro y
      apply iSup_le
      intro hy
      calc
        internalMetric E F 0 y ≤ ENNReal.ofReal (Real.exp (ξ * b)) *
            internalMetric D F 0 y :=
          hD.internalMetric_weylScaling_le hE hEnonneg hopen (hD.weylScaling_zero ξ)
            hforward hcorridor 0 y
        _ ≤ ENNReal.ofReal (Real.exp (ξ * b)) * m := by
          gcongr
          have hybound : internalMetric D F 0 y ≤
              (⨆ z ∈ sphere (0 : ℂ) 5, internalMetric D F 0 z) :=
            le_iSup_of_le y (le_iSup_of_le hy le_rfl)
          exact hybound.trans hpath
    have hscaleQ : ENNReal.ofReal (Real.exp (ξ * a)) * (n : ℝ≥0∞)⁻¹ ≤
        ENNReal.ofReal (Real.exp (ξ * a)) * ENNReal.ofReal (setDist D Q' (frontier Q)) := by
      gcongr
    exact lt_of_le_of_lt hub (lt_of_lt_of_le hnumQ
      (hscaleQ.trans (h.obstacle_boundary_weyl_lower_bound hD hE hQ hreverse)))


end HarmonicBalls
