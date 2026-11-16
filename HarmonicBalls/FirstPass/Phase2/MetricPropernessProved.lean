import HarmonicBalls.FirstPass.S11.MetricBall
import HarmonicBalls.Proposed.MetricProperness
import HarmonicBalls.FirstPass.Phase2.WeylExponentOfDG20
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Eq115

/-!
# Compactness from large-scale metric crossings

The deterministic conclusion of the proof of Dubédat, Falconet, Gwynne,
Pfeffer and Sun, Lemma 3.8: sufficiently large crossings force metric balls
to lie in bounded Euclidean sets.
-/

namespace HarmonicBalls

/-- Large metric distances across arbitrarily large annuli imply compactness
of all closed metric balls in the Euclidean topology. -/
theorem IsEuclideanLengthMetric.isCompact_closedBall_of_far_crossing
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hfar : ∀ N R : ℝ, ∃ ρ : ℝ, R ≤ ρ ∧ ∀ x y : ℂ,
      ‖x‖ ≤ ρ → 3 / 2 * ρ ≤ ‖y‖ → N ≤ D x y)
    (z : ℂ) (R : ℝ) : IsCompact {w : ℂ | D z w ≤ R} := by
  obtain ⟨ρ, hz, hρ⟩ := hfar (R + 1) ‖z‖
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_le (FirstPassS11.continuous_dist_right hD z) continuous_const) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3 / 2 * ρ)).subset ?_
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hn
  push Not at hn
  have h := hρ z w hz hn.le
  change D z w ≤ R at hw
  linarith

/-- The distribution-valued form of an LQG metric satisfies the weak metric
axioms with its natural scaling constants. -/
theorem isWeakLQGMetric_distributionMetric {γ ξ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    LQGMetric.IsWeakLQGMetric γ (distributionMetric 𝔇)
      (fun r => r ^ (LQGMetric.xiGamma γ * LQGMetric.Q γ)) := by
  have hξ := xi_eq_xiGamma_derived γ ξ hγ hγ₂ 𝔇 h𝔇
  have hcm : ∀ D : ℂ → ℂ → ℝ, LatticeProb.LQG.IsEuclideanLengthMetric D →
      ∃ d : LQGMetric.ContMetric, (∀ u v, d.1 (u, v) = D u v) ∧ d.IsLength :=
    fun _ hD => LatticeProb.LQG.exists_contMetric_of_isEuclideanLengthMetric hD
  apply LQGMetric.GM.gm_eq1_15 hγ
  refine ⟨measurable_distributionMetric h𝔇.measurable_apply, ?_, ?_, ?_, ?_⟩
  · intro Ω _ P _ h hh
    exact ae_isLength_distributionMetric h𝔇 hcm hh
  · intro Ω _ P _ h hh U
    exact locality_distributionMetric h𝔇 hcm hh U
  · intro Ω _ P _ h hh
    simpa only [hξ] using ae_weylScale_distributionMetric h𝔇 hcm hh
  · intro Ω _ P _ h hh r hr z
    exact ae_coord_distributionMetric h𝔇 hcm hh hr z

end HarmonicBalls
