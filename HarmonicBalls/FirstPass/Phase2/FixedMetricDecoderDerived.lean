import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.Steps.Sec11.CenteredFieldSigma
import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity
import HarmonicBalls.Steps.Sec11.ContinuousFieldShift
import HarmonicBalls.Steps.Sec11.MetricConstantScaling
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity
import HarmonicBalls.Steps.Sec11.CountableCoordinateObservables
import HarmonicBalls.FirstPass.S11m.Finiteness

/-!
# Fixed-metric normalized measurable decoder, derived (task fp-phase2-b1-decoder-derive, owner z4)

Target: `LocalLQGMetricNormalizedMeasurableFixedMetricFrozen` (`FirstPass/S11r/Frozen.lean:89`), audit binder hB1.
Route: MQ-lh-4 (`notes/fp-gaps/MATH-ANSWERS.md` lines 405-431).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric ProbabilityTheory
open scoped ENNReal

universe u

/-- The open square `ball c r ×ˢ ball c r` is a Polish space (open subspace of `ℂ × ℂ`). -/
instance ballSquare_polishSpace (c : ℂ) (r : ℝ) :
    PolishSpace ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) :=
  IsOpen.polishSpace ((isOpen_ball).prod isOpen_ball)

/-- The open square `ball c r ×ˢ ball c r` is locally compact. -/
instance ballSquare_locallyCompactSpace (c : ℂ) (r : ℝ) :
    LocallyCompactSpace ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) :=
  IsOpen.locallyCompactSpace ((isOpen_ball).prod isOpen_ball)

/-- A countable dense sequence in the closed-and-open square `ball c r ×ˢ ball c r`, and a measurable decoder that
recovers a continuous function on the square from its values along the sequence (Borel embedding of
`C(X, ℝ)` into `ℕ → ℝ`, as in `IsLQGMetric.exists_common_continuous_observable`). -/
theorem exists_dense_decode_ball (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ d : ℕ → ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)), DenseRange d ∧
      ∃ decode : (ℕ → ℝ) → C(↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)), ℝ), Measurable decode ∧
        ∀ f : C(↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)), ℝ), decode (fun n => f (d n)) = f := by
  have hne : Nonempty ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) :=
    ⟨⟨(c, c), mem_ball_self hr, mem_ball_self hr⟩⟩
  let d : ℕ → ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) := TopologicalSpace.denseSeq _
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq _
  let e : C(↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)), ℝ) → ℕ → ℝ := fun f n => f (d n)
  have he : Measurable e := measurable_pi_iff.mpr fun n => (continuous_eval_const (d n)).measurable
  have hinj : Function.Injective e := by
    intro f g h
    apply ContinuousMap.ext
    have hdense := hd.equalizer f.continuous g.continuous
    apply congrFun (hdense ?_)
    funext n
    exact congrFun h n
  have hemb : MeasurableEmbedding e := he.measurableEmbedding hinj
  obtain ⟨decode, hdecode, hdecode_eq⟩ :=
    hemb.exists_measurable_extend (g := id) measurable_id (fun _ => inferInstance)
  exact ⟨d, hd, decode, hdecode, fun f => congrFun hdecode_eq f⟩

end HarmonicBalls
