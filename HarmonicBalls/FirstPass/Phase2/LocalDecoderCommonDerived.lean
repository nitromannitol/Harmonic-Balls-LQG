import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# Common local decoder, derived (task fp-phase2-b1-decoder-derive part (2), owner z4)

Targets: `LocalMeasureKernelStmt` (`FirstPass/S11r/Frozen.lean:144`) and `LocalLQGDecoderCommonFrozen`
(`FirstPass/Frozen/S11c.lean:388`). Route: MQ-lh-12 (`notes/fp-gaps/MATH-ANSWERS.md` lines 75-103).

Step 3 of the route (countable Borel coding of continuous functions on a Polish, locally compact space) is proved
here for an arbitrary such space; the square and the profile domain `{(r,x) : closedBall x r ⊆ D}` are instances.
The GMC steps 1, 2, 4-8 of the route are not yet written.
-/

namespace HarmonicBalls

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- MQ-lh-12 step 3: a countable dense family of a Polish, locally compact space `X` and a measurable decoder
recovering each continuous function `X → ℝ` from its values along the family (Borel embedding of `C(X, ℝ)` into
`ℕ → ℝ`, with a measurable left inverse by `MeasurableEmbedding.exists_measurable_extend`). -/
theorem exists_dense_decode_polish (X : Type*) [TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X]
    [Nonempty X] :
    ∃ d : ℕ → X, DenseRange d ∧ ∃ decode : (ℕ → ℝ) → C(X, ℝ), Measurable decode ∧
      ∀ f : C(X, ℝ), decode (fun n => f (d n)) = f := by
  let d : ℕ → X := TopologicalSpace.denseSeq X
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq X
  let e : C(X, ℝ) → ℕ → ℝ := fun f n => f (d n)
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
