import HarmonicBalls.Proofs.GFF.CoordinateModification
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgRate
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Field.Measurable

/-!
# A whole-plane GFF plus a continuous function, in project coordinates

Leonardo Bonanno's fields `IsGFFPlusCont h P` (a distribution-valued whole-plane GFF, with an
arbitrary random additive constant, plus a measurably chosen random continuous function) are,
on the same probability space and with the same test pairings, a project whole-plane GFF
(normalized by its unit circle average around `0`) plus a random continuous function.

The normalization subtracts the unit circle average `h_1(0)` of the GFF part: adding a
measurable random constant keeps the whole-plane GFF property
(`LQGMetric.IsWholePlaneGFF.addConst`), and almost surely `(h + c)_1(0) = h_1(0) + c`
(`LQGMetric.CircleAvg.ae_circleAvg_addConst_one_zero`). The normalized field is identified with a
project whole-plane GFF by `normalizedGFF_exists_projectGFF`, and the subtracted circle average
is moved into the continuous part.
-/

open MeasureTheory ProbabilityTheory

namespace HarmonicBalls

/-- The distribution of a continuous function, paired with a test function, with the
integrand written as `f x * φ x`. -/
theorem ofCont_apply_mul (f : C(ℂ, ℝ)) (φ : LQGMetric.TestC) :
    LQGMetric.ofCont f φ = ∫ x, f x * φ x := by
  rw [LQGMetric.ofCont_apply]
  simp_rw [mul_comm (φ _)]

/-- **A Bonanno whole-plane GFF plus a continuous function is a project whole-plane GFF plus
a continuous function.** On the same probability space, every field `h` with
`LQGMetric.IsGFFPlusCont h P` has test pairings `h ω φ = hC ω φ + ∫ g ω x φ x`, where
`(hC, hcirc)` is a project whole-plane GFF and `g` is a random continuous function, measurable
at every point. -/
theorem exists_projectGFF_of_isGFFPlusCont {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → LQGMetric.DistC} (hh : LQGMetric.IsGFFPlusCont h P) :
    ∃ (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (g : Ω → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc ∧ (∀ ω, Continuous (g ω)) ∧
      (∀ x, Measurable fun ω => g ω x) ∧
      ∀ ω (φ : LQGMetric.TestC), h ω φ = hC ω φ + ∫ x, g ω x * φ x := by
  obtain ⟨-, f0, hf0, h0⟩ := hh
  let G : Ω → LQGMetric.DistC := fun ω => h ω - LQGMetric.ofCont (f0 ω)
  let a : Ω → ℝ := fun ω => LQGMetric.circleAvg (G ω) 1 0
  have ham : Measurable a := (LQGMetric.measurable_circleAvg_left 1 0).comp h0.measurable
  have h1 : LQGMetric.IsWholePlaneGFF (fun ω => LQGMetric.addConst (G ω) (-a ω)) P :=
    h0.addConst ham.neg
  have h2 : LQGMetric.IsNormalizedWPGFF (fun ω => LQGMetric.addConst (G ω) (-a ω)) P := by
    refine ⟨h1, ?_⟩
    filter_upwards [LQGMetric.CircleAvg.ae_circleAvg_addConst_one_zero h0] with ω hω
    rw [hω]
    exact add_neg_cancel _
  obtain ⟨hC, hcirc, hGFF, hCeq, -⟩ := normalizedGFF_exists_projectGFF h2
  let g : Ω → C(ℂ, ℝ) := fun ω => f0 ω + ContinuousMap.const ℂ (a ω)
  refine ⟨hC, hcirc, fun ω x => g ω x, hGFF, fun ω => (g ω).continuous, fun x => ?_,
    fun ω φ => ?_⟩
  · exact ((continuous_eval_const x).measurable.comp hf0).add ham
  · have hconst : LQGMetric.ofCont (ContinuousMap.const ℂ (a ω)) φ = (∫ x, φ x) * a ω := by
      have e := LQGMetric.GFFInv.addConst_apply 0 (a ω) φ
      simpa [LQGMetric.addConst, LQGMetric.addFun] using e
    have hsplit : (∫ x, g ω x * φ x) =
        LQGMetric.ofCont (f0 ω) φ + LQGMetric.ofCont (ContinuousMap.const ℂ (a ω)) φ := by
      have hadd : LQGMetric.ofCont (g ω) =
          LQGMetric.ofCont (f0 ω) + LQGMetric.ofCont (ContinuousMap.const ℂ (a ω)) := by
        unfold LQGMetric.ofCont
        rw [ContinuousMap.coe_add]
        exact Distribution.ofFun_add ((f0 ω).continuous.locallyIntegrable.locallyIntegrableOn _)
          ((ContinuousMap.const ℂ (a ω)).continuous.locallyIntegrable.locallyIntegrableOn _)
      rw [← ofCont_apply_mul, hadd]
      rfl
    have hG : G ω φ = h ω φ - LQGMetric.ofCont (f0 ω) φ := rfl
    rw [hCeq, LQGMetric.GFFInv.addConst_apply, hsplit, hconst, hG]
    ring

end HarmonicBalls
