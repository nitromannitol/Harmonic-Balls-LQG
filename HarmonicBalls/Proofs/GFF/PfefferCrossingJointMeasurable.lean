import HarmonicBalls.Proofs.GFF.PfefferAroundAEMeasurable
import Mathlib.MeasureTheory.Measure.Prod

/-! # Joint measurability of annular distances

The across observable is almost everywhere measurable jointly in the metric,
center and radii, for arbitrary s-finite product measures.
-/

namespace HarmonicBalls

open Set Filter MeasureTheory
open scoped ENNReal

/-- Strict sublevels of the across observable are universally measurable
jointly in a continuous distance function and the circle parameters. -/
theorem uMeasurableSet_pfefferAcross_joint_lt (c : ℝ≥0∞) :
    LQGMetric.UMeasurableSet {q : C(ℂ × ℂ, ℝ) × (ℂ × ℝ × ℝ) |
      pfefferAcross (fun x y => q.1 (x, y)) q.2.1 q.2.2.1 q.2.2.2 < c} := by
  let : PolishSpace C(ℂ × ℂ, ℝ) := LQGMetric.polishSpace_continuousMap _ _
  let R : Set ((C(ℂ × ℂ, ℝ) × (ℂ × ℝ × ℝ)) × (ℂ × ℂ)) := {q |
    dist q.2.1 q.1.2.1 = q.1.2.2.1 ∧
    dist q.2.2 q.1.2.1 = q.1.2.2.2 ∧
    ENNReal.ofReal (q.1.1 (q.2.1, q.2.2)) < c}
  have hR : MeasurableSet R := by
    apply MeasurableSet.inter
    · apply measurableSet_eq_fun <;> fun_prop
    · apply MeasurableSet.inter
      · apply measurableSet_eq_fun <;> fun_prop
      · have hf : Measurable (fun q : (C(ℂ × ℂ, ℝ) × (ℂ × ℝ × ℝ)) × (ℂ × ℂ) =>
            ENNReal.ofReal (q.1.1 (q.2.1, q.2.2))) := by
          apply ENNReal.measurable_ofReal.comp
          exact ((continuous_fst.comp continuous_fst).eval continuous_snd).measurable
        exact measurableSet_lt hf measurable_const
  have hproj := LQGMetric.UMeasurableSet.setOf_exists hR
  convert hproj using 1
  ext q
  change pfefferAcross (fun x y => q.1 (x, y)) q.2.1 q.2.2.1 q.2.2.2 < c ↔
    ∃ v : ℂ × ℂ, dist v.1 q.2.1 = q.2.2.1 ∧
      dist v.2 q.2.1 = q.2.2.2 ∧ ENNReal.ofReal (q.1 (v.1, v.2)) < c
  simp only [pfefferAcross, iInf_lt_iff, Metric.mem_sphere]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩
    exact ⟨(x, y), hx, hy, h⟩
  · rintro ⟨⟨x, y⟩, hx, hy, h⟩
    exact ⟨x, hx, y, hy, h⟩

/-- Pointwise almost everywhere measurable Euclidean length metrics have an
almost everywhere measurable across observable jointly with center and radii. -/
theorem aemeasurable_pfefferAcross_joint_of_ae_pointwise
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [SFinite P]
    (ν : Measure (ℂ × ℝ × ℝ)) [SFinite ν] {D : Ω → ℂ → ℂ → ℝ}
    (hpoint : ∀ x y, AEMeasurable (fun ω => D ω x y) P)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) :
    AEMeasurable (fun q : Ω × (ℂ × ℝ × ℝ) =>
      pfefferAcross (D q.1) q.2.1 q.2.2.1 q.2.2.2) (P.prod ν) := by
  obtain ⟨F, hF, _, hFeq⟩ := exists_measurable_continuousMap_of_ae_pointwise hpoint hmetric
  have hm : @Measurable (NullMeasurableSpace (Ω × (ℂ × ℝ × ℝ)) (P.prod ν)) ℝ≥0∞ _ _
      (fun q => pfefferAcross (fun x y => F q.1 (x, y)) q.2.1 q.2.2.1 q.2.2.2) := by
    apply measurable_of_Iio
    intro c
    exact ((uMeasurableSet_pfefferAcross_joint_lt c).preimage
      ((hF.comp measurable_fst).prodMk measurable_snd)).nullMeasurableSet (P.prod ν)
  have hae : AEMeasurable
      (fun q : Ω × (ℂ × ℝ × ℝ) =>
        pfefferAcross (fun x y => F q.1 (x, y)) q.2.1 q.2.2.1 q.2.2.2) (P.prod ν) :=
    (show NullMeasurable _ (P.prod ν) from hm).aemeasurable
  apply hae.congr
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae hFeq] with q hq
  have heq : (fun x y => F q.1 (x, y)) = D q.1 := by
    funext x y
    exact hq x y
  rw [heq]

end HarmonicBalls
