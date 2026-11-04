import HarmonicBalls.Draft.Section6

/-!
# Comparison of good annuli

The good-annulus condition depends on the measure only through mass ratios on the annulus.
This is the deterministic comparison used in the singular-weight reduction in the proof of
Lemma 6.4. The comparison factor is arbitrary, since the weight need not be flat to within a
universal factor on an annulus which approaches the singularity.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- A lower and an upper comparison of measures on an annulus transfer its good-annulus
property, with the mass threshold divided by the ratio of the comparison constants. -/
theorem isGoodAnnulus_of_measure_comparison
    {μ ν : Measure ℂ} {r a b t : ℝ} {z : ℂ} {c : ℝ≥0∞}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (ht : 0 < t)
    (hlower : ∀ s ⊆ annulus z (3 * r) (5 * r), c * ν s ≤ μ s)
    (hupper : μ (annulus z (3 * r) (5 * r)) ≤
      ENNReal.ofReal t * c * ν (annulus z (3 * r) (5 * r)))
    (hg : IsGoodAnnulus ν r z a b) : IsGoodAnnulus μ r z (a / t) b := by
  intro Y hY hYA hmass u hu
  refine hg Y hY hYA ?_ u hu
  refine (ENNReal.mul_le_mul_iff_right hc0 hct).1 ?_
  calc c * ν Y ≤ μ Y := hlower Y hYA
    _ ≤ ENNReal.ofReal (a / t) * μ (annulus z (3 * r) (5 * r)) := hmass
    _ ≤ ENNReal.ofReal (a / t) *
        (ENNReal.ofReal t * c * ν (annulus z (3 * r) (5 * r))) := by gcongr
    _ = c * ((ENNReal.ofReal (a / t) * ENNReal.ofReal t) *
        ν (annulus z (3 * r) (5 * r))) := by ring
    _ = c * (ENNReal.ofReal a * ν (annulus z (3 * r) (5 * r))) := by
      rw [ENNReal.ofReal_div_of_pos ht,
        ENNReal.div_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr ht) ENNReal.ofReal_ne_top]

/-- Transfer a good annulus through a density bounded above and below on the annulus. -/
theorem isGoodAnnulus_of_withDensity_bounds
    {μ ν : Measure ℂ} {r a b t : ℝ} {z : ℂ} {c : ℝ≥0∞} {w : ℂ → ℝ≥0∞}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (ht : 0 < t)
    (hμ : μ.restrict (annulus z (3 * r) (5 * r)) =
      (ν.withDensity w).restrict (annulus z (3 * r) (5 * r)))
    (hw : ∀ x ∈ annulus z (3 * r) (5 * r), c ≤ w x ∧ w x ≤ ENNReal.ofReal t * c)
    (hg : IsGoodAnnulus ν r z a b) : IsGoodAnnulus μ r z (a / t) b := by
  let A := annulus z (3 * r) (5 * r)
  have hA : MeasurableSet A := isOpen_ball.measurableSet.diff isClosed_closedBall.measurableSet
  have hlo : c • ν.restrict A ≤ μ.restrict A := by
    rw [hμ, Measure.le_iff]
    intro s hs
    rw [Measure.smul_apply, Measure.restrict_apply hs, Measure.restrict_apply hs,
      withDensity_apply _ (hs.inter hA), smul_eq_mul, ← setLIntegral_const]
    exact setLIntegral_mono' (hs.inter hA) fun x hx => (hw x hx.2).1
  have hhi : μ.restrict A ≤ (ENNReal.ofReal t * c) • ν.restrict A := by
    rw [hμ, Measure.le_iff]
    intro s hs
    rw [Measure.smul_apply, Measure.restrict_apply hs, Measure.restrict_apply hs,
      withDensity_apply _ (hs.inter hA), smul_eq_mul, ← setLIntegral_const]
    exact setLIntegral_mono' (hs.inter hA) fun x hx => (hw x hx.2).2
  apply isGoodAnnulus_of_measure_comparison hc0 hct ht _ _ hg
  · intro s hs
    have h := hlo s
    rwa [Measure.smul_apply, Measure.restrict_eq_self _ hs, Measure.restrict_eq_self _ hs, smul_eq_mul] at h
  · have h := hhi A
    rwa [Measure.smul_apply, Measure.restrict_eq_self _ (subset_refl A),
      Measure.restrict_eq_self _ (subset_refl A), smul_eq_mul] at h

/-- The density comparison also transfers bounds for the outer probability of a bad annulus;
neither good-annulus event is required to be measurable. -/
theorem badGoodAnnulus_measure_le_of_withDensity_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {μ ν : Ω → Measure ℂ}
    {r a b t : ℝ} {z : ℂ} {c : ℝ≥0∞} {w : ℂ → ℝ≥0∞}
    (hc0 : c ≠ 0) (hct : c ≠ ⊤) (ht : 0 < t)
    (hw : ∀ x ∈ annulus z (3 * r) (5 * r), c ≤ w x ∧ w x ≤ ENNReal.ofReal t * c)
    (hμ : ∀ᵐ ω ∂P, (μ ω).restrict (annulus z (3 * r) (5 * r)) =
      ((ν ω).withDensity w).restrict (annulus z (3 * r) (5 * r))) :
    P {ω | ¬ IsGoodAnnulus (μ ω) r z (a / t) b} ≤
      P {ω | ¬ IsGoodAnnulus (ν ω) r z a b} := by
  apply measure_mono_ae
  filter_upwards [hμ] with ω hω hbad
  intro hgood
  exact hbad (isGoodAnnulus_of_withDensity_bounds hc0 hct ht hω hw hgood)

end HarmonicBalls.Section6
