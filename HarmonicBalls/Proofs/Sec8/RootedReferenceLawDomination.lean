import HarmonicBalls.Proofs.Sec11.PinchReferenceLaw
import HarmonicBalls.Proofs.Sec8.LocalSmoothShiftLaw

/-! # Integrating fixed-root field comparisons

Pointwise domination of shifted field laws gives domination of the corresponding
joint laws with the independent root retained as a coordinate.
The imported Section 6 development uses Leonardo Bonanno's whole-plane GFF
formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set

/-- A measurable family of fixed-root comparisons lifts to the joint
field-and-root reference laws. The root marginal need not be finite. -/
theorem shiftedRootReferenceLaw_absolutelyContinuous_of_fiberwise
    {Z Ω Ξ F : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    [MeasurableSpace Ξ] [MeasurableSpace F]
    (ρ : Measure Z) (P : Measure Ω) (Q : Measure Ξ) [SFinite P] [SFinite Q]
    (X : Z × Ω → F) (Y : Z × Ξ → F)
    (hX : Measurable X) (hY : Measurable Y)
    (hdom : ∀ᵐ z ∂ρ, P.map (fun o => X (z, o)) ≪ Q.map (fun o => Y (z, o))) :
    shiftedRootReferenceLaw ρ P X ≪ shiftedRootReferenceLaw ρ Q Y := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hzero
  have haetarget : ∀ᵐ x ∂shiftedRootReferenceLaw ρ Q Y, x ∉ s :=
    measure_eq_zero_iff_ae_notMem.mp hzero
  have hm : Measurable (fun x : Z × Ξ => (Y x, x.1)) := hY.prodMk measurable_fst
  have hs' : MeasurableSet {x : F × Z | x ∉ s} := hs.compl
  have haepair : ∀ᵐ x ∂(ρ.prod Q), (Y x, x.1) ∉ s :=
    (ae_map_iff hm.aemeasurable hs').mp haetarget
  have hfixed : ∀ᵐ z ∂ρ, ∀ᵐ f ∂Q.map (fun o => Y (z, o)), (f, z) ∉ s := by
    have hsections := (Measure.ae_prod_iff_ae_ae (hm hs')).mp haepair
    filter_upwards [hsections] with z hz
    have hsection : Measurable (fun o => Y (z, o)) := hY.comp measurable_prodMk_left
    have hsectionset : MeasurableSet {f | (f, z) ∉ s} := measurable_prodMk_right hs'
    exact (ae_map_iff hsection.aemeasurable hsectionset).2 hz
  have haesource : ∀ᵐ x ∂shiftedRootReferenceLaw ρ P X, x ∉ s :=
    ae_shiftedRootReferenceLaw_of_ae_comparison ρ P X hX
      (fun z => Q.map (fun o => Y (z, o))) hs' hdom hfixed
  exact measure_eq_zero_iff_ae_notMem.mpr haesource

/-- A fixed-root global shift comparison lifts, after restriction and a
root-dependent common insertion, to the joint local field-and-root law.
Joint measurability and the global comparisons remain explicit premises. -/
theorem shiftedRootReferenceLaw_local_shift_domination
    {Z Ω : Type*} [MeasurableSpace Z] [MeasurableSpace Ω]
    (ρ : Measure Z) (P : Measure Ω) [SFinite P] {c : ℂ} {r : ℝ}
    (X : Ω → LQGMetric.TestC0 → ℝ) (hX : Measurable X)
    (f g : Z → ℂ → ℝ) (k : Z → Section6.LocalTest (Metric.ball c r) → ℝ)
    (heq : ∀ᵐ z ∂ρ, EqOn (f z) (g z) (Metric.closedBall c r))
    (hdom : ∀ᵐ z ∂ρ,
      P.map (fun o φ => X o φ + ∫ x, φ.1 x * f z x) ≪ P.map X)
    (hshift : Measurable (fun p : Z × Ω =>
      fun φ : Section6.LocalTest (Metric.ball c r) =>
        X p.2 φ.1 + (∫ x, φ.1.1 x * g p.1 x) + k p.1 φ))
    (hbase : Measurable (fun p : Z × Ω =>
      fun φ : Section6.LocalTest (Metric.ball c r) => X p.2 φ.1 + k p.1 φ)) :
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (Metric.ball c r) =>
        X p.2 φ.1 + (∫ x, φ.1.1 x * g p.1 x) + k p.1 φ) ≪
    shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : Section6.LocalTest (Metric.ball c r) => X p.2 φ.1 + k p.1 φ) := by
  apply shiftedRootReferenceLaw_absolutelyContinuous_of_fiberwise ρ P P _ _ hshift hbase
  filter_upwards [heq, hdom] with z heqz hdomz
  exact local_shifted_pairing_laws_of_global_domination P X hX (f z) (g z) heqz (k z) hdomz

end HarmonicBalls
