import HarmonicBalls.Proofs.Sec8.RootedFieldCoordinateLaw

/-! # Typical points from observed rooted bind laws

Almost-everywhere properties of an observed unnormalized rooted bind transfer
to typical points on its sampling set. A countable cover transfers them to
typical points of the full random measure. No rooted change-of-measure formula
is assumed. The imported Section 6 development uses Leonardo Bonanno's
whole-plane GFF formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- A property of the observed rooted bind holds at almost every root in the
sampling set. The property itself need not be measurable. -/
theorem ae_ae_mem_of_observed_restricted_bind
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (P : Measure Ω) (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (X : Ω → F) (hX : Measurable X) (B : Set ℂ) (hB : MeasurableSet B)
    (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞) {p : F × ℂ → Prop}
    (hp : ∀ᵐ x ∂(P.bind fun ω => ((μ ω).restrict B).map (fun z => (X ω, z))), p x) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ B → p (X ω, z) := by
  have hk := aemeasurable_observed_restricted_root_kernel P μ hμ X hX B hB hfin
  filter_upwards [Measure.ae_ae_of_ae_bind hk hp] with ω hω
  have hz : ∀ᵐ z ∂(μ ω).restrict B, p (X ω, z) :=
    ae_of_ae_map measurable_prodMk_left.aemeasurable hω
  exact (ae_restrict_iff' hB).mp hz

/-- Observed rooted bind properties on a countable cover hold at almost every
point of the original random measure. -/
theorem ae_ae_of_observed_restricted_bind_cover
    {Ω F : Type*} [MeasurableSpace Ω] [MeasurableSpace F]
    (P : Measure Ω) (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (X : Ω → F) (hX : Measurable X) (B : ℕ → Set ℂ)
    (hB : ∀ n, MeasurableSet (B n)) (hcover : ∀ z, ∃ n, z ∈ B n)
    (hfin : ∀ n, ∀ᵐ ω ∂P, μ ω (B n) ≠ ∞) {p : F × ℂ → Prop}
    (hp : ∀ n, ∀ᵐ x ∂(P.bind fun ω => ((μ ω).restrict (B n)).map
      (fun z => (X ω, z))), p x) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, p (X ω, z) := by
  have h : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ B n → p (X ω, z) := fun n =>
    ae_ae_mem_of_observed_restricted_bind P μ hμ X hX (B n) (hB n) (hfin n) (hp n)
  filter_upwards [ae_all_iff.mpr h] with ω hω
  filter_upwards [ae_all_iff.mpr hω] with z hz
  obtain ⟨n, hn⟩ := hcover z
  exact hz n hn

/-- The unit-disk raw whole-plane rooted bind transfers almost-everywhere
properties to LQG-typical roots in the disk. -/
theorem IsWholePlaneGFF.ae_ae_mem_unitBall_of_raw_rooted_bind
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasure P γ hcirc μ)
    {p : (RawMeanZeroTest → ℝ) × ℂ → Prop}
    (hp : ∀ᵐ x ∂(P.bind fun ω => ((μ ω).restrict (ball 0 1)).map
      (fun z => ((fun φ : RawMeanZeroTest => hC ω φ.1), z))), p x) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ ball 0 1 →
      p ((fun φ : RawMeanZeroTest => hC ω φ.1), z) := by
  filter_upwards [Measure.ae_ae_of_ae_bind (hh.aemeasurable_raw_rooted_unitBall_kernel hμ) hp]
    with ω hω
  have hz : ∀ᵐ z ∂(μ ω).restrict (ball 0 1),
      p ((fun φ : RawMeanZeroTest => hC ω φ.1), z) :=
    ae_of_ae_map measurable_prodMk_left.aemeasurable hω
  exact (ae_restrict_iff' measurableSet_ball).mp hz

#print axioms ae_ae_mem_of_observed_restricted_bind
#print axioms ae_ae_of_observed_restricted_bind_cover
#print axioms IsWholePlaneGFF.ae_ae_mem_unitBall_of_raw_rooted_bind

end HarmonicBalls
