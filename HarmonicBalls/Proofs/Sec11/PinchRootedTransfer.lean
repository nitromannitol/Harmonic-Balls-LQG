import HarmonicBalls.Proofs.Sec8.LocalMeasureRatios
import HarmonicBalls.Proofs.Sec11.PinchShiftFrequency
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-! # Rooted-law transfer to measure-typical points

The absolute continuity of the rooted law is kept as a hypothesis. This file
only proves the measure-theoretic transfer; it does not establish the rooted
GFF law or the fixed-point input for that law.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- A rooted almost-everywhere property transfers to typical points of the
original measure when the sampling density is positive almost everywhere on
the sampling set and its weighted mass is finite. -/
theorem ae_ae_of_rooted_weighted_restriction
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    (B : Set ℂ) (hB : MeasurableSet B) (w : ℂ → ℝ≥0∞) (hw : Measurable w)
    (hpos : ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict B, w z ≠ 0)
    (hfin : ∀ᵐ ω ∂P, ((μ ω).withDensity w) B ≠ ∞)
    (hk : ∀ᵐ ω ∂P, κ ω = normalizedRestriction ((μ ω).withDensity w) B)
    (ν : Measure (Ω × ℂ)) (hac : P ⊗ₘ κ ≪ ν)
    {p : Ω → ℂ → Prop} (hp : ∀ᵐ x ∂ν, p x.1 x.2) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ B → p ω z := by
  have hroot : ∀ᵐ ω ∂P, ∀ᵐ z ∂κ ω, p ω z :=
    Measure.ae_ae_of_ae_compProd (hac.ae_le hp)
  filter_upwards [hroot, hpos, hfin, hk] with ω hroot hpos hfin hk
  rw [hk, normalizedRestriction] at hroot
  have hres : ∀ᵐ z ∂((μ ω).withDensity w).restrict B, p ω z :=
    (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr hfin)).mp hroot
  rw [restrict_withDensity hB] at hres
  have hres' := (ae_withDensity_iff hw).mp hres
  apply (ae_restrict_iff' hB).mp
  filter_upwards [hres', hpos] with z hz hzp
  exact hz hzp

/-- Rooted transfer on a countable measurable cover gives the property at
almost every point of the original random measure. -/
theorem ae_ae_of_rooted_weighted_cover
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (κ : ℕ → Kernel Ω ℂ) [∀ n, IsSFiniteKernel (κ n)]
    (B : ℕ → Set ℂ) (hB : ∀ n, MeasurableSet (B n))
    (hcover : ∀ z, ∃ n, z ∈ B n) (w : ℕ → ℂ → ℝ≥0∞)
    (hw : ∀ n, Measurable (w n))
    (hpos : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (B n), w n z ≠ 0)
    (hfin : ∀ n, ∀ᵐ ω ∂P, ((μ ω).withDensity (w n)) (B n) ≠ ∞)
    (hk : ∀ n, ∀ᵐ ω ∂P,
      κ n ω = normalizedRestriction ((μ ω).withDensity (w n)) (B n))
    (ν : ℕ → Measure (Ω × ℂ)) (hac : ∀ n, P ⊗ₘ κ n ≪ ν n)
    {p : Ω → ℂ → Prop} (hp : ∀ n, ∀ᵐ x ∂ν n, p x.1 x.2) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, p ω z := by
  have hlocal : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ B n → p ω z := fun n =>
    ae_ae_of_rooted_weighted_restriction P μ (κ n) (B n) (hB n) (w n) (hw n)
      (hpos n) (hfin n) (hk n) (ν n) (hac n) (hp n)
  filter_upwards [ae_all_iff.mpr hlocal] with ω hω
  filter_upwards [ae_all_iff.mpr hω] with z hz
  obtain ⟨n, hn⟩ := hcover z
  exact hz n hn

open Classical in
/-- A common rooted pinch-frequency bound on a countable cover transfers to
almost every point of the LQG measure. The rooted laws and the common rate
remain explicit hypotheses. -/
theorem ae_ae_pinchBlockDensity_of_rooted_weighted_cover
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [SFinite P]
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ)
    (U T Q' Q : Set ℂ) (M q : ℝ)
    (κ : ℕ → Kernel Ω ℂ) [∀ n, IsSFiniteKernel (κ n)]
    (B : ℕ → Set ℂ) (hB : ∀ n, MeasurableSet (B n))
    (hcover : ∀ z, ∃ n, z ∈ B n) (w : ℕ → ℂ → ℝ≥0∞)
    (hw : ∀ n, Measurable (w n))
    (hpos : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (B n), w n z ≠ 0)
    (hfin : ∀ n, ∀ᵐ ω ∂P, ((μ ω).withDensity (w n)) (B n) ≠ ∞)
    (hk : ∀ n, ∀ᵐ ω ∂P,
      κ n ω = normalizedRestriction ((μ ω).withDensity (w n)) (B n))
    (ν : ℕ → Measure (Ω × ℂ)) (hac : ∀ n, P ⊗ₘ κ n ≪ ν n)
    (hp : ∀ n, ∀ᵐ x ∂ν n, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEvent (μ x.1) (D x.1) U T Q' Q M ((2 : ℝ)⁻¹ ^ k) x.2}.ncard : ℝ)) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, ∀ᶠ N : ℕ in atTop, q * N ≤
      ({k : ℕ | N + 1 ≤ k ∧ k ≤ 2 * N ∧
        pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ k) z}.ncard : ℝ) :=
  ae_ae_of_rooted_weighted_cover P μ κ B hB hcover w hw hpos hfin hk ν hac hp

#print axioms ae_ae_of_rooted_weighted_restriction
#print axioms ae_ae_of_rooted_weighted_cover
#print axioms ae_ae_pinchBlockDensity_of_rooted_weighted_cover

end HarmonicBalls
