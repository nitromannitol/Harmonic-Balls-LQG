import HarmonicBalls.FirstPass.Frozen.S8c
import HarmonicBalls.FirstPass.S11i.SingularWeyl

/-! # The Weyl relation off the origin, derived (FIRST-PASS fp-8-2-hWeyl-derived, worker z6)

The frozen Prop `LocalLQGInsertionWeylOffOrigin` (`FirstPass/Frozen/S8c.lean`) is derived here from the
definitions of the GFF circle averages and of the LQG vague limits. No LQG measure existence, no coordinate
change and no Cameron-Martin theorem is used. The argument is Steps 1-7 of ChatGPT Pro chat 219
(`notes/fp-gaps/CHATGPT-219-hb-8-2-R9-hL1-hWeyl-PRO.md` §1.3).

* Steps 1-4 (this file): on one common conull set, the vague limits of `lam` (insertion `0`) and `μ` (insertion `α₀`)
  satisfy `∫ f dlam = ∫ f ‖·‖^(γ α₀) dμ` for every continuous compactly supported `f` vanishing near `0`. The
  approximation identity and the passage to the limit are `SingularWeyl.integral_test_eq`.
* Steps 5-6 (deterministic, Radon measures): `HarmonicBalls.FirstPassS8cWeyl.eq_withDensity_offOrigin_of_integral_eq`
  (`FirstPass/S8c/WeylOffOriginRadon.lean`).
* Step 7: the assembly, with one `∀ᵐ ω` binder (`localLQGInsertionWeylOffOrigin_derived`).
-/

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- Steps 1-4 of the derivation of the Weyl relation off the origin (Duplantier-Sheffield 2011, vague limits
of the LQG approximations). Almost surely, for every continuous compactly supported `f : ℂ → ℝ` vanishing on a ball
about `0`, the no-insertion measure `lam ω` and the insertion-`α₀` measure `μ ω` satisfy
`∫ f d(lam ω) = ∫ f(z) ‖z‖^(γ α₀) d(μ ω)`. The two vague limits are taken for one common conull set. -/
theorem ae_integral_eq_rpow_of_isLQGMeasureOfField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {γ α₀ : ℝ} {μ lam : Ω → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hlam : IsLQGMeasureOfField P γ 0 hcirc lam) :
    ∀ᵐ ω ∂P, ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → (∃ δ > 0, ∀ z : ℂ, ‖z‖ < δ → f z = 0) →
      ∫ z, f z ∂(lam ω) = ∫ z, f z * ‖z‖ ^ (γ * α₀) ∂(μ ω) := by
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  have hlam' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage 0 (hcirc ω)) (lam ω) := hlam
  filter_upwards [hμ', hlam', SingularWeyl.ae_measurable_dyadic_circleAverage hGFF] with ω hμω hlamω hmeas
  intro f hf hfs hfδ'
  obtain ⟨δ, hδ, hfδ⟩ := hfδ'
  -- the density `‖z‖^(γ α₀)` is the Weyl factor of `-α₀` off the origin, and both vanish near the origin
  have hpt : ∀ z : ℂ, f z * ‖z‖ ^ (γ * α₀) = f z * SingularWeyl.weylFactor γ (-α₀) z := by
    intro z
    by_cases hz : ‖z‖ < δ
    · simp [hfδ z hz]
    · have hpos : 0 < ‖z‖ := lt_of_lt_of_le hδ (not_lt.1 hz)
      congr 1
      rw [SingularWeyl.weylFactor, Real.rpow_def_of_pos hpos]
      congr 1
      ring
  have hinv : ∀ z : ℂ, SingularWeyl.weylFactor γ (-α₀) z * SingularWeyl.weylFactor γ α₀ z = 1 := by
    intro z
    rw [SingularWeyl.weylFactor, SingularWeyl.weylFactor, ← Real.exp_add]
    convert Real.exp_zero using 2
    ring
  have hlhs : ∀ z : ℂ, f z * SingularWeyl.weylFactor γ (-α₀) z * SingularWeyl.weylFactor γ α₀ z = f z := by
    intro z
    rw [mul_assoc, hinv z, mul_one]
  have hcont : Continuous (fun z => f z * SingularWeyl.weylFactor γ (-α₀) z) :=
    SingularWeyl.continuous_mul_weylFactor hf hδ hfδ
  have hcs : HasCompactSupport (fun z => f z * SingularWeyl.weylFactor γ (-α₀) z) := hfs.mul_right
  have hgz : ∀ z : ℂ, ‖z‖ < δ → f z * SingularWeyl.weylFactor γ (-α₀) z = 0 := fun z hz => by
    simp [hfδ z hz]
  -- Step 3 and Step 4: the approximation identity and the two vague limits, for the test function
  -- `f · weylFactor γ (-α₀)`
  have key := SingularWeyl.integral_test_eq (γ := γ) (α := α₀) (δ := δ)
    (hg := fun r z => fieldCircleAverage 0 (hcirc ω) r z)
    (hh := fun r z => fieldCircleAverage α₀ (hcirc ω) r z) (m0 := lam ω) (mα := μ ω)
    (fun r z hr hrz => SingularWeyl.fieldCircleAverage_eq_sub hr hrz)
    (fun k => SingularWeyl.measurable_fieldCircleAverage (α := 0) (hc := hcirc ω) (dyadicScale_pos k)
      (hmeas k))
    (fun k => SingularWeyl.measurable_fieldCircleAverage (α := α₀) (hc := hcirc ω) (dyadicScale_pos k)
      (hmeas k))
    hlamω hμω hcont hcs hδ hgz
  calc ∫ z, f z ∂(lam ω)
      = ∫ z, f z * SingularWeyl.weylFactor γ (-α₀) z * SingularWeyl.weylFactor γ α₀ z ∂(lam ω) :=
        integral_congr_ae (Eventually.of_forall fun z => (hlhs z).symm)
    _ = ∫ z, f z * SingularWeyl.weylFactor γ (-α₀) z ∂(μ ω) := key.symm
    _ = ∫ z, f z * ‖z‖ ^ (γ * α₀) ∂(μ ω) :=
        integral_congr_ae (Eventually.of_forall fun z => (hpt z).symm)

end HarmonicBalls
