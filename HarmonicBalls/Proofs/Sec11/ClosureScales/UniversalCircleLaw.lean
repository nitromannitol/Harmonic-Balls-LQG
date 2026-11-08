import HarmonicBalls.Proofs.Sec11.ClosureScales.UniversalRealization
import HarmonicBalls.Proofs.Sec5.GaussianProcessLaw

/-!
# Lemma l:r6-transfer, step 5 (lite): the universal law of the circle averages on `J`

Source: `notes/sec11-proof/sec11-proof-r7.tex`, Lemma `l:r6-transfer` (lines 284-640), the identity `c_*P = λ` for
the canonical profile. The canonical profile of a whole-plane GFF is the measurable modification of the circle
averages from `UniversalRealization.lean`. Its restriction to `J = (0,∞) × ℂ` is a random element of `J → ℝ` with
the product σ-algebra. This file proves that the law of this restriction does not depend on the GFF model: two
whole-plane GFFs, in arbitrary universes, give the same law.

The proof uses the identical distribution of finite families of circle averages from
`IsWholePlaneGFF.identDistrib_finite_observables` (Sec5, `GaussianProcessLaw.lean`), and the finite-cylinder π-system
generating the product σ-algebra (Mathlib, `measurableCylinders`).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology ProbabilityTheory

universe u₁ u₂

/-- The restriction of a canonical profile to the index set `J`: a random element of `J → ℝ`, `J` as a subtype. -/
def circleProfileOnJ (f : CanonicalProfile) : ↥circleIndexSet → ℝ :=
  fun p => f.1 p.1

theorem measurable_circleProfileOnJ : Measurable circleProfileOnJ := by
  refine Measurable.of_eval fun p => ?_
  exact (measurable_pi_apply (p.1 : ℝ × ℂ)).comp measurable_subtype_coe

/-- A point of `J` gives an admissible circle-average observable (its radius is positive). -/
lemma circle_observable_admissible {p : ℝ × ℂ} (hp : p ∈ circleIndexSet) :
    GFFObservable.IsAdmissible (GFFObservable.circle p.1 p.2) :=
  hp.1

/-- **Universal law of the circle averages on `J`.** Let `(P₁, hC₁, hcirc₁)` and `(P₂, hC₂, hcirc₂)` be whole-plane
GFFs in arbitrary universes, and let `c₁`, `c₂` be measurable canonical profiles of them (agreeing with the circle
averages on `J` almost surely). Then the restrictions of the canonical profiles to `J` have the same law. -/
theorem IsWholePlaneGFF.map_circleProfileOnJ_eq
    {Ω₁ : Type u₁} {Ω₂ : Type u₂} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {hC₁ : Ω₁ → (ℂ → ℝ) → ℝ} {hcirc₁ : Ω₁ → ℝ → ℂ → ℝ}
    {hC₂ : Ω₂ → (ℂ → ℝ) → ℝ} {hcirc₂ : Ω₂ → ℝ → ℂ → ℝ}
    (h₁ : IsWholePlaneGFF P₁ hC₁ hcirc₁) (h₂ : IsWholePlaneGFF P₂ hC₂ hcirc₂)
    {c₁ : Ω₁ → CanonicalProfile} {c₂ : Ω₂ → CanonicalProfile}
    (hc₁ : Measurable c₁) (hc₂ : Measurable c₂)
    (hc₁J : ∀ᵐ ω ∂P₁, ∀ p ∈ circleIndexSet, (c₁ ω).1 p = hcirc₁ ω p.1 p.2)
    (hc₂J : ∀ᵐ ω ∂P₂, ∀ p ∈ circleIndexSet, (c₂ ω).1 p = hcirc₂ ω p.1 p.2) :
    P₁.map (fun ω => circleProfileOnJ (c₁ ω)) = P₂.map (fun ω => circleProfileOnJ (c₂ ω)) := by
  have hm₁ : Measurable fun ω => circleProfileOnJ (c₁ ω) := measurable_circleProfileOnJ.comp hc₁
  have hm₂ : Measurable fun ω => circleProfileOnJ (c₂ ω) := measurable_circleProfileOnJ.comp hc₂
  refine ext_of_generate_finite (measurableCylinders _) generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders ?_ ?_
  · intro t ht
    obtain ⟨s, S, hS, rfl⟩ := (mem_measurableCylinders t).mp ht
    have hcyl : MeasurableSet (cylinder (α := fun _ : ↥circleIndexSet => ℝ) s S) :=
      MeasurableSet.cylinder s hS
    rw [Measure.map_apply hm₁ hcyl, Measure.map_apply hm₂ hcyl]
    -- the finite family of admissible circle-average observables indexed by `s`
    let v : ↥s → GFFObservable.Admissible :=
      fun i => ⟨GFFObservable.circle i.1.1.1 i.1.1.2, circle_observable_admissible i.1.2⟩
    have hid := IsWholePlaneGFF.identDistrib_finite_observables h₁ h₂ v
    have hae₁ : (fun ω => circleProfileOnJ (c₁ ω)) ⁻¹' cylinder s S =ᵐ[P₁]
        (fun ω (i : ↥s) => hcirc₁ ω i.1.1.1 i.1.1.2) ⁻¹' S := by
      filter_upwards [hc₁J] with ω hω
      have hfun : (fun i : ↥s => circleProfileOnJ (c₁ ω) i.1) =
          fun i : ↥s => hcirc₁ ω i.1.1.1 i.1.1.2 :=
        funext fun i => hω i.1.1 i.1.2
      apply propext
      show (fun i : ↥s => circleProfileOnJ (c₁ ω) i.1) ∈ S ↔
        (fun i : ↥s => hcirc₁ ω i.1.1.1 i.1.1.2) ∈ S
      rw [hfun]
    have hae₂ : (fun ω => circleProfileOnJ (c₂ ω)) ⁻¹' cylinder s S =ᵐ[P₂]
        (fun ω (i : ↥s) => hcirc₂ ω i.1.1.1 i.1.1.2) ⁻¹' S := by
      filter_upwards [hc₂J] with ω hω
      have hfun : (fun i : ↥s => circleProfileOnJ (c₂ ω) i.1) =
          fun i : ↥s => hcirc₂ ω i.1.1.1 i.1.1.2 :=
        funext fun i => hω i.1.1 i.1.2
      apply propext
      show (fun i : ↥s => circleProfileOnJ (c₂ ω) i.1) ∈ S ↔
        (fun i : ↥s => hcirc₂ ω i.1.1.1 i.1.1.2) ∈ S
      rw [hfun]
    calc P₁ ((fun ω => circleProfileOnJ (c₁ ω)) ⁻¹' cylinder s S)
        = P₁ ((fun ω (i : ↥s) => hcirc₁ ω i.1.1.1 i.1.1.2) ⁻¹' S) := measure_congr hae₁
      _ = P₂ ((fun ω (i : ↥s) => hcirc₂ ω i.1.1.1 i.1.1.2) ⁻¹' S) := hid.measure_mem_eq hS
      _ = P₂ ((fun ω => circleProfileOnJ (c₂ ω)) ⁻¹' cylinder s S) := (measure_congr hae₂).symm
  · rw [Measure.map_apply hm₁ MeasurableSet.univ, Measure.map_apply hm₂ MeasurableSet.univ]
    simp

end HarmonicBalls
