# Translated disc finite-source Green potential

`HarmonicBalls.Proofs.Potential.TranslatedDiscFiniteSourceLaplacian` proves
`integrableOn_translatedDisc_greenPotential` for a finite source concentrated
a.e. on the closed disc and `hasLaplacian_translatedDisc_greenPotential` for
a finite source concentrated a.e. on the open disc. The latter has no atom,
growth, or continuity restriction. Its sign is `ΔGν = -ν`, in the sense of
`HasLaplacian`; the totalized Green kernel and its diagonal convention are
preserved by `Section6.greenPotential_translate`.

The source measure is pushed forward by `z ↦ z - c`. Translation preserves
planar volume and takes the origin disc to the disc centered at `c`. A test
function is pulled back by `z ↦ z + c`; smoothness, compact support, support
in the disc, and the Laplacian are transported. The origin-disc finite-source
result then supplies the distributional identity. The potential-theoretic
infrastructure uses work of Leonardo Bonanno.

The following consumer examples were checked with Lean after building the
module. The first specializes exactly to the origin-disc result; the second
uses an atom at an arbitrary point of an arbitrary disc.

```lean
import HarmonicBalls.Proofs.Potential.TranslatedDiscFiniteSourceLaplacian
open MeasureTheory Metric Set
open HarmonicBalls

example {ν : Measure ℂ} [IsFiniteMeasure ν] {R : ℝ} (hR : 0 < R)
    (hν : ∀ᵐ y ∂ν, y ∈ ball (0 : ℂ) R) :
    HasLaplacian (greenPotential (ball 0 R) ν) 0 ν (ball 0 R) :=
  hasLaplacian_translatedDisc_greenPotential hR hν

example {c a : ℂ} {R : ℝ} (hR : 0 < R) (ha : a ∈ ball c R) :
    HasLaplacian (greenPotential (ball c R) (Measure.dirac a)) 0
      (Measure.dirac a) (ball c R) := by
  apply hasLaplacian_translatedDisc_greenPotential hR
  exact (ae_dirac_iff measurableSet_ball).2 ha
```

Both declarations print only `propext`, `Classical.choice`, and `Quot.sound`.
The source has no `sorry`, `axiom`, `admit`, `native_decide`, or heartbeat
override. The general-domain Riesz theorem and E51 representatives are separate
obligations; no numbered result is closed here.
