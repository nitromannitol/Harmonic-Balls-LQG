import HarmonicBalls.Defs.GFF

/-!
# First-pass frozen input: existence of the whole-plane GFF (fp-S11r, owner n2)

One EXTERNAL fact, used by the realization lemma `hmodel_at_gamma` (FirstPass/S11r.lean, the model hypothesis of
Lemma 11.13 in FirstPass/S11i/CertificateCanonical.lean). It is general Gaussian free field theory, not specific to
this paper. A `def ... : Prop`, never an axiom.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- FIRST-PASS FROZEN. Existence of the whole-plane Gaussian free field (EXTERNAL, general): for every universe `u` there
are a probability space `Ω : Type u`, a pairing `hC` and a circle-average process `hcirc` with `IsWholePlaneGFF P hC hcirc`,
that is a centred Gaussian field with covariance `wholePlaneCov` (`log (max(|z|,1) max(|w|,1) / |z-w|)`, normalised so that
the average on the unit circle vanishes), whose circle averages are a.s. continuous in `(r, z) ∈ (0, ∞) × ℂ`.
Source: standard; locator pending (whole-plane GFF as in Duplantier-Sheffield arXiv:0808.1560, cited by
`Proposed/LQG.lean`; Berestycki-Powell arXiv:2404.16642, whole-plane GFF section). Used by: `hmodel_at_gamma`
(FirstPass/S11r.lean), hence the model hypothesis `hmodel` of `certificate_canonical_pos` (FirstPass/S11i/CertificateCanonical.lean).
PENDING TRUTH CHECK (operator to route). -/
def WholePlaneGFFExistsFrozen : Prop :=
  ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc

end HarmonicBalls
