import Mathlib
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.GFF
import HarmonicBalls.Proofs.Sec11.ClosureScales.UniversalRealization
import HarmonicBalls.Proofs.Sec11.ClosureScales.PalmPairingMeasurable

/-! # Route (A), canonical field model: the Borel reconstruction pairing

For a canonical circle-average sample `c` (an element of `CanonicalProfile`, continuous on the positive-radius index
set) and a smooth compactly supported test function `φ`, the reconstruction pairing is the limit of the dyadic circle
integrals `∫ c(2^{-n}, z) φ(z) d²z`. It is defined
as a limit superior, which equals the limit wherever the limit exists. We prove that it is a Borel function of the
canonical sample, pointwise in the test function and as a map into the raw pairing functionals with the pairing
σ-algebra. The almost-sure identification with the raw pairings of the GFF is not part of this file. -/

noncomputable section

open MeasureTheory Filter Topology Metric Set

namespace HarmonicBalls

/-- The reconstruction pairing of a canonical circle-average sample at a test function:
`R(c)(φ) = limsup_n ∫ c(2^{-n}, z) φ(z) d²z`. -/
def canonicalReconPairing (c : CanonicalProfile) (φ : ℂ → ℝ) : ℝ :=
  limsup (fun n : ℕ => ∫ z : ℂ, c.1 (dyadicScale n, z) * φ z) atTop

/-- Where the dyadic circle integrals converge, the reconstruction pairing is their limit. -/
theorem canonicalReconPairing_eq_of_tendsto {c : CanonicalProfile} {φ : ℂ → ℝ} {L : ℝ}
    (h : Tendsto (fun n : ℕ => ∫ z : ℂ, c.1 (dyadicScale n, z) * φ z) atTop (𝓝 L)) :
    canonicalReconPairing c φ = L :=
  h.limsup_eq

/-- The reconstruction pairing is a Borel function of the canonical sample, for each test function. -/
theorem measurable_canonicalReconPairing {φ : ℂ → ℝ} (hφ : IsTestFunction Set.univ φ) :
    Measurable fun c : CanonicalProfile => canonicalReconPairing c φ := by
  have hF : ∀ n : ℕ, Measurable fun c : CanonicalProfile => ∫ z : ℂ, c.1 (dyadicScale n, z) * φ z := by
    intro n
    have hdyad : 0 < dyadicScale n := by
      unfold dyadicScale
      positivity
    -- continuous in the radial-free variable `z`: the sample is continuous on the positive-radius index set
    have hcont : ∀ c : CanonicalProfile, Continuous fun z : ℂ => c.1 (dyadicScale n, z) := fun c =>
      c.2.comp_continuous (continuous_const.prodMk continuous_id)
        (fun z => Set.mk_mem_prod (Set.mem_Ioi.2 hdyad) (Set.mem_univ z))
    -- measurable in the sample, for each `z`: a coordinate evaluation of the subtype
    have hmeas : ∀ z : ℂ, Measurable fun c : CanonicalProfile => c.1 (dyadicScale n, z) :=
      fun z => (measurable_pi_apply (dyadicScale n, z)).comp measurable_subtype_coe
    -- Carathéodory: jointly measurable
    have hjoint : Measurable
        (Function.uncurry fun (z : ℂ) (c : CanonicalProfile) => c.1 (dyadicScale n, z)) :=
      measurable_uncurry_of_continuous_of_measurable hcont hmeas
    have hφm : Measurable fun p : CanonicalProfile × ℂ => φ p.2 :=
      hφ.1.continuous.measurable.comp measurable_snd
    have hswap : Measurable fun p : CanonicalProfile × ℂ =>
        Function.uncurry (fun (z : ℂ) (c : CanonicalProfile) => c.1 (dyadicScale n, z)) (p.2, p.1) :=
      hjoint.comp measurable_swap
    have hint : StronglyMeasurable fun p : CanonicalProfile × ℂ =>
        Function.uncurry (fun (z : ℂ) (c : CanonicalProfile) => c.1 (dyadicScale n, z)) (p.2, p.1) * φ p.2 :=
      (hswap.mul hφm).stronglyMeasurable
    exact (hint.integral_prod_right').measurable
  unfold canonicalReconPairing
  exact Measurable.limsup hF

/-- The reconstruction as a Borel map into the raw pairing functionals `(ℂ → ℝ) → ℝ` with the pairing σ-algebra:
the Borel reconstruction `R : 𝓐 → 𝓡` of the canonical model. -/
theorem measurable_canonicalReconPairing_map :
    @Measurable CanonicalProfile ((ℂ → ℝ) → ℝ) _ pairingMeasSpace
      (fun c : CanonicalProfile => fun φ : ℂ → ℝ => canonicalReconPairing c φ) :=
  measurable_pairing_of_eval _ fun _ hφ => measurable_canonicalReconPairing hφ

end HarmonicBalls

end
