import Mathlib
import HarmonicBalls.FirstPass.S11i.Step8LocalCompat

/-!
# Almost-sure local-to-physical window limit (Step 8, fp-S11i-11-13f, n3)

Combines the deterministic compatibility `tendsto_localWindow_iff_unitScale` (dc64724) with the almost-sure fitting
identity and the almost-sure local good set. The fitting identity is the `fitting_eq` field of `CertificateIdentification`
(`FirstPass/S11i/Identification.lean:33`), taken here as the explicit hypothesis `hfit` for the decoded observation
`obs ω = fun φ => fieldPairing α₀ (hC ω) φ.1` of the target field. The local good set is the complement of
`refBadWindowSet` for the local certificate sequence (`ReferenceNullS11i`, `ReferenceNull.lean:29`), pulled back along the
marked observation `campbellMarkedObs`. The root set `U` must lie in the local domain `ball c₂ r₂` (exhaustion later).
No new input.
-/

universe u

namespace HarmonicBalls.FirstPassS11iStep8PhysicalWindow

open MeasureTheory Filter Topology Set Metric
open HarmonicBalls HarmonicBalls.S11c HarmonicBalls.FirstPassS11iStep8Transfer
open HarmonicBalls.FirstPassS11iStep8LocalCompat FirstPassS11ah FirstPassS11ai

/-- **Almost-sure physical window limit on a local good set.** -/
theorem ae_unitScale_of_local_good {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {c₂ : ℂ} {r₂ : ℝ} (α₀ : ℝ) (U : Set ℂ) (hU : U ⊆ ball c₂ r₂) (q : ℝ)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (Ostar U' V W T Q' Q : Set ℂ) (η M : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (μα : Ω → Measure ℂ) (Dα : Ω → ℂ → ℂ → ℝ)
    (hfit : ∀ᵐ ω ∂P, ∀ (z : ℂ) (n : ℕ), closedBall z (cutRadius n) ⊆ ball c₂ r₂ →
      (FirstPassS11i.CertificateEvent (κ (fun φ => fieldPairing α₀ (hC ω) φ.1))
          (m (fun φ => fieldPairing α₀ (hC ω) φ.1)) Ostar U' V W T Q' Q η M (certScale n) z ↔
        FirstPassS11i.CertificateEvent (μα ω) (Dα ω) Ostar U' V W T Q' Q η M (certScale n) z))
    (hGood : ∀ᵐ ω ∂P, ∀ᵐ z ∂(μα ω), z ∈ U →
      campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z ∉
        HarmonicBalls.ReferenceNullS11i.refBadWindowSet (localCertSeq κ m Ostar U' V W T Q' Q η M) q) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μα ω), z ∈ U →
      Tendsto (fun N : ℕ => unitScaleWindowFreq (μα ω) (Dα ω) Ostar U' V W T Q' Q η M z N) atTop (𝓝 q) := by
  filter_upwards [hfit, hGood] with ω hf hg
  filter_upwards [hg] with z hz hzU
  have hzD : z ∈ ball c₂ r₂ := hU hzU
  have hloc : Tendsto (fun N : ℕ => HarmonicBalls.ReferenceNullS11i.refWindowAverage
      (localCertSeq κ m Ostar U' V W T Q' Q η M) N (z, fun φ => fieldPairing α₀ (hC ω) φ.1)) atTop (𝓝 q) := by
    by_contra hnot
    refine hz hzU ?_
    show ¬ Tendsto _ _ _
    exact hnot
  exact (tendsto_localWindow_iff_unitScale κ m Ostar U' V W T Q' Q η M
    (fun φ => fieldPairing α₀ (hC ω) φ.1) (μα ω) (Dα ω) q
    (eventually_closedBall_cutRadius_subset hzD) (fun n hn => hf z n hn)).1 hloc

end HarmonicBalls.FirstPassS11iStep8PhysicalWindow

#print axioms HarmonicBalls.FirstPassS11iStep8PhysicalWindow.ae_unitScale_of_local_good
