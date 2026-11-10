import Mathlib
import HarmonicBalls.FirstPass.S11asLocal
import HarmonicBalls.FirstPass.S11ah.Cutoff

/-!
# Centred fitting identity of the decoded certificate (Step 8, fp-S11i-11-13f, n3)

The fitting identity `hfit` of `ae_unitScale_of_ball` (`FirstPass/S11i/Step8Exhaustion.lean`) compares the
certificate event of a decoded pair `(κ(obs), m(obs))` with that of the physical pair `(μα, Dα)` at every
centre `z` and every cutoff `closedBall z (cutRadius n)` inside the local domain `ball c₂ r₂`.
The centre-0 lemma `FirstPassS11asLocal.certificateEvent_of_restrict_scalar` only treats centre `0`.

* `certificateEvent_of_restrict_scalar_at`: the same statement at an arbitrary centre `z`, with the mass
  identity and the metric identity required on `closedBall z (7 r)` (deterministic; the proof is the centre-0 proof
  with `certificateEvent_measure_congr` and `certificateEvent_congr_of_eqOn_closedBall` used at centre `z`).
* `ae_fitting_of_decoders`: the almost-sure fitting identity from the mass clause of `LocalMeasureKernelStmt`
  (`S11r/Frozen.lean`) and a plain metric identity `hDp` on every `closedBall z (7 r) ⊆ ball c₂ r₂`.

Gap (not closed here): `LocalMetricReplacementStmt` (`S11r/LocalMetricReplacement.lean`) gives the decoded metric as
`b · internalMetric (weylScaling 𝔇 …) (ball c₂ r₂)`, the INTERNAL metric of the ball, whereas `CertificateEvent`
(`S11i/Certificate.lean`) uses the plain metric `setDist D` and `internalMetric D O` on sets inside the cutoff ball.
So `hDp` (plain identity on the cutoff ball) is NOT supplied by the frozen decoder statements. It is kept as a hypothesis.
-/

namespace HarmonicBalls.FirstPassS11iStep8Fitting

open MeasureTheory Filter Topology Set Metric
open FirstPassS11ah

/-- **Centred scale-and-metric transfer of the certificate event.** Centre-`z` version of
`FirstPassS11asLocal.certificateEvent_of_restrict_scalar`: if the masses agree on `closedBall z (7 r)` up to a
positive constant `a` and the metrics agree there up to a positive constant `b`, the certificate events at
`(r, z)` agree. Source: Lemma 11.13 (Armstrong-Kuusi-Mourrat certificate, Step 2 locality). -/
theorem certificateEvent_of_restrict_scalar_at (μ μ' : Measure ℂ) (D D' : ℂ → ℂ → ℝ)
    (Ostar U V W T Q' Q : Set ℂ) (η M r : ℝ) (z : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7) (hr : 0 < r)
    (hμ : μ.restrict (closedBall z (7 * r)) = (ENNReal.ofReal a • μ').restrict (closedBall z (7 * r)))
    (hD : Set.EqOn (Function.uncurry D) (Function.uncurry (fun x y => b * D' x y))
      (closedBall z (7 * r) ×ˢ closedBall z (7 * r))) :
    FirstPassS11i.CertificateEvent μ D Ostar U V W T Q' Q η M r z ↔
      FirstPassS11i.CertificateEvent μ' D' Ostar U V W T Q' Q η M r z := by
  refine Iff.trans (FirstPassS11i.certificateEvent_congr_of_eqOn_closedBall (U := U) hC hr hD) ?_
  refine Iff.trans (FirstPassS11aq.certificateEvent_measure_congr (fun x y => b * D' x y) Ostar U V W T Q' Q η M r z
    hr hU hμ) ?_
  exact FirstPassS11asLocal.certificateEvent_smul_iff μ' D' Ostar U V W T Q' Q η M r z ha hb

/-- **Almost-sure fitting identity of a decoded pair (Step 8 `hfit`).** Inputs: the mass clause `hκ` (for almost every
`ω`, the decoded measure `κ(obs ω)` restricted to the local domain `ball c₂ r₂` is a positive multiple of `μα ω`
restricted there; this is the mass clause of `LocalMeasureKernelStmt`), and the plain metric identity `hDp` (for
almost every `ω` there is `b > 0` with `m(obs ω) = b · Dα ω` on `closedBall z (7 r) ²` whenever `closedBall z (7 r)`
lies in the local domain). The conclusion is the fitting identity at every centre and every cutoff radius
`cutRadius n = 7 · certScale n` whose cutoff ball lies in the local domain. -/
theorem ae_fitting_of_decoders {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (α₀ η M : ℝ) (Ostar U' V W T Q' Q : Set ℂ) (c₂ : ℂ) (r₂ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (μα : Ω → Measure ℂ) (Dα : Ω → ℂ → ℂ → ℝ)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (hCC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U' ⊆ closedBall 0 7)
    (hκ : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (κ (fun φ => fieldPairing α₀ (hC ω) φ.1)).restrict (ball c₂ r₂) =
        ENNReal.ofReal a • (μα ω).restrict (ball c₂ r₂))
    (hDp : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ (z : ℂ) (r : ℝ), 0 < r → closedBall z (7 * r) ⊆ ball c₂ r₂ →
      Set.EqOn (Function.uncurry (m (fun φ => fieldPairing α₀ (hC ω) φ.1)))
        (Function.uncurry (fun x y => b * Dα ω x y)) (closedBall z (7 * r) ×ˢ closedBall z (7 * r))) :
    ∀ᵐ ω ∂P, ∀ (z : ℂ) (n : ℕ), closedBall z (cutRadius n) ⊆ ball c₂ r₂ →
      (FirstPassS11i.CertificateEvent (κ (fun φ => fieldPairing α₀ (hC ω) φ.1))
          (m (fun φ => fieldPairing α₀ (hC ω) φ.1)) Ostar U' V W T Q' Q η M (certScale n) z ↔
        FirstPassS11i.CertificateEvent (μα ω) (Dα ω) Ostar U' V W T Q' Q η M (certScale n) z) := by
  filter_upwards [hκ, hDp] with ω hκω hDω
  obtain ⟨a, ha, hκeq⟩ := hκω
  obtain ⟨b, hb, hDeq⟩ := hDω
  intro z n hzn
  have hr : 0 < certScale n := by unfold certScale; positivity
  have hsub : closedBall z (7 * certScale n) ⊆ ball c₂ r₂ := hzn
  have hμ : (κ (fun φ => fieldPairing α₀ (hC ω) φ.1)).restrict (closedBall z (7 * certScale n)) =
      (ENNReal.ofReal a • μα ω).restrict (closedBall z (7 * certScale n)) := by
    calc (κ (fun φ => fieldPairing α₀ (hC ω) φ.1)).restrict (closedBall z (7 * certScale n))
        = ((κ (fun φ => fieldPairing α₀ (hC ω) φ.1)).restrict (ball c₂ r₂)).restrict
            (closedBall z (7 * certScale n)) := (Measure.restrict_restrict_of_subset hsub).symm
      _ = (ENNReal.ofReal a • (μα ω).restrict (ball c₂ r₂)).restrict (closedBall z (7 * certScale n)) := by
          rw [hκeq]
      _ = ENNReal.ofReal a • (μα ω).restrict (closedBall z (7 * certScale n)) := by
          rw [Measure.restrict_smul, Measure.restrict_restrict_of_subset hsub]
      _ = (ENNReal.ofReal a • μα ω).restrict (closedBall z (7 * certScale n)) := by
          rw [Measure.restrict_smul]
  exact certificateEvent_of_restrict_scalar_at _ _ _ _ Ostar U' V W T Q' Q η M (certScale n) z ha hb hCC hU hr
    hμ (hDeq z (certScale n) hr hsub)

end HarmonicBalls.FirstPassS11iStep8Fitting

#print axioms HarmonicBalls.FirstPassS11iStep8Fitting.certificateEvent_of_restrict_scalar_at
#print axioms HarmonicBalls.FirstPassS11iStep8Fitting.ae_fitting_of_decoders
