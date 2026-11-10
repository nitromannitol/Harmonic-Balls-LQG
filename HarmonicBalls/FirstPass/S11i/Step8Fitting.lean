import Mathlib
import HarmonicBalls.FirstPass.S11asLocal
import HarmonicBalls.FirstPass.S11ah.Cutoff
import HarmonicBalls.FirstPass.S11i.Step8Locality

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
* `ae_fitting_eventually_of_decoders`: the eventual form. `hDp` is not available for all radii: the internal-metric
  clause of `LocalMetricReplacementStmt` gives, for each centre `z` in `ball c₂ r₂` and a.e. `ω`, the plain identity
  only for `r ≤ s0(z, ω)` (`FirstPassS11iStep8Locality.eventually_eqOn_of_internal`). The conclusion holds for every
  centre `z` in the local domain and all large `n` (`certScale n → 0`). The decoder is assumed nonnegative (replace
  it by `max m 0` at the consumer; this keeps the `ENNReal` clause).

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

/-- **Restriction of a scalar mass identity.** If `ν` and `ofReal a • μ` agree after restriction to a ball `B`,
they agree after restriction to any `K ⊆ B`. -/
theorem restrict_eq_scalar_of_subset {ν μ : Measure ℂ} {a : ℝ} {B K : Set ℂ} (hsub : K ⊆ B)
    (h : ν.restrict B = ENNReal.ofReal a • μ.restrict B) :
    ν.restrict K = (ENNReal.ofReal a • μ).restrict K := by
  calc ν.restrict K = (ν.restrict B).restrict K := (Measure.restrict_restrict_of_subset hsub).symm
    _ = (ENNReal.ofReal a • μ.restrict B).restrict K := by rw [h]
    _ = ENNReal.ofReal a • μ.restrict K := by
        rw [Measure.restrict_smul, Measure.restrict_restrict_of_subset hsub]
    _ = (ENNReal.ofReal a • μ).restrict K := by rw [Measure.restrict_smul]

/-- **Eventual almost-sure fitting identity (Step 8 `hfit`, eventual form).** Inputs, for a.e. `ω`: the mass clause
`hκ` on `ball c₂ r₂`; the decoder `m` is nonnegative (`hm0`); the physical metric `Dα ω` is nonnegative (`hDnn`) and
a Euclidean length metric (`hLen`, Fact 2.2 I, see `FirstPass/S11i/Step8LengthMetric.lean`); and the decoded metric
is a positive multiple of the internal metric of `Dα ω` on the local domain (`hint`, the clause of
`LocalMetricReplacementStmt` with `p` over `ball c₂ r₂ ×ˢ ball c₂ r₂`). Locality
(`eventually_eqOn_of_internal`) then gives, for each centre `z` in the local domain, the plain identity
`m = b · Dα` on `closedBall z (7 s) ²` for all `s ≤ s0(z, ω)`. Hence the fitting identity holds at every centre
`z ∈ ball c₂ r₂` for all large `n`; `certScale n → 0`. -/
theorem ae_fitting_eventually_of_decoders {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (α₀ η M : ℝ) (Ostar U' V W T Q' Q : Set ℂ) (c₂ : ℂ) (r₂ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (μα : Ω → Measure ℂ) (Dα : Ω → ℂ → ℂ → ℝ)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (hCC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U' ⊆ closedBall 0 7)
    (hκ : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
      (κ (fun φ => fieldPairing α₀ (hC ω) φ.1)).restrict (ball c₂ r₂) =
        ENNReal.ofReal a • (μα ω).restrict (ball c₂ r₂))
    (hm0 : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ m (fun φ => fieldPairing α₀ (hC ω) φ.1) x y)
    (hDnn : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ Dα ω x y)
    (hLen : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dα ω))
    (hint : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ x ∈ ball c₂ r₂, ∀ y ∈ ball c₂ r₂,
      ENNReal.ofReal (m (fun φ => fieldPairing α₀ (hC ω) φ.1) x y) =
        ENNReal.ofReal b * internalMetric (Dα ω) (ball c₂ r₂) x y) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball c₂ r₂, ∀ᶠ n in atTop,
      (FirstPassS11i.CertificateEvent (κ (fun φ => fieldPairing α₀ (hC ω) φ.1))
          (m (fun φ => fieldPairing α₀ (hC ω) φ.1)) Ostar U' V W T Q' Q η M (certScale n) z ↔
        FirstPassS11i.CertificateEvent (μα ω) (Dα ω) Ostar U' V W T Q' Q η M (certScale n) z) := by
  filter_upwards [hκ, hm0, hDnn, hLen, hint] with ω hκω hm0ω hDnnω hLenω hintω
  obtain ⟨a, ha, hκeq⟩ := hκω
  obtain ⟨b, hb, hintb⟩ := hintω
  have hopen : IsOpen (ball c₂ r₂) := Metric.isOpen_ball
  intro z hz
  obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.1 hopen z hz
  obtain ⟨s0, hs0, hEq⟩ := FirstPassS11iStep8Locality.eventually_eqOn_of_internal hLenω hDnnω hopen hz hb
    hm0ω hintb
  have hT : Tendsto certScale atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hpos : (0 : ℝ) < min s0 (ε / 7) := lt_min hs0 (by positivity)
  filter_upwards [hT.eventually (Iio_mem_nhds hpos)] with n hn
  have hn' : certScale n < min s0 (ε / 7) := hn
  have hr : 0 < certScale n := certScale_pos n
  have hsmall : certScale n ≤ s0 := le_of_lt (lt_of_lt_of_le hn' (min_le_left _ _))
  have h7 : 7 * certScale n < ε := by
    have := lt_of_lt_of_le hn' (min_le_right _ _)
    linarith
  have hsub : closedBall z (7 * certScale n) ⊆ ball c₂ r₂ :=
    (Metric.closedBall_subset_ball h7).trans hεsub
  have hμ := restrict_eq_scalar_of_subset hsub hκeq
  exact certificateEvent_of_restrict_scalar_at _ _ _ _ Ostar U' V W T Q' Q η M (certScale n) z ha hb hCC hU hr
    hμ (hEq (certScale n) hr hsmall)

end HarmonicBalls.FirstPassS11iStep8Fitting

#print axioms HarmonicBalls.FirstPassS11iStep8Fitting.certificateEvent_of_restrict_scalar_at
#print axioms HarmonicBalls.FirstPassS11iStep8Fitting.ae_fitting_of_decoders
#print axioms HarmonicBalls.FirstPassS11iStep8Fitting.ae_fitting_eventually_of_decoders
