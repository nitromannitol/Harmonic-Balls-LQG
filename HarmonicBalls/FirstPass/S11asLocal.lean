import HarmonicBalls.FirstPass.S11asWeyl
import HarmonicBalls.FirstPass.S11asAssembly
import HarmonicBalls.FirstPass.S11aq
import HarmonicBalls.FirstPass.S11al
import HarmonicBalls.FirstPass.S11i.CertDilate

/-!
# Locality of the rooted decoded pair up to positive constants (fp-S11as, round 8)

The decoders `Dμ`, `Dd` of `LQGCanonicalIdentificationStmt` identify the LQG measure and metric of a model only up to
positive constants, and these constants depend on `ω`: `μ ω = ofReal a • Dμ (L ω)` with `a = a(ω) > 0`. Two rooted
decoded pairs at the same root `z` (for two admissible shifts `u`, `u'` with `u - u'` vanishing on the window) therefore
agree on the certificate window only up to positive constants. The certificate event is invariant under such constants
(rule [C43] of `S11i/CertDilate.lean` at scale `R = 1`), so the exact equalities of `hLocμ` / `hLocd`
(`S11ai/RootedPhysical.lean`, `rooted_covariance_window`) may be weakened to the constant form proved here.

Contents (all proved, no hypothesis beyond those named in the statements):
* `certificateEvent_smul_iff`: `CertificateEvent (a • μ) (b * D) ↔ CertificateEvent μ D` (`a, b > 0`);
* `restrict_eq_ofReal_div_of_smul_eq`: two normalising constants of restricted measures combine to a positive ratio;
* `ae_restrict_decoded_of_weyl`: a.s. restriction locality of the decoded measures from the restriction locality of the LQG
  measures (`hWeyl`) and the a.s. decoder identities (`hdec`, `hdec'`, i.e. `LQGCanonicalIdentificationStmt` in the mass
  part);
* `ae_decoded_restrict_scalar`: the same with `hWeyl` supplied by the Weyl locality `lqgMeasure_restrict_eq_of_shift`;
* `certificateEvent_of_restrict_scalar`, `ae_certificateEvent_iff`: certificate equivalence from mass and metric
  locality up to positive constants on `closedBall 0 (7 r)`.

NOT PROVED HERE: the metric locality `hloc`'s metric part for the decoded metrics `Dd (L_u)` and `Dd (L_u')`. The LQG
metric has no Weyl locality lemma in the repository yet (`LQGMetricFieldAxioms` clause IV, `Proposed/LQG.lean:216`, is a
coordinate-change rule, and its Weyl factor is constant only for shifts constant on the window).
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls

namespace FirstPassS11asLocal

/-- **Scalar invariance of the certificate event.** Scaling the mass by `a > 0` and the metric by `b > 0` does not change
the certificate event at `(r, z)`. This is the case `R = 1` of the dilation covariance rule `certificateEvent_dilate_iff`
(rule [C43]): the constants `a` and `b` cancel in every strict inequality, by homogeneity of the internal metric, the
set distance and the Green potential. -/
theorem certificateEvent_smul_iff (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ)
    (η M r : ℝ) (z : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    FirstPassS11i.CertificateEvent (ENNReal.ofReal a • μ) (fun u v => b * D u v) Ostar U V W T Q' Q η M r z ↔
      FirstPassS11i.CertificateEvent μ D Ostar U V W T Q' Q η M r z := by
  have h := HarmonicBalls.FirstPassS11iCertDilate.certificateEvent_dilate_iff μ D Ostar U V W T Q' Q η M r z
    (R := 1) (a := a) (b := b) one_pos ha hb
  simpa using h

/-- **Two normalising constants.** If `c' • ν'` and `c • ν` agree on `S` (with `c = ofReal a`, `c' = ofReal a'`, `a, a' > 0`),
then `ν'` and `(a / a') • ν` agree on `S`. -/
theorem restrict_eq_ofReal_div_of_smul_eq {ν ν' : Measure ℂ} {S : Set ℂ} {a a' : ℝ} (ha' : 0 < a')
    (h : (ENNReal.ofReal a' • ν').restrict S = (ENNReal.ofReal a • ν).restrict S) :
    ν'.restrict S = (ENNReal.ofReal (a / a') • ν).restrict S := by
  rw [Measure.restrict_smul, Measure.restrict_smul] at h
  have hc0 : ENNReal.ofReal a' ≠ 0 := (ENNReal.ofReal_pos.2 ha').ne'
  have hct : ENNReal.ofReal a' ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [FirstPassS11asAssembly.eq_inv_smul_of_smul_eq hc0 hct h, smul_smul, Measure.restrict_smul,
    ENNReal.ofReal_div_of_pos ha', div_eq_mul_inv, mul_comm]

/-- **A.s. restriction locality of decoded measures.** Let `μ, μ'` be the LQG measures and `ν, ν'` their decoders, with the
a.s. decoder identities `μ ω = ofReal a(ω) • ν ω`, `μ' ω = ofReal a'(ω) • ν' ω` (positive `a, a'`, the mass part of
`LQGCanonicalIdentificationStmt`). If the LQG measures agree on `S` (`hWeyl`), then the decoded measures agree on `S`
up to a positive constant. -/
theorem ae_restrict_decoded_of_weyl {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (μ μ' ν ν' : Ω → Measure ℂ) (S : Set ℂ)
    (hWeyl : ∀ᵐ ω ∂P, (μ' ω).restrict S = (μ ω).restrict S)
    (hdec : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ μ ω = ENNReal.ofReal a • ν ω)
    (hdec' : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ μ' ω = ENNReal.ofReal a • ν' ω) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, 0 < c ∧ (ν' ω).restrict S = (ENNReal.ofReal c • ν ω).restrict S := by
  filter_upwards [hWeyl, hdec, hdec'] with ω hw hd hd'
  obtain ⟨a, ha, h1⟩ := hd
  obtain ⟨a', ha', h2⟩ := hd'
  refine ⟨a / a', div_pos ha ha', restrict_eq_ofReal_div_of_smul_eq ha' ?_⟩
  rw [← h1, ← h2]
  exact hw

/-- **A.s. decoded mass locality from the Weyl shift.** Two LQG measures of fields `hcirc` and `hcirc' = hcirc + circle averages
of v`, with `v = 0` on `S`, agree on `S` (`FirstPassS11asWeyl.lqgMeasure_restrict_eq_of_shift`); their decoders then agree on
`S` up to a positive constant. -/
theorem ae_decoded_restrict_scalar {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α : ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ} {μ μ' ν ν' : Ω → Measure ℂ} {v : ℂ → ℝ} (hv : Continuous v)
    (hshift : ∀ ω r x, hcirc' ω r x = hcirc ω r x + Real.circleAverage v x r)
    (hcont : ∀ᵐ ω ∂P, ∀ n : ℕ, Continuous (fieldCircleAverage α (hcirc ω) (dyadicScale n)))
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hμ' : IsLQGMeasureOfField P γ α hcirc' μ')
    {S : Set ℂ} (hS : MeasurableSet S) (hv0 : ∀ x ∈ S, v x = 0)
    (hdec : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ μ ω = ENNReal.ofReal a • ν ω)
    (hdec' : ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧ μ' ω = ENNReal.ofReal a • ν' ω) :
    ∀ᵐ ω ∂P, ∃ c : ℝ, 0 < c ∧ (ν' ω).restrict S = (ENNReal.ofReal c • ν ω).restrict S :=
  ae_restrict_decoded_of_weyl μ μ' ν ν' S
    (FirstPassS11asWeyl.lqgMeasure_restrict_eq_of_shift hv hshift hcont hμ hμ' hS hv0) hdec hdec'

/-- **Certificate equivalence up to positive constants (deterministic).** If the masses agree on `closedBall 0 (7 r)` up to a
positive constant `a`, and the metrics agree there up to a positive constant `b`, then the certificate events at `(r, 0)`
agree. -/
theorem certificateEvent_of_restrict_scalar (μ μ' : Measure ℂ) (D D' : ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ)
    (η M r : ℝ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7) (hr : 0 < r)
    (hμ : μ.restrict (closedBall 0 (7 * r)) = (ENNReal.ofReal a • μ').restrict (closedBall 0 (7 * r)))
    (hD : Set.EqOn (Function.uncurry D) (Function.uncurry (fun x y => b * D' x y))
      (closedBall 0 (7 * r) ×ˢ closedBall 0 (7 * r))) :
    FirstPassS11i.CertificateEvent μ D Ostar U V W T Q' Q η M r 0 ↔
      FirstPassS11i.CertificateEvent μ' D' Ostar U V W T Q' Q η M r 0 := by
  refine Iff.trans (FirstPassS11i.certificateEvent_congr_of_eqOn_closedBall (U := U) hC hr hD) ?_
  refine Iff.trans (FirstPassS11aq.certificateEvent_measure_congr (fun x y => b * D' x y) Ostar U V W T Q' Q η M r 0
    hr hU hμ) ?_
  exact certificateEvent_smul_iff μ' D' Ostar U V W T Q' Q η M r 0 ha hb

/-- **A.s. certificate equivalence from local constant-locality.** The interface for `hCov` of n1: if for almost every `ω` the
physical pair `(μ ω, D ω)` and the canonical pair `(μ' ω, D' ω)` agree on the window `closedBall 0 (7 r)` up to positive
constants (mass and metric), then the certificate events at `(r, 0)` agree almost surely. -/
theorem ae_certificateEvent_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (μ μ' : Ω → Measure ℂ) (D D' : Ω → ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ) (η M r : ℝ)
    (hC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7) (hr : 0 < r)
    (hloc : ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      (μ ω).restrict (closedBall 0 (7 * r)) = (ENNReal.ofReal a • μ' ω).restrict (closedBall 0 (7 * r)) ∧
      Set.EqOn (Function.uncurry (D ω)) (Function.uncurry (fun x y => b * D' ω x y))
        (closedBall 0 (7 * r) ×ˢ closedBall 0 (7 * r))) :
    ∀ᵐ ω ∂P, (FirstPassS11i.CertificateEvent (μ ω) (D ω) Ostar U V W T Q' Q η M r 0 ↔
      FirstPassS11i.CertificateEvent (μ' ω) (D' ω) Ostar U V W T Q' Q η M r 0) := by
  filter_upwards [hloc] with ω hω
  obtain ⟨a, b, ha, hb, hμω, hDω⟩ := hω
  exact certificateEvent_of_restrict_scalar (μ ω) (μ' ω) (D ω) (D' ω) Ostar U V W T Q' Q η M r ha hb hC hU hr
    hμω hDω

end FirstPassS11asLocal
