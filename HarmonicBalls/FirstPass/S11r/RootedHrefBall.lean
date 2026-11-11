import HarmonicBalls.FirstPass.S11r.RootedBallMetric
import HarmonicBalls.FirstPass.S11i.Step8HrefBall

/-!
# The `href` field of `Step8UnitBallInputs2`, for the ball decoders

For a valid ball `p` (root disc `ball c r`, decoder disc `ball c (2r)`), the kernel `ballKernel p` and the metric `ballMetric p`
of HzoomUnitBallDecoders.lean satisfy the rooted covariance for the decoded pair, by
`rootedCertificateEventualCovarianceStmt_of_given_families` (with `κ = kernelF`, `mD = metricCont`, the clauses `kernelF_clause`
and `metricCont_clause20`), transferred from `windowMetric` to `ballMetric` by `ae_ballMetric_decodedRoot_eq`. Then
`href_discNormalized_doubledDisc_finiteKernel` (Step8HrefBall.lean) with `m₀ = m = ballMetric p` and `H = univ` gives `href`.

The binders are those of `rootedCertificateEventualCovarianceStmt_of_given_families` for this model, except: `hLenC` is derived
(`hLenC_of_dilation_data`), `hExist0`/`hExistα` are derived from `μ`, and `hmG`/`hκG` are derived for the ball decoders. The
dilation data `G`, `G0` and the decoder hypotheses on `Dμ`, `Dd` remain named binders (GAP 2 items; see the report).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11c FirstPassS11ai
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders
open HarmonicBalls.FirstPassS11rRootedBallMetric

namespace HarmonicBalls.FirstPassS11rRootedHrefBall

/-- **The `href` field for the ball decoders, for one whole-plane model.** The rooted reference observations avoid the
failure set of the ball kernel `ballKernel p` and the ball metric `ballMetric p` at the frequency `q`. -/
theorem href_ballMetric_of_inputs {γ ξ q η M : ℝ}
    (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{0}) (hB : HarmonicBalls.BirkhoffPointwiseErgodic.{0})
    (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{0} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (μ : Ω → Measure ℂ) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) (p : ℚ × ℚ × ℚ) (hp : ValidBall p)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (Ostar U V W T Q' Q : Set ℂ)
    (hCont : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (hFdef : ∀ L : ModConstTestPairings (Set.univ : Set ℂ),
      FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F)
    (hDμ : Measurable Dμ) (hDd : ∀ x y : ℂ, Measurable fun L : ModConstTestPairings (Set.univ : Set ℂ) => Dd L x y)
    (hIdγ : S11n.LQGCanonicalIdentificationStmt.{0} γ ξ γ Dμ Dd) (hPos : LQGMeasureSquarePositiveFrozen.{0})
    (G : Set S11n.CanonSpace) (hGm : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (hGreg : ∀ L ∈ G, IsEuclideanLengthMetric (Dd L))
    (G0 : Set S11n.CanonSpace) (hG0 : MeasurableSet G0) (hG0a : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G0)
    (hinv : dilOp ⁻¹' G0 = G0)
    (hstep : ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Dμ (dilOp L) = ENNReal.ofReal a • (Dμ L).map (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp L) x y = b * Dd L (((1 / 2 : ℝ) : ℂ) * x) (((1 / 2 : ℝ) : ℂ) * y))
    (hA10 : ∀ μ' : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarked P γ hC hcirc μ')
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{0}) (hLenFr : LQGMetricLengthUnivFrozen.{0})
    (hFieldFr : LQGMetricFieldAxiomsUnivFrozen.{0}) (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hUax : LQGMetricSatisfiesAxiomsUnivFrozen.{0}) (hXi : LQGMetricExponentPositive)
    (hComp : WeylMetricCompositionContinuousOuterFrozen)
    (hCC : ∀ z : ℂ, LQGMeasureCoordChange P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hνex : ∀ z : ℂ, LQGMeasureExistence P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hq : q = (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (ballCen p) (ballRad p) → ∀ᵐ ω ∂P,
      campbellReferenceObs γ 0 (ball (ballCen p) (2 * ballRad p)) (hC ω) z ∉
        ReferenceNullS11i.refBadWindowSet
          (localCertSeq (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) Ostar U V W T Q' Q η M) q := by
  obtain ⟨hr, hcl, hout, h0⟩ := validBall_facts hp
  have : IsFiniteKernel (kernelF hγ0 hγ2 hK p) := kernelF_isFiniteKernel hγ0 hγ2 hK p hp
  have hTr : ∀ z : ℂ, IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z) :=
    fun z => isWholePlaneGFF_translatedPairing
      (fun Q C K => HarmonicBalls.wholePlaneGFFAffineInvariance_derived Q C K) hG z
  have hLenC := hLenC_of_dilation_data hCM γ 0 hG hTr (c₁ := ballCen p) (r₁ := ballRad p)
    (ball (ballCen p) (ballRad p)) G hGm hGa Dd hGreg
  have hEx : LQGMeasureExistence P γ 0 hC hcirc := fun _ _ _ _ => ⟨μ, hμ⟩
  have hCov := FirstPassS11ai.rootedCertificateEventualCovarianceStmt_of_given_families hCM hγ0 hγ2 (lqgQ_pos hγ0) h𝔇
    hG (c₁ := ballCen p) (c₂ := ballCen p) (r₁ := ballRad p) (r₂ := 2 * ballRad p) (hr₂ := by linarith)
      hcl h0 hout (ball (ballCen p) (ballRad p)) Ostar U V W T Q' Q η M hCont hU (fun ℓ => kernelF hγ0 hγ2 hK p ℓ)
    (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p) (kernelF_clause hγ0 hγ2 hK p hp) (metricCont_clause20 hγ0 hγ2 hR 𝔇 h𝔇 p hp)
    Dμ Dd hDμ hDd hIdγ hPos G hGm hGa hGreg G0 hG0 hG0a hinv hstep hEx hEx hA10 hProf hLenFr hFieldFr hRootFr hUax hR hK hXi
    hComp hCC hνex hLenC
  have hae := ae_ballMetric_decodedRoot_eq hG hfr hγ0 hγ2 (lqgQ_pos hγ0) hR h𝔇 p hp
  have hCov' := rootedCert_congr_dR
    (dR' := FirstPassS11at.decodedRootMetric (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) γ 0 hC) hCov
    (by filter_upwards [hae] with z hz; filter_upwards [hz] with ω hω; exact hω.symm)
  have hnull := HarmonicBalls.FirstPassS11iStep8HrefBall.href_discNormalized_doubledDisc_finiteKernel hCM hB hG
    (ballCen p) (validBall_facts hp).1 hF hCont hU Dμ Dd hFdef (kernelF hγ0 hγ2 hK p) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p)
    hCov' (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) Set.univ MeasurableSet.univ (by simp) (fun _ _ => rfl)
  rw [hq]
  exact hnull

end HarmonicBalls.FirstPassS11rRootedHrefBall

