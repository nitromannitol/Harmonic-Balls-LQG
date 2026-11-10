import HarmonicBalls.FirstPass.S11r.RootedCovGiven
import HarmonicBalls.FirstPass.S11i.HzoomUnitBallDecoders

/-!
# Rooted covariance inputs for the ball decoders (fp-S11r-n4-instance-gaps, n2)

* GAP 1. `ballMetric p ℓ` (HzoomUnitBallDecoders) is the window metric of `metricCont p` on every observation `ℓ` for which
  its `if`-branch holds (`ballMetric_eq_windowMetric_of_length`). Under the rooted reference law this branch holds for
  almost every root and almost every model: `rootedLengthProperty` gives it from clause (20) of `LocalMetricReplacementStmt`
  (`metricCont_clause20`). So the decoded root metrics of `ballMetric` and of `windowMetric (ball c (2r)) (metricCont p)`
  agree almost surely (`ae_ballMetric_decodedRoot_eq`), and the rooted covariance statement is invariant under such an
  almost-sure change of the decoded metric (`rootedCert_congr_dR`).
* CHECK (3). `kernelF_clause` is the rooted kernel clause (second conjunct of `LocalMeasureKernelStmt`, `hκG`) for `kernelF`,
  taken from the second conjunct of `FirstPassS11ahFinite.exists_finite_localMeasureKernel`; it is identical clause by clause.
* GAP 2 (length clause). `hLenC_of_dilation_data`: the guarded length clause `hLenC` of
  `rootedCertificateEventualCovarianceStmt_of_given_families` follows from the dilation data `G` (`hGm`, `hGa`, `hGreg`) by
  `FirstPassS11at.ae_isEuclideanLengthMetric_shiftedCanon`; it needs no further input.
-/

universe u

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11c FirstPassS11ai
open HarmonicBalls.FirstPassS11iStep8Exhaustion HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders

namespace HarmonicBalls.FirstPassS11rRootedBallMetric

/-- On an observation where the `if`-branch of `ballMetric` holds, `ballMetric` is the window metric of `metricCont`. -/
theorem ballMetric_eq_windowMetric_of_length {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (p : ℚ × ℚ × ℚ)
    (ℓ : FirstPassS11ahFinite.LocalObs (ballCen p) (2 * ballRad p))
    (h : FirstPassS11ah.IsLengthMetricOn (ball (ballCen p) (2 * ballRad p))
      (FirstPassS11ah.decoderOn (ball (ballCen p) (2 * ballRad p)) (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p ℓ))) :
    ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p ℓ =
      FirstPassS11at.windowMetric (ball (ballCen p) (2 * ballRad p)) (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p) ℓ := by
  unfold ballMetric
  simp only [h, ↓reduceIte]
  funext x y
  unfold FirstPassS11at.windowMetric FirstPassS11ah.decoderOn
  by_cases hxy : (x, y) ∈ ball (ballCen p) (2 * ballRad p) ×ˢ ball (ballCen p) (2 * ballRad p) <;> simp [hxy]

/-- Clause (20) of `LocalMetricReplacementStmt` for the continuous decoder `metricCont p` of a valid ball, at the root window
`ball (ballCen p) (ballRad p)` and the decoder disc `ball (ballCen p) (2 * ballRad p)`. -/
theorem metricCont_clause20 {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (p : ℚ × ℚ × ℚ) (hp : ValidBall p) :
    ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ᵐ z ∂(volume.restrict (ball (ballCen p) (ballRad p))), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
        ∀ q : ↥(ball (ballCen p) (2 * ballRad p) ×ˢ ball (ballCen p) (2 * ballRad p) : Set (ℂ × ℂ)),
          ENNReal.ofReal (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p (campbellReferenceObs γ α (ball (ballCen p) (2 * ballRad p))
            (hC ω) z).2 q) =
            ENNReal.ofReal b * internalMetric
              (fun a v => (weylScaling (𝔇 (hC ω)) ξ
                (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) a v).toReal)
              (ball (ballCen p) (2 * ballRad p)) q.1.1 q.1.2 := by
  obtain ⟨hr, hcl, hout, h0⟩ := validBall_facts hp
  intro α hα Ω _ P _ hC hcirc hG
  have hspec := (Classical.choose_spec (hR (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p) hγ0 hγ2 hr
    (by linarith) hcl hout h0 𝔇 h𝔇)).2.2
  unfold metricCont
  simp only [hp, ↓reduceDIte]
  exact hspec α hα Ω P hC hcirc hG

/-- **GAP 1.** For a valid ball, the decoded rooted metric of `ballMetric` agrees almost surely with the decoded rooted metric
of the window metric of `metricCont`, under the rooted reference law at the insertion `α₀ < Q_γ`. -/
theorem ae_ballMetric_decodedRoot_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    (hfr : HarmonicBalls.RootedPhysicalMetricContinuousAtInsertionFrozen.{0})
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{0} γ ξ c₁ c₂ r₁ r₂)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇) (p : ℚ × ℚ × ℚ) (hp : ValidBall p) :
    ∀ᵐ z ∂(volume.restrict (ball (ballCen p) (ballRad p))), ∀ᵐ ω ∂P,
      FirstPassS11at.decodedRootMetric (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) γ α₀ hC z ω =
        FirstPassS11at.decodedRootMetric
          (FirstPassS11at.windowMetric (ball (ballCen p) (2 * ballRad p)) (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p))
          γ α₀ hC z ω := by
  obtain ⟨hr, hcl, -, h0⟩ := validBall_facts hp
  have hLen := FirstPassS11ah.rootedLengthProperty hG h𝔇 hfr hγ0 hγ2 hα hcl h0 (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p)
    (metricCont_clause20 hγ0 hγ2 hR 𝔇 h𝔇 p hp α₀ hα _ P hC hcirc hG)
  filter_upwards [hLen] with z hz
  filter_upwards [hz] with ω hω
  exact ballMetric_eq_windowMetric_of_length hγ0 hγ2 hR 𝔇 h𝔇 p _ hω

/-- The rooted covariance statement is invariant under an almost-sure change of the decoded root metric. -/
theorem rootedCert_congr_dR {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ}
    {A Ostar U V W T Q' Q : Set ℂ} {η M : ℝ} {Adm : ℂ → ℝ → (ℂ → ℝ) → Prop} {rR : ℂ → ℝ}
    {μR : ℂ → Ω → Measure ℂ} {dR dR' : ℂ → Ω → ℂ → ℂ → ℝ} {Dμ : _} {Dd : _}
    (h : FirstPassS11at.RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ A Ostar U V W T Q' Q η M
      Adm rR μR dR Dμ Dd)
    (heq : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, dR z ω = dR' z ω) :
    FirstPassS11at.RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ A Ostar U V W T Q' Q η M
      Adm rR μR dR' Dμ Dd := by
  filter_upwards [h, heq] with z hz hzeq
  intro hzA b u hAdm
  filter_upwards [hz hzA b u hAdm, hzeq] with ω hω hωeq
  obtain ⟨n₀, hn⟩ := hω
  refine ⟨n₀, fun n hn' h1 h2 h3 => ?_⟩
  have key := hn n hn' h1 h2 h3
  rw [hωeq] at key
  exact key

/-- **CHECK (3), finiteness.** The kernel `kernelF` of a valid decoder disc is a finite kernel. -/
theorem kernelF_isFiniteKernel {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{u} γ c₁ c₂ r₁ r₂)
    (p : ℚ × ℚ × ℚ) (hp : ValidBall p) : IsFiniteKernel (kernelF hγ0 hγ2 hK p) := by
  unfold kernelF
  simp only [hp, ↓reduceDIte]
  exact (Classical.choose_spec (FirstPassS11ahFinite.exists_finite_localMeasureKernel
    (hK (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p)) hγ0 hγ2 (validBall_facts hp).1
    (by linarith [(validBall_facts hp).1]) (validBall_facts hp).2.1 (validBall_facts hp).2.2.1
    (validBall_facts hp).2.2.2)).1

/-- **CHECK (3), the rooted kernel clause `hκG`.** The kernel `kernelF` of a valid decoder disc satisfies the rooted kernel
clause of `LocalMeasureKernelStmt` (its second conjunct) at the root window `ball (ballCen p) (ballRad p)`. -/
theorem kernelF_clause {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{u} γ c₁ c₂ r₁ r₂)
    (p : ℚ × ℚ × ℚ) (hp : ValidBall p) :
    ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ᵐ z ∂(volume.restrict (ball (ballCen p) (ballRad p))), ∀ μz : Ω → Measure ℂ,
        IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage α (hcirc ω))
          (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) μz →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
          (kernelF hγ0 hγ2 hK p (campbellReferenceObs γ α (ball (ballCen p) (2 * ballRad p)) (hC ω) z).2).restrict
              (ball (ballCen p) (2 * ballRad p)) =
            ENNReal.ofReal a • (μz ω).restrict (ball (ballCen p) (2 * ballRad p)) := by
  intro α hα Ω _ P _ hC hcirc hG
  unfold kernelF
  simp only [hp, ↓reduceDIte]
  exact (Classical.choose_spec (FirstPassS11ahFinite.exists_finite_localMeasureKernel
    (hK (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p)) hγ0 hγ2 (validBall_facts hp).1
    (by linarith [(validBall_facts hp).1]) (validBall_facts hp).2.1 (validBall_facts hp).2.2.1
    (validBall_facts hp).2.2.2)).2.2 α hα Ω P hC hcirc hG

/-- **GAP 2, length clause.** The guarded length clause `hLenC` of `rootedCertificateEventualCovarianceStmt_of_given_families`
is produced by the dilation data `G` of the decoders: almost every shifted canonical field is a Euclidean length metric
under `Dd`, since `G` is measurable, carries the canonical field of `h^{α₀}` almost surely, and `Dd` is Euclidean on `G`. -/
theorem hLenC_of_dilation_data {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{u}) (γ α₀ : ℝ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    (hTr : ∀ z : ℂ, IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    {c₁ : ℂ} {r₁ : ℝ} (A : Set ℂ) (G : Set S11n.CanonSpace) (hGm : MeasurableSet G)
    (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ)
    (hGreg : ∀ L ∈ G, IsEuclideanLengthMetric (Dd L)) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u →
      ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dd (FirstPassS11at.shiftedCanon γ hC hcirc z u ω)) := by
  refine ae_of_all _ fun z => fun _ b u hAdm => ?_
  exact FirstPassS11at.ae_isEuclideanLengthMetric_shiftedCanon hCM γ hh hTr z u hAdm.2.2.2.1 hAdm.2.2.2.2.1
    hAdm.2.2.2.2.2.1 G hGm hGa Dd hGreg

end HarmonicBalls.FirstPassS11rRootedBallMetric

#print axioms HarmonicBalls.FirstPassS11rRootedBallMetric.ae_ballMetric_decodedRoot_eq
#print axioms HarmonicBalls.FirstPassS11rRootedBallMetric.rootedCert_congr_dR
#print axioms HarmonicBalls.FirstPassS11rRootedBallMetric.kernelF_clause
#print axioms HarmonicBalls.FirstPassS11rRootedBallMetric.kernelF_isFiniteKernel
#print axioms HarmonicBalls.FirstPassS11rRootedBallMetric.hLenC_of_dilation_data
