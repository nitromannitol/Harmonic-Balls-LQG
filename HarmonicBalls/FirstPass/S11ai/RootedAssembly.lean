import HarmonicBalls.FirstPass.S11ai.RootedInstance
import HarmonicBalls.FirstPass.S11ai.RootedTransfer
import HarmonicBalls.FirstPass.S11at

/-!
# Steps 6-7 assembly: the covariance clause from q1's decoded wrapper (fp-S11ai-11-13-steps-6-7e)

Operator note 2026-11-10 13:02 UTC (tasks/n1.md): the named covariance hypothesis `hCov` of `RootedInstance.lean` is replaced by the
application of q1's wrapper `FirstPassS11at.rootedCertificateEventualCovarianceStmt_decoded_of_rootedLocalIdent`
(`HarmonicBalls/FirstPass/S11at.lean`, the binder `hOuter` and `hProf` replace the old `hWin` and `hBridge`).

What is proved here: `ae_quantum_bad_mass_eq_zero_of_rootedLocalIdent`, the entry of the chain with the covariance clause
discharged by the wrapper. Its hypotheses are exactly the wrapper's binders (with the Adm/rR instantiation below), the
coding identity `hG` (Step 7, a named hypothesis), and the Step 8 data of `ae_quantum_bad_mass_eq_zero_of_identification`.

Instantiations (not hypotheses): `Adm := AdmissibleRootShift α₀`, `rR := rootRadius`, `mD`-decoder through
`FirstPassS11at.windowMetric (ball c₂ r₂) mD`, `hTr` from `isWholePlaneGFF_translatedPairing` (affine invariance `hAff`), and the
admissibility clauses `hAdmReg`, `hAdmPos`, `hc1`, `hrR`, proved from the definition of `AdmissibleRootShift`
and from `h0`.

Named hypotheses (not discharged here): `hG` (Step 7 coding identity; `RootedTransfer.hG_of_scaleOne` is NOT used because it
needs `ScaleOneAll`, FLAG 1 of `RootedInstance.lean`), `hOuter` (`closedBall c₂ r₂ ⊆ ball 0 1`, the Lemma 11.13 geometry layer),
`hProf`, `hRLI`, `hRLIm` (n2's rooted local identification, pending its theorem names), and the frozen Props of the wrapper.
-/

universe u

namespace FirstPassS11ai

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls
open HarmonicBalls.S11c

/-- **Steps 6-7 entry with q1's decoded covariance wrapper.** Same conclusion as `ae_quantum_bad_mass_eq_zero_of_identification`
(bad quantum mass vanishes), with `hCov` supplied by `FirstPassS11at.rootedCertificateEventualCovarianceStmt_decoded_of_rootedLocalIdent`
and the decoded rooted pair `decodedRootMeasure κ`, `decodedRootMetric (FirstPassS11at.windowMetric (ball c₂ r₂) mD)`. -/
theorem ae_quantum_bad_mass_eq_zero_of_rootedLocalIdent
    (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : HarmonicBalls.LocalCampbellMarkedRestrictionFrozen.{u})
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hAff : AffineInvarianceAll Ω)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (h0 : (0 : ℂ) ∉ closedBall c₂ r₂) (A : Set ℂ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    {ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (mD : (FirstPassS11at.WinTest (ball c₂ r₂) → ℝ) → C(↥(ball c₂ r₂ ×ˢ ball c₂ r₂), ℝ))
    (c : ℕ → (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) → ℝ)
    (hSeq : ∀ (n : ℕ) (z : ℂ) (ℓ : {φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ),
      c n (z, ℓ) = FirstPassS11ah.localCert (ball c₂ r₂) κ (FirstPassS11at.windowMetric (ball c₂ r₂) mD)
        Ostar U V W T Q' Q η M n ℓ z)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (hG : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
        (FirstPassS11i.CertificateEvent
            (Dμ (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            (Dd (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            Ostar U V W T Q' Q η M 1 0 ↔
          ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))) ∈ F))
    {S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ))}
    (hS : MeasurableSet S)
    (hSfail : ∀ x, x ∈ S ↔ x.1 ∈ A ∧ ¬ Tendsto (fun N : ℕ => ReferenceNullS11i.refWindowAverage c N x) atTop
      (𝓝 (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal))
    (hCont : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    -- binders of `rootedCertificateEventualCovarianceStmt_decoded_of_rootedLocalIdent` (q1, S11at.lean:1070)
    (G : Set S11n.CanonSpace) (hGm : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (hGreg : ∀ L ∈ G, IsEuclideanLengthMetric (Dd L))
    (G0 : Set S11n.CanonSpace) (hG0 : MeasurableSet G0) (hG0a : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G0)
    (hinv : dilOp ⁻¹' G0 = G0)
    (hstep : ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Dμ (dilOp L) = ENNReal.ofReal a • (Dμ L).map (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp L) x y = b * Dd L (((1 / 2 : ℝ) : ℂ) * x) (((1 / 2 : ℝ) : ℂ) * y))
    (Uj Dj : ℕ → Set ℂ)
    (κj : (j : ℕ) → ({φ : ℂ → ℝ // IsTestFunction (Dj j) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (mj : (j : ℕ) → (FirstPassS11at.WinTest (Dj j) → ℝ) → C(↥(Dj j ×ˢ Dj j), ℝ))
    (hDj : ∀ j, Dj j ⊆ ball c₂ r₂) (hDjO : ∀ j, IsOpen (Dj j))
    (hExist0 : LQGMeasureExistence P γ 0 hC hcirc) (hExistα : LQGMeasureExistence P γ α₀ hC hcirc)
    (hA10 : ∀ μ' : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarked P γ hC hcirc μ')
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{u}) (hOuter : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1)
    (hκ : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (FirstPassS11at.rootedCircleField α₀ γ hcirc z) μz → ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
          ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂))
    (hκj : ∀ j, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Uj j → ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (FirstPassS11at.rootedCircleField α₀ γ hcirc z) μz → ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κj j (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2).restrict (Dj j) =
          ENNReal.ofReal a • (μz ω).restrict (Dj j))
    (hRLI : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u →
      ∃ j : ℕ, z ∈ Uj j ∧ ∀ᵐ ω ∂P, ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ closedBall z ρ ⊆ Dj j ∧
        ((κj j (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2).map (fun w : ℂ => w - z)).restrict
            (closedBall 0 ρ) =
          ENNReal.ofReal c • (Dμ (FirstPassS11at.shiftedCanon γ hC hcirc z u ω)).restrict (closedBall 0 ρ))
    (hDwD : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂),
        ENNReal.ofReal (mD (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (FirstPassS11at.rootedWeylMetric 𝔇 ξ α₀ γ hC z ω) (ball c₂ r₂) p.1.1 p.1.2)
    (hDwj : ∀ j, ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Uj j → ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(Dj j ×ˢ Dj j),
        ENNReal.ofReal (mj j (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (FirstPassS11at.rootedWeylMetric 𝔇 ξ α₀ γ hC z ω) (Dj j) p.1.1 p.1.2)
    (hLenFr : LQGMetricLengthUnivFrozen.{u}) (hFieldFr : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{u})
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hRLIm : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u →
      ∃ j : ℕ, z ∈ Uj j ∧ ∀ᵐ ω ∂P, ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧ closedBall z ρ ⊆ Dj j ∧
        ∀ x ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ closedBall (0 : ℂ) ρ,
          FirstPassS11at.windowMetric (Dj j) (mj j) (campbellReferenceObs γ α₀ (Dj j) (hC ω) z).2 (x + z) (y + z) =
            c * Dd (FirstPassS11at.shiftedCanon γ hC hcirc z u ω) x y)
    (hLenC : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u →
      ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dd (FirstPassS11at.shiftedCanon γ hC hcirc z u ω))) :
    ∀ᵐ ω ∂P, ∫⁻ z in ball c₁ r₁,
      S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 := by
  -- admissibility clauses of the wrapper, from the definition of `AdmissibleRootShift`
  have hAdmReg : ∀ (z : ℂ) (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u →
      ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0 :=
    fun _ _ _ h => ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  have hAdmPos : ∀ (z : ℂ) (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u → 0 < b :=
    fun _ _ _ h => h.1
  have hc1 : ball c₁ r₁ ⊆ ball c₂ r₂ := ball_subset_closedBall.trans hsub
  have hTr : ∀ z : ℂ, IsWholePlaneGFF P (translatedPairing hC hcirc z) (translatedCircle hcirc z) :=
    fun z => isWholePlaneGFF_translatedPairing hAff hh z
  -- the root radius is positive on `ball c₁ r₁`, since `0 ∉ closedBall c₂ r₂`
  have hrR : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → 0 < rootRadius z := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℂ)) measurableSet_ball] with z hz _
    have hzc : z ∈ closedBall c₂ r₂ := ball_subset_closedBall (hsub (ball_subset_closedBall hz))
    have hz0 : z ≠ 0 := fun h => h0 (h ▸ hzc)
    exact rootRadius_pos (norm_pos_iff.2 hz0)
  -- Step 6: the eventual covariance clause, from q1's decoded wrapper
  have hCov := FirstPassS11at.rootedCertificateEventualCovarianceStmt_decoded_of_rootedLocalIdent
    (γ := γ) (α₀ := α₀) (ξ := ξ) (𝔇 := 𝔇) (hCM := hCM) (hC := hC) (hcirc := hcirc) (hh := hh) (hTr := hTr)
    (c₁ := c₁) (c₂ := c₂) (r₁ := r₁) (r₂ := r₂) (A := A) (Ostar := Ostar) (U := U) (V := V) (W := W) (T := T)
    (Q' := Q') (Q := Q) (η := η) (M := M) (hCont := hCont) (hU := hU) (Adm := AdmissibleRootShift α₀)
    (hAdmReg := hAdmReg) (rR := rootRadius) (κ := κ) (mD := mD) (Dμ := Dμ) (Dd := Dd) (G := G) (hG := hGm)
    (hGa := hGa) (hGreg := hGreg) (G0 := G0) (hG0 := hG0) (hG0a := hG0a) (hinv := hinv) (hstep := hstep)
    (Uj := Uj) (Dj := Dj) (κj := κj) (mj := mj) (hDj := hDj) (hDjO := hDjO) (hc1 := hc1) (hAdmPos := hAdmPos)
    (hrR := hrR) (hExist0 := hExist0) (hExistα := hExistα) (hA10 := hA10) (hProf := hProf) (hOuter := hOuter)
    (hκ := hκ) (hκj := hκj) (hRLI := hRLI) (hDwD := hDwD) (hDwj := hDwj) (hLenFr := hLenFr) (hFieldFr := hFieldFr)
    (hRootFr := hRootFr) (h𝔇 := h𝔇) (hγ0 := hγ0) (hγ2 := hγ2) (hα := hα) (hRLIm := hRLIm) (hLenC := hLenC)
  exact ae_quantum_bad_mass_eq_zero_of_identification hCM hB hCamp hγ0 hγ2 hα hh hμ hE hr₁ hr₂ hsub h0 A Ostar U V W T Q' Q η M
    κ (FirstPassS11at.windowMetric (ball c₂ r₂) mD) c hSeq Dμ Dd hF hCov hG hS hSfail

end FirstPassS11ai

#print axioms FirstPassS11ai.ae_quantum_bad_mass_eq_zero_of_rootedLocalIdent
