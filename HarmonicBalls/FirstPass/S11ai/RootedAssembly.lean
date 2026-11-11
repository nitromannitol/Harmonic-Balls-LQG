import HarmonicBalls.FirstPass.S11r.RootedBufferKernel
import HarmonicBalls.FirstPass.S11r.RootedBufferKernelGuarded
import HarmonicBalls.FirstPass.S11ai.RootedInstance
import HarmonicBalls.FirstPass.S11ai.RootedTransfer
import HarmonicBalls.FirstPass.S11at

/-!
# Steps 6-7 assembly: the covariance clause from the decoded wrapper

What is proved here: `ae_quantum_bad_mass_eq_zero_of_rootedLocalIdent`, the entry of the chain with the covariance clause
discharged by the wrapper `FirstPassS11at.rootedCertificateEventualCovarianceStmt_decoded_of_rootedLocalIdent`
(`HarmonicBalls/FirstPass/S11at.lean`). The rooted local identification families and clauses (`uc dc ur dr κj mj`, `hbuf`,
`hsubj`, `hκmeas`, `hmmeas`, `hwin`, `hRLI`, `hRLIm`, `hκj`) are the output of `HarmonicBalls.ae_rootedLocalIdent_assembled_kernel`
(`HarmonicBalls/FirstPass/S11r/RootedBufferKernel.lean`), taken at one kernel family `κj`. They are not binders of the entry.

Named hypotheses (not discharged here): `hFdef`, `hLenAll` (the all-z form of the length-metric
clause `hLenC` of the family), `hOuter` (`closedBall c₂ r₂ ⊆ ball 0 1`), `hProf`, and the frozen Props.

Instantiations (not hypotheses): `Adm := AdmissibleRootShift α₀`, `rR := rootRadius`, `mD`-decoder through
`FirstPassS11at.windowMetric (ball c₂ r₂) mD`, `hTr` from `isWholePlaneGFF_translatedPairing` (affine invariance `hAff`), and the
admissibility clauses `hAdmReg`, `hAdmPos`, `hc1`, `hrR`, proved from the definition of `AdmissibleRootShift` and from `h0`.
-/

universe u

namespace FirstPassS11ai

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls
open HarmonicBalls.S11c

/-- **Steps 6-7 entry with the decoded covariance wrapper and the rooted local identification.** Bad quantum mass vanishes
(`ae_quantum_bad_mass_eq_zero_of_identification` conclusion). The families `uc dc ur dr κj mj` and the clauses `hbuf`, `hwin`,
`hRLI`, `hRLIm`, `hκj` come from `HarmonicBalls.ae_rootedLocalIdent_assembled_kernel`, with one kernel `κj` for all of them. -/
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
    (hFdef : ∀ L : ModConstTestPairings (Set.univ : Set ℂ),
      FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F)
    {S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ))}
    (hS : MeasurableSet S)
    (hSfail : ∀ x, x ∈ S ↔ x.1 ∈ A ∧ ¬ Tendsto (fun N : ℕ => ReferenceNullS11i.refWindowAverage c N x) atTop
      (𝓝 (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal))
    (hCont : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (G : Set S11n.CanonSpace) (hGm : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (hGreg : ∀ L ∈ G, IsEuclideanLengthMetric (Dd L))
    (G0 : Set S11n.CanonSpace) (hG0 : MeasurableSet G0) (hG0a : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G0)
    (hinv : dilOp ⁻¹' G0 = G0)
    (hstep : ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Dμ (dilOp L) = ENNReal.ofReal a • (Dμ L).map (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp L) x y = b * Dd L (((1 / 2 : ℝ) : ℂ) * x) (((1 / 2 : ℝ) : ℂ) * y))
    (hExist0 : LQGMeasureExistence P γ 0 hC hcirc) (hExistα : LQGMeasureExistence P γ α₀ hC hcirc)
    (hA10 : ∀ μ' : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarked P γ hC hcirc μ')
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{u}) (hOuter : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1)
    (hκ : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (FirstPassS11at.rootedCircleField α₀ γ hcirc z) μz → ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
          ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂))
    (hDwD : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂),
        ENNReal.ofReal (mD (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (FirstPassS11at.rootedWeylMetric 𝔇 ξ α₀ γ hC z ω) (ball c₂ r₂) p.1.1 p.1.2)
    (hLenFr : LQGMetricLengthUnivFrozen.{u}) (hFieldFr : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{u})
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hUax : LQGMetricSatisfiesAxiomsUnivFrozen.{u})
    (hLMR : ∀ (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLMK : ∀ (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{u} γ c₁ c₂ r₁ r₂)
    (hXi : LQGMetricExponentPositive)
    (hComp : WeylMetricCompositionContinuousOuterFrozen)
    (hCC : ∀ z : ℂ, LQGMeasureCoordChange P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hνex : ∀ z : ℂ, LQGMeasureExistence P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hDex : ∀ z : ℂ, ∃ D : Ω → ℂ → ℂ → ℝ, IsLQGMetricOfField P γ ξ γ (S11c.translatedPairing hC hcirc z) D)
    (hDμ : Measurable Dμ) (hDd : ∀ x y : ℂ, Measurable fun L : ModConstTestPairings (Set.univ : Set ℂ) => Dd L x y)
    (hIdγ : S11n.LQGCanonicalIdentificationStmt.{u} γ ξ γ Dμ Dd) (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hLenAll : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dd (FirstPassS11at.shiftedCanon γ hC hcirc z u ω))) :
    ∀ᵐ ω ∂P, ∫⁻ z in ball c₁ r₁,
      S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 := by
  have hAdmReg : ∀ (z : ℂ) (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u →
      ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0 :=
    fun _ _ _ h => ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  have hAdmPos : ∀ (z : ℂ) (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u → 0 < b :=
    fun _ _ _ h => h.1
  have hc1 : ball c₁ r₁ ⊆ ball c₂ r₂ := ball_subset_closedBall.trans hsub
  have hTr : ∀ z : ℂ, IsWholePlaneGFF P (translatedPairing hC hcirc z) (translatedCircle hcirc z) :=
    fun z => isWholePlaneGFF_translatedPairing hAff hh z
  have hrR : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → 0 < rootRadius z := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℂ)) measurableSet_ball] with z hz _
    have hzc : z ∈ closedBall c₂ r₂ := ball_subset_closedBall (hsub (ball_subset_closedBall hz))
    have hz0 : z ≠ 0 := fun h => h0 (h ▸ hzc)
    exact rootRadius_pos (norm_pos_iff.2 hz0)
  -- Step 6a: the families of buffered rooted local identification, with the window kernel clause hκj
  obtain ⟨uc, dc, ur, dr, κj, mj, hbuf, hsubj, hκmeas, hmmeas, hwin, hRLI, hRLIm, hκj⟩ :=
    HarmonicBalls.ae_rootedLocalIdent_assembled_kernel (γ := γ) (ξ := ξ) (α₀ := α₀) (hCM := hCM) (hG := hh)
      (hγ0 := hγ0) (hγ2 := hγ2) (hα := hα) (hc1 := hc1) (hr₂ := hr₂) (hOuter := hOuter)
      (hLMR := hLMR) (hLMK := hLMK) (h𝔇 := h𝔇) (hXi := hXi) (hField := hFieldFr) (hU := hUax)
      (hLenFr := hLenFr) (hRootFr := hRootFr) (hComp := hComp) (hCC := hCC) (hνex := hνex) (hDex := hDex)
      (Dμ := Dμ) (Dd := Dd) (hDμ := hDμ) (hDd := hDd) (hIdγ := hIdγ) (hPos := hPos) (hLenC := hLenAll)
  have hRLI' : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u →
      ∃ j : ℕ, z ∈ ball (uc j) (ur j) ∧ ∀ᵐ ω ∂P, ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧
        closedBall z ρ ⊆ ball (dc j) (dr j) ∧
        ((κj j (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2).map (fun w : ℂ => w - z)).restrict
            (closedBall 0 ρ) =
          ENNReal.ofReal c • (Dμ (FirstPassS11at.shiftedCanon γ hC hcirc z u ω)).restrict (closedBall 0 ρ) := by
    filter_upwards [hRLI] with z hz hA b u hadm using hz b u hadm
  have hRLIm' : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u →
      ∃ j : ℕ, z ∈ ball (uc j) (ur j) ∧ ∀ᵐ ω ∂P, ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧
        closedBall z ρ ⊆ ball (dc j) (dr j) ∧
        ∀ x ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ closedBall (0 : ℂ) ρ,
          FirstPassS11at.windowMetric (ball (dc j) (dr j)) (mj j)
              (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2 (x + z) (y + z) =
            c * Dd (FirstPassS11at.shiftedCanon γ hC hcirc z u ω) x y := by
    filter_upwards [hRLIm] with z hz hA b u hadm using hz b u hadm
  have hLenC' : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u →
      ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dd (FirstPassS11at.shiftedCanon γ hC hcirc z u ω)) := by
    filter_upwards [hLenAll] with z hz hA b u hadm using hz b u hadm
  have hDj : ∀ j, ball (dc j) (dr j) ⊆ ball c₂ r₂ := fun j => ball_subset_closedBall.trans (hsubj j)
  have hDjO : ∀ j, IsOpen (ball (dc j) (dr j)) := fun j => isOpen_ball
  -- Step 7: pointwise coding identity, derived from hFdef
  have hG : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
        (FirstPassS11i.CertificateEvent
            (Dμ (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            (Dd (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            Ostar U V W T Q' Q η M 1 0 ↔
          ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))) ∈ F) := by
    refine ae_of_all _ fun z _ b u _ => ?_
    exact ae_of_all _ fun ω n => hFdef _
  -- Step 6: the eventual covariance clause, from the decoded wrapper
  have hCov :=FirstPassS11at.rootedCertificateEventualCovarianceStmt_decoded_of_rootedLocalIdent
    (γ := γ) (α₀ := α₀) (ξ := ξ) (𝔇 := 𝔇) (hCM := hCM) (hC := hC) (hcirc := hcirc) (hh := hh) (hTr := hTr)
    (c₁ := c₁) (c₂ := c₂) (r₁ := r₁) (r₂ := r₂) (A := A) (Ostar := Ostar) (U := U) (V := V) (W := W) (T := T)
    (Q' := Q') (Q := Q) (η := η) (M := M) (hCont := hCont) (hU := hU) (Adm := AdmissibleRootShift α₀)
    (hAdmReg := hAdmReg) (rR := rootRadius) (κ := κ) (mD := mD) (Dμ := Dμ) (Dd := Dd) (G := G) (hG := hGm)
    (hGa := hGa) (hGreg := hGreg) (G0 := G0) (hG0 := hG0) (hG0a := hG0a) (hinv := hinv) (hstep := hstep)
    (Uj := fun j => ball (uc j) (ur j)) (Dj := fun j => ball (dc j) (dr j)) (κj := κj) (mj := mj)
    (hDj := hDj) (hDjO := hDjO) (hc1 := hc1) (hAdmPos := hAdmPos)
    (hrR := hrR) (hExist0 := hExist0) (hExistα := hExistα) (hA10 := hA10) (hProf := hProf) (hOuter := hOuter)
    (hκ := hκ) (hκj := hκj) (hRLI := hRLI') (hDwD := hDwD) (hDwj := hwin) (hLenFr := hLenFr)
    (hFieldFr := hFieldFr) (hRootFr := hRootFr) (h𝔇 := h𝔇) (hγ0 := hγ0) (hγ2 := hγ2) (hα := hα)
    (hRLIm := hRLIm') (hLenC := hLenC')
  exact ae_quantum_bad_mass_eq_zero_of_identification hCM hB hCamp hγ0 hγ2 hα hh hμ hE hr₁ hr₂ hsub h0 A Ostar U V W T Q' Q η M
    κ (FirstPassS11at.windowMetric (ball c₂ r₂) mD) c hSeq Dμ Dd hF hCov hG hS hSfail

#print axioms ae_quantum_bad_mass_eq_zero_of_rootedLocalIdent

/-- **Steps 6-7 entry, guarded length clause.** The same conclusion as
`ae_quantum_bad_mass_eq_zero_of_rootedLocalIdent`, with the length-metric binder `hLenAll` in the guarded form
`z ∈ A → …`. The families `uc dc ur dr κj mj` and the clauses `hbuf`, `hwin`,
`hRLI`, `hRLIm`, `hκj` come from the guarded kernel `HarmonicBalls.ae_rootedLocalIdent_assembled_kernel_guarded`
(`HarmonicBalls/FirstPass/S11r/RootedBufferKernelGuarded.lean`), with one kernel `κj` for all of them. -/
theorem ae_quantum_bad_mass_eq_zero_of_rootedLocalIdent_guarded
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
    (hFdef : ∀ L : ModConstTestPairings (Set.univ : Set ℂ),
      FirstPassS11i.CertificateEvent (Dμ L) (Dd L) Ostar U V W T Q' Q η M 1 0 ↔ ballRestrictPairing 7 L ∈ F)
    {S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ))}
    (hS : MeasurableSet S)
    (hSfail : ∀ x, x ∈ S ↔ x.1 ∈ A ∧ ¬ Tendsto (fun N : ℕ => ReferenceNullS11i.refWindowAverage c N x) atTop
      (𝓝 (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal))
    (hCont : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (G : Set S11n.CanonSpace) (hGm : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (hGreg : ∀ L ∈ G, IsEuclideanLengthMetric (Dd L))
    (G0 : Set S11n.CanonSpace) (hG0 : MeasurableSet G0) (hG0a : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G0)
    (hinv : dilOp ⁻¹' G0 = G0)
    (hstep : ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Dμ (dilOp L) = ENNReal.ofReal a • (Dμ L).map (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp L) x y = b * Dd L (((1 / 2 : ℝ) : ℂ) * x) (((1 / 2 : ℝ) : ℂ) * y))
    (hExist0 : LQGMeasureExistence P γ 0 hC hcirc) (hExistα : LQGMeasureExistence P γ α₀ hC hcirc)
    (hA10 : ∀ μ' : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarked P γ hC hcirc μ')
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{u}) (hOuter : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1)
    (hκ : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (FirstPassS11at.rootedCircleField α₀ γ hcirc z) μz → ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
          ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂))
    (hDwD : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂),
        ENNReal.ofReal (mD (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (FirstPassS11at.rootedWeylMetric 𝔇 ξ α₀ γ hC z ω) (ball c₂ r₂) p.1.1 p.1.2)
    (hLenFr : LQGMetricLengthUnivFrozen.{u}) (hFieldFr : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{u})
    (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hUax : LQGMetricSatisfiesAxiomsUnivFrozen.{u})
    (hLMR : ∀ (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLMK : ∀ (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{u} γ c₁ c₂ r₁ r₂)
    (hXi : LQGMetricExponentPositive)
    (hComp : WeylMetricCompositionContinuousOuterFrozen)
    (hCC : ∀ z : ℂ, LQGMeasureCoordChange P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hνex : ∀ z : ℂ, LQGMeasureExistence P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hDex : ∀ z : ℂ, ∃ D : Ω → ℂ → ℂ → ℝ, IsLQGMetricOfField P γ ξ γ (S11c.translatedPairing hC hcirc z) D)
    (hDμ : Measurable Dμ) (hDd : ∀ x y : ℂ, Measurable fun L : ModConstTestPairings (Set.univ : Set ℂ) => Dd L x y)
    (hIdγ : S11n.LQGCanonicalIdentificationStmt.{u} γ ξ γ Dμ Dd) (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (hLenAll : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dd (FirstPassS11at.shiftedCanon γ hC hcirc z u ω))) :
    ∀ᵐ ω ∂P, ∫⁻ z in ball c₁ r₁,
      S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 := by
  have hAdmReg : ∀ (z : ℂ) (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u →
      ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0 :=
    fun _ _ _ h => ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  have hAdmPos : ∀ (z : ℂ) (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u → 0 < b :=
    fun _ _ _ h => h.1
  have hc1 : ball c₁ r₁ ⊆ ball c₂ r₂ := ball_subset_closedBall.trans hsub
  have hTr : ∀ z : ℂ, IsWholePlaneGFF P (translatedPairing hC hcirc z) (translatedCircle hcirc z) :=
    fun z => isWholePlaneGFF_translatedPairing hAff hh z
  have hrR : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → 0 < rootRadius z := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℂ)) measurableSet_ball] with z hz _
    have hzc : z ∈ closedBall c₂ r₂ := ball_subset_closedBall (hsub (ball_subset_closedBall hz))
    have hz0 : z ≠ 0 := fun h => h0 (h ▸ hzc)
    exact rootRadius_pos (norm_pos_iff.2 hz0)
  -- Step 6a: the families of guarded buffered rooted local identification, with the window kernel clause hκj
  obtain ⟨uc, dc, ur, dr, κj, mj, hbuf, hsubj, hκmeas, hmmeas, hwin, hRLI, hRLIm, hκj⟩ :=
    HarmonicBalls.ae_rootedLocalIdent_assembled_kernel_guarded (γ := γ) (ξ := ξ) (α₀ := α₀) (hCM := hCM) (hG := hh)
      (hγ0 := hγ0) (hγ2 := hγ2) (hα := hα) (hc1 := hc1) (hr₂ := hr₂) (hOuter := hOuter)
      (hLMR := hLMR) (hLMK := hLMK) (h𝔇 := h𝔇) (hXi := hXi) (hField := hFieldFr) (hU := hUax)
      (hLenFr := hLenFr) (hRootFr := hRootFr) (hComp := hComp) (hCC := hCC) (hνex := hνex) (hDex := hDex)
      (Dμ := Dμ) (Dd := Dd) (hDμ := hDμ) (hDd := hDd) (hIdγ := hIdγ) (hPos := hPos) (A := A) (hLenC := hLenAll)
  have hRLI' : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u →
      ∃ j : ℕ, z ∈ ball (uc j) (ur j) ∧ ∀ᵐ ω ∂P, ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧
        closedBall z ρ ⊆ ball (dc j) (dr j) ∧
        ((κj j (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2).map (fun w : ℂ => w - z)).restrict
            (closedBall 0 ρ) =
          ENNReal.ofReal c • (Dμ (FirstPassS11at.shiftedCanon γ hC hcirc z u ω)).restrict (closedBall 0 ρ) := by
    filter_upwards [hRLI] with z hz hA b u hadm using hz b u hadm
  have hRLIm' : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u →
      ∃ j : ℕ, z ∈ ball (uc j) (ur j) ∧ ∀ᵐ ω ∂P, ∃ c ρ : ℝ, 0 < c ∧ 0 < ρ ∧
        closedBall z ρ ⊆ ball (dc j) (dr j) ∧
        ∀ x ∈ closedBall (0 : ℂ) ρ, ∀ y ∈ closedBall (0 : ℂ) ρ,
          FirstPassS11at.windowMetric (ball (dc j) (dr j)) (mj j)
              (campbellReferenceObs γ α₀ (ball (dc j) (dr j)) (hC ω) z).2 (x + z) (y + z) =
            c * Dd (FirstPassS11at.shiftedCanon γ hC hcirc z u ω) x y := by
    filter_upwards [hRLIm] with z hz hA b u hadm using hz hA b u hadm
  have hDj : ∀ j, ball (dc j) (dr j) ⊆ ball c₂ r₂ := fun j => ball_subset_closedBall.trans (hsubj j)
  have hDjO : ∀ j, IsOpen (ball (dc j) (dr j)) := fun j => isOpen_ball
  -- Step 7: pointwise coding identity, derived from hFdef
  have hG : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
        (FirstPassS11i.CertificateEvent
            (Dμ (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            (Dd (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            Ostar U V W T Q' Q η M 1 0 ↔
          ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))) ∈ F) := by
    refine ae_of_all _ fun z _ b u _ => ?_
    exact ae_of_all _ fun ω n => hFdef _
  -- Step 6: the eventual covariance clause, from the decoded wrapper (guarded length and window clauses)
  have hCov :=FirstPassS11at.rootedCertificateEventualCovarianceStmt_decoded_of_rootedLocalIdent
    (γ := γ) (α₀ := α₀) (ξ := ξ) (𝔇 := 𝔇) (hCM := hCM) (hC := hC) (hcirc := hcirc) (hh := hh) (hTr := hTr)
    (c₁ := c₁) (c₂ := c₂) (r₁ := r₁) (r₂ := r₂) (A := A) (Ostar := Ostar) (U := U) (V := V) (W := W) (T := T)
    (Q' := Q') (Q := Q) (η := η) (M := M) (hCont := hCont) (hU := hU) (Adm := AdmissibleRootShift α₀)
    (hAdmReg := hAdmReg) (rR := rootRadius) (κ := κ) (mD := mD) (Dμ := Dμ) (Dd := Dd) (G := G) (hG := hGm)
    (hGa := hGa) (hGreg := hGreg) (G0 := G0) (hG0 := hG0) (hG0a := hG0a) (hinv := hinv) (hstep := hstep)
    (Uj := fun j => ball (uc j) (ur j)) (Dj := fun j => ball (dc j) (dr j)) (κj := κj) (mj := mj)
    (hDj := hDj) (hDjO := hDjO) (hc1 := hc1) (hAdmPos := hAdmPos)
    (hrR := hrR) (hExist0 := hExist0) (hExistα := hExistα) (hA10 := hA10) (hProf := hProf) (hOuter := hOuter)
    (hκ := hκ) (hκj := hκj) (hRLI := hRLI') (hDwD := hDwD) (hDwj := hwin) (hLenFr := hLenFr)
    (hFieldFr := hFieldFr) (hRootFr := hRootFr) (h𝔇 := h𝔇) (hγ0 := hγ0) (hγ2 := hγ2) (hα := hα)
    (hRLIm := hRLIm') (hLenC := hLenAll)
  exact ae_quantum_bad_mass_eq_zero_of_identification hCM hB hCamp hγ0 hγ2 hα hh hμ hE hr₁ hr₂ hsub h0 A Ostar U V W T Q' Q η M
    κ (FirstPassS11at.windowMetric (ball c₂ r₂) mD) c hSeq Dμ Dd hF hCov hG hS hSfail

#print axioms ae_quantum_bad_mass_eq_zero_of_rootedLocalIdent_guarded

end FirstPassS11ai
