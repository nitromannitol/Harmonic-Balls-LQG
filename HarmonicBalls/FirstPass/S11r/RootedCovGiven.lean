import HarmonicBalls.FirstPass.S11r.RootedBufferKernelGuarded
import HarmonicBalls.FirstPass.S11r.RootedDex
import HarmonicBalls.FirstPass.S11ai.RootedTransfer
import HarmonicBalls.FirstPass.S11at

/-!
# Rooted eventual covariance for GIVEN kernel and metric families (fp-S11r-covariance-given-families)

The rooted eventual covariance clause `FirstPassS11at.RootedCertificateEventualCovarianceStmt` for a GIVEN decoder pair
on the decoder disc `D = ball c₂ r₂` with root window `ball c₁ r₁`: a kernel `κ` and a metric replacement `mD`, which enter
only through their clauses at the insertion `α₀`:
* `hκG`: the rooted kernel clause of `LocalMeasureKernelStmt` (its second conjunct) for `κ`;
* `hmG`: the rooted metric clause (20) of `LocalMetricReplacementStmt` for `mD`.

The sub-window families of the rooted local identification are NOT given: they are produced by the guarded assembled
kernel `HarmonicBalls.ae_rootedLocalIdent_assembled_kernel_guarded` (its own `κj, mj` families, from the universal
`hLMK`, `hLMR`). The hypothesis `hDex` is the derived translated LQG metric (`exists_isLQGMetricOfField_translatedPairing_derived`),
and the affine invariance is `wholePlaneGFFAffineInvariance_derived`, so no affine binder is taken.

The proof repeats the steps 6a and 6 of `ae_quantum_bad_mass_eq_zero_of_rootedLocalIdent_guarded`, with the producer
`FirstPassS11at.rootedCertificateEventualCovarianceStmt_decoded_of_rootedLocalIdent`. The length clause `hLenC` is guarded
by `A` (the operator's guarded form, 2026-11-10).
-/

universe u

namespace FirstPassS11ai

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls
open HarmonicBalls.S11c

/-- **Rooted eventual covariance for given decoder families.** For `0 < γ < 2`, `α₀ < Q_γ`, a whole-plane GFF `hC`, a
kernel `κ` on the decoder disc `ball c₂ r₂` satisfying the rooted kernel clause at the root window `ball c₁ r₁` (`hκG`), and
a metric replacement `mD` satisfying the rooted metric clause (20) (`hmG`), the rooted eventual certificate covariance holds
with the decoded root measure `decodedRootMeasure κ` and the decoded root metric `decodedRootMetric (windowMetric _ mD)`. -/
theorem rootedCertificateEventualCovarianceStmt_of_given_families
    (hCM : HarmonicBalls.CameronMartinGFFMutualAbsCont.{u})
    {γ α₀ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (h0 : (0 : ℂ) ∉ closedBall c₂ r₂) (hOuter : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1)
    (A : Set ℂ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (hCont : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (mD : (FirstPassS11at.WinTest (ball c₂ r₂) → ℝ) → C(↥(ball c₂ r₂ ×ˢ ball c₂ r₂), ℝ))
    -- the rooted kernel clause of `LocalMeasureKernelStmt` for `κ` (second conjunct), at the root window `ball c₁ r₁`
    (hκG : ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ μz : Ω → Measure ℂ,
        IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage α (hcirc ω))
          (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) μz →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
          (κ (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
            ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂))
    -- the rooted metric clause (20) of `LocalMetricReplacementStmt` for `mD`, at the insertion `α`
    (hmG : ∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
      ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
        ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
          ENNReal.ofReal (mD (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2 p) =
            ENNReal.ofReal b * internalMetric
              (fun u v => (weylScaling (𝔇 (hC ω)) ξ
                (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)) u v).toReal)
              (ball c₂ r₂) p.1.1 p.1.2)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    (hDμ : Measurable Dμ) (hDd : ∀ x y : ℂ, Measurable fun L : ModConstTestPairings (Set.univ : Set ℂ) => Dd L x y)
    (hIdγ : S11n.LQGCanonicalIdentificationStmt.{u} γ ξ γ Dμ Dd) (hPos : LQGMeasureSquarePositiveFrozen.{u})
    (G : Set S11n.CanonSpace) (hGm : MeasurableSet G) (hGa : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G)
    (hGreg : ∀ L ∈ G, IsEuclideanLengthMetric (Dd L))
    (G0 : Set S11n.CanonSpace) (hG0 : MeasurableSet G0) (hG0a : ∀ᵐ ω ∂P, alphaCanon γ hC ω ∈ G0)
    (hinv : dilOp ⁻¹' G0 = G0)
    (hstep : ∀ L ∈ G0, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      Dμ (dilOp L) = ENNReal.ofReal a • (Dμ L).map (fun w : ℂ => w / (((1 / 2 : ℝ)) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp L) x y = b * Dd L (((1 / 2 : ℝ) : ℂ) * x) (((1 / 2 : ℝ) : ℂ) * y))
    (hExist0 : LQGMeasureExistence P γ 0 hC hcirc) (hExistα : LQGMeasureExistence P γ α₀ hC hcirc)
    (hA10 : ∀ μ' : Ω → Measure ℂ, DMSLemmaA10WholePlaneMarked P γ hC hcirc μ')
    (hProf : LQGMeasureOfProfileMeasurableFrozen.{u})
    (hLenFr : LQGMetricLengthUnivFrozen.{u}) (hFieldFr : LQGMetricFieldAxiomsUnivFrozen.{u})
    (hRootFr : RootedPhysicalMetricContinuousAtInsertionFrozen.{u})
    (hUax : LQGMetricSatisfiesAxiomsUnivFrozen.{u})
    (hLMR : ∀ (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (hLMK : ∀ (c₁ c₂ : ℂ) (r₁ r₂ : ℝ), LocalMeasureKernelStmt.{u} γ c₁ c₂ r₁ r₂)
    (hXi : LQGMetricExponentPositive) (hComp : WeylMetricCompositionContinuousOuterFrozen)
    (hCC : ∀ z : ℂ, LQGMeasureCoordChange P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hνex : ∀ z : ℂ, LQGMeasureExistence P γ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z))
    (hLenC : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, IsEuclideanLengthMetric (Dd (FirstPassS11at.shiftedCanon γ hC hcirc z u ω))) :
    FirstPassS11at.RootedCertificateEventualCovarianceStmt P γ hC hcirc c₁ c₂ r₁ r₂ A Ostar U V W T Q' Q η M
      (AdmissibleRootShift α₀) rootRadius
      (FirstPassS11at.decodedRootMeasure κ γ α₀ hC)
      (FirstPassS11at.decodedRootMetric (FirstPassS11at.windowMetric (ball c₂ r₂) mD) γ α₀ hC) Dμ Dd := by
  have hc1 : ball c₁ r₁ ⊆ ball c₂ r₂ := ball_subset_closedBall.trans hsub
  have hAdmReg : ∀ (z : ℂ) (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u →
      ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0 :=
    fun _ _ _ h => ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  have hAdmPos : ∀ (z : ℂ) (b : ℝ) (u : ℂ → ℝ), AdmissibleRootShift α₀ z b u → 0 < b :=
    fun _ _ _ h => h.1
  -- the translated whole-plane GFF and the translated LQG metric, from the derived affine invariance
  have hTr : ∀ z : ℂ, IsWholePlaneGFF P (translatedPairing hC hcirc z) (translatedCircle hcirc z) :=
    fun z => isWholePlaneGFF_translatedPairing (fun Q C K => HarmonicBalls.wholePlaneGFFAffineInvariance_derived Q C K) hh z
  have hDex : ∀ z : ℂ, ∃ D : Ω → ℂ → ℂ → ℝ, IsLQGMetricOfField P γ ξ γ (S11c.translatedPairing hC hcirc z) D :=
    fun z => HarmonicBalls.exists_isLQGMetricOfField_translatedPairing_derived hγ0 hγ2 hh h𝔇 hFieldFr z
  have hrR : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → 0 < rootRadius z := by
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℂ)) measurableSet_ball] with z hz _
    have hzc : z ∈ closedBall c₂ r₂ := ball_subset_closedBall (hsub (ball_subset_closedBall hz))
    have hz0 : z ≠ 0 := fun h => h0 (h ▸ hzc)
    exact rootRadius_pos (norm_pos_iff.2 hz0)
  -- the given kernel and metric clauses at the insertion `α₀`
  have hκ : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ μz : Ω → Measure ℂ,
      IsLQGMeasure P γ (FirstPassS11at.rootedCircleField α₀ γ hcirc z) μz → ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
        (κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
          ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂) :=
    hκG α₀ hα Ω P hC hcirc hh
  have hDwD : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂),
        ENNReal.ofReal (mD (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (FirstPassS11at.rootedWeylMetric 𝔇 ξ α₀ γ hC z ω) (ball c₂ r₂)
            p.1.1 p.1.2 :=
    hmG α₀ hα Ω P hC hcirc hh
  -- Step 6a: the sub-window families of the guarded buffered rooted local identification
  obtain ⟨uc, dc, ur, dr, κj, mj, hbuf, hsubj, hκmeas, hmmeas, hwin, hRLI, hRLIm, hκj⟩ :=
    HarmonicBalls.ae_rootedLocalIdent_assembled_kernel_guarded (γ := γ) (ξ := ξ) (α₀ := α₀) (hCM := hCM) (hG := hh)
      (hγ0 := hγ0) (hγ2 := hγ2) (hα := hα) (hc1 := hc1) (hr₂ := hr₂) (hOuter := hOuter)
      (hLMR := hLMR) (hLMK := hLMK) (h𝔇 := h𝔇) (hXi := hXi) (hField := hFieldFr) (hU := hUax)
      (hLenFr := hLenFr) (hRootFr := hRootFr) (hComp := hComp) (hCC := hCC) (hνex := hνex) (hDex := hDex)
      (Dμ := Dμ) (Dd := Dd) (hDμ := hDμ) (hDd := hDd) (hIdγ := hIdγ) (hPos := hPos) (A := A) (hLenC := hLenC)
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
  -- Step 6: the eventual covariance clause, from the decoded wrapper with the given `κ` and `mD`
  exact FirstPassS11at.rootedCertificateEventualCovarianceStmt_decoded_of_rootedLocalIdent
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
    (hRLIm := hRLIm') (hLenC := hLenC)

#print axioms rootedCertificateEventualCovarianceStmt_of_given_families

end FirstPassS11ai
