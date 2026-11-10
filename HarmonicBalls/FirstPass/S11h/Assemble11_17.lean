import HarmonicBalls.FirstPass.S11h.Cover11_17
import HarmonicBalls.FirstPass.S11h.AsFacts11_17
import HarmonicBalls.FirstPass.S11h.Select11_17
import HarmonicBalls.FirstPass.S11h.O2Bump
import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11h.PinchCertificate11_17

/-!
# First pass, Lemma 11.17 (corrected form): assembly from the 11.16 pinch event (fp-S11h, owner n2)

`firstPass_11_17_of_11_16` proves `PinchThirdEventFaithfulStmt` (Faithful.lean) from four hypotheses (`h16`, `hAx`,
`hCMGFF`, `hCert`):
- `h16`: the faithful Lemma 11.16, `PinchSecondEventFaithfulStmt` (owned by n4). The operator allows it as a hypothesis
  (decision 21:12 UTC; the Draft 11.16 is not used). It must come from the corrected Lemma 11.16 (`firstPass_11_16_corrected_*`,
  FirstPass/S11k.lean), never from the older `firstPass_11_16_of_11_17` (using it here would be a cycle).
- `hAx`: the staged metric field axioms `LQGMetricFieldAxioms` (Proposed/LQG.lean:199, Fact 2.2 I-IV), pending the
  operator's source-check; used only through the almost-sure facts of AsFacts11_17.lean.
- `hCMGFF`: the frozen `CameronMartinGFFMutualAbsCont` (Frozen/S11d). Step 17.6 is proved from it through
  `pinchPair_transfer_of_certificate` (PinchCertificate11_17.lean).
- `hCert`: `PinchCertificateStmt`, the field-level certificate of Step 17.6 for the bump shift (one measurable field
  event certifying the pinch triple before and after the shift). It is proved from frozen inputs by
  `pinchCertificateStmt_of_frozen` (PinchCertificateProof11_17.lean); `firstPass_11_17_corrected` there has it discharged.

The proof follows Steps 17.3-17.6 of `notes/fp-gaps/CHATGPT-11-15-17-faithful.md` (section 6): the truncation selection
(Select11_17, Cover11_17), the almost-sure bump admissibility and persistence of the pinch events (AsFacts11_17,
PairPersistence11_17), the smooth bump of `exists_pinch_bump` (O2Bump), and finally the transfer with `hCMGFF` and `hCert`.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Metric
open scoped ENNReal

universe u

/-- The three pinch events of the shifted pair `(μ e^{γ f}, e^{ξ f} D)` (paper Step 17.5). -/
def pinchShiftedEvents (γ ξ : ℝ) (f : ℂ → ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ) (μ : Measure ℂ)
    (D : ℂ → ℂ → ℝ) : Prop :=
  pinchFirstEvent (bumpShiftedMetric D ξ f) W T Q' Q δ ∧
    pinchSecondEvent (μ.withDensity (fun x => ENNReal.ofReal (Real.exp (γ * f x))))
      (bumpShiftedMetric D ξ f) U V δ M ∧
    pinchThirdEvent (bumpShiftedMetric D ξ f) V W δ

/-- The implication of Step 17.5 for one bump strength `k`: if `Ẽ₁`, `Ẽ₂` hold and `k · d₂ < a₂`, then the bump shift
`f = ξ⁻¹ log k · φ` carries the pair to one satisfying the three pinch events. -/
def pinchShiftImp (γ ξ : ℝ) (φ : ℂ → ℝ) (U V W T Q' Q : Set ℂ) (δ M : ℝ) (μ : Measure ℂ)
    (D : ℂ → ℂ → ℝ) (k : ℝ) : Prop :=
  (pinchFirstEvent D W T Q' Q δ ∧ pinchSecondEvent μ D U V δ M ∧
      ENNReal.ofReal k * internalDiam D δ (thickening (3 * δ) W \ V) <
        ENNReal.ofReal (setDist D (sphere (0 : ℂ) (2 * δ)) (sphere (0 : ℂ) (3 * δ)))) →
    pinchShiftedEvents γ ξ (bumpExponent ξ k φ) U V W T Q' Q δ M μ D

/-- The bump exponent `f = ξ⁻¹ log k · φ` is nonpositive for `0 < k ≤ 1` and `0 ≤ φ ≤ 1`. -/
theorem bumpExponent_nonpos {ξ k : ℝ} {φ : ℂ → ℝ} (hξ : 0 < ξ) (hk0 : 0 < k) (hk1 : k ≤ 1)
    (hφ : ∀ z, 0 ≤ φ z ∧ φ z ≤ 1) (z : ℂ) : bumpExponent ξ k φ z ≤ 0 := by
  unfold bumpExponent
  have hl : Real.log k ≤ 0 := Real.log_nonpos hk0.le hk1
  have hi : 0 < ξ⁻¹ := inv_pos.2 hξ
  have h2 : ξ⁻¹ * Real.log k ≤ 0 := by nlinarith
  have h3 := mul_nonneg (neg_nonneg.mpr h2) (hφ z).1
  nlinarith

/-- Lemma 11.17, corrected form (`PinchThirdEventFaithfulStmt`), from the faithful Lemma 11.16 `h16` and the named inputs `hAx`, `hCMGFF`, `hCert` (four hypotheses in all). -/
theorem firstPass_11_17_of_11_16 (h16 : PinchSecondEventFaithfulStmt.{u})
    (hAx : ∀ (γ ξ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hCMGFF : CameronMartinGFFMutualAbsCont.{u}) (hCert : PinchCertificateStmt.{u}) :
    PinchThirdEventFaithfulStmt.{u} := by
  unfold PinchThirdEventFaithfulStmt
  intro U V W T Q' Q δ hgeo γ α₀ dγ hγ hγ₂ hα hdγ Ω _ P hC hcirc μ D hgff hμ hD M hM
  have hξ : 0 < γ / dγ := div_pos hγ hdγ
  have haxioms : LQGMetricFieldAxioms P γ (γ / dγ) α₀ hC hcirc := hAx γ (γ / dγ) α₀ Ω P hC hcirc
  have hDae : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) :=
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ (γ / dγ) α₀ hC hcirc D haxioms hgff hγ hγ₂ hα hD
  obtain ⟨A0, hA0sub, -, hA0pos⟩ :=
    h16 U V W T Q' Q δ hgeo γ α₀ (γ / dγ) hγ hγ₂ hα Ω P hC hcirc μ D hgff hμ hD M hM
  obtain ⟨φ, hφsm, hφcs, hφtsupp, hφO2, hφU, hφcirc, hφ01⟩ := exists_pinch_bump hgeo
  have hφc : Continuous φ := hφsm.continuous
  have hφsupp : ∀ z, z ∉ thickening (5 * δ) W → φ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h' => hz (hφtsupp h'))
  -- Step 17.5, almost surely, for every bump strength k_n
  have hn_ae : ∀ n : ℕ, ∀ᵐ ω ∂P,
      pinchShiftImp γ (γ / dγ) φ U V W T Q' Q δ M (μ ω) (D ω) (pinchSelectK n) :=
    fun n => ae_pinchEvents_bumpShift P γ (γ / dγ) α₀ hC hcirc D μ haxioms hgff hγ hγ₂ hα hD hξ hgeo
      hφc hφcs hφsupp hφO2 hφU hφ01 (pinchSelectK_pos n) (pinchSelectK_le_one n)
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ,
      pinchShiftImp γ (γ / dγ) φ U V W T Q' Q δ M (μ ω) (D ω) (pinchSelectK n) :=
    ae_all_iff.2 hn_ae
  -- Step 17.3, the truncation selection
  have hcover_ae : ∀ᵐ ω ∂P, ∃ n : ℕ, pinchSelectGood (D ω) V W δ n :=
    ae_exists_pinchSelectGood hDae hgeo
  have hcov : A0 ⊆ (⋃ n : ℕ, {ω | pinchSelectGood (D ω) V W δ n}) ∪
      {ω | ¬ ∃ n : ℕ, pinchSelectGood (D ω) V W δ n} := by
    intro ω _
    by_cases hex : ∃ n : ℕ, pinchSelectGood (D ω) V W δ n
    · obtain ⟨n, hn⟩ := hex
      exact Or.inl (mem_iUnion.2 ⟨n, hn⟩)
    · exact Or.inr hex
  obtain ⟨n, hnpos⟩ := exists_pos_inter_of_ae_cover hA0pos (ae_iff.1 hcover_ae) hcov
  -- the shifted events hold on a set of positive measure
  have hBad : P {ω | ¬ ∀ m : ℕ,
      pinchShiftImp γ (γ / dγ) φ U V W T Q' Q δ M (μ ω) (D ω) (pinchSelectK m)} = 0 :=
    ae_iff.1 hall
  have hSpos : 0 < P {ω | pinchShiftedEvents γ (γ / dγ) (bumpExponent (γ / dγ) (pinchSelectK n) φ)
      U V W T Q' Q δ M (μ ω) (D ω)} := by
    have hsub : A0 ∩ {ω | pinchSelectGood (D ω) V W δ n} ⊆
        {ω | pinchShiftedEvents γ (γ / dγ) (bumpExponent (γ / dγ) (pinchSelectK n) φ)
            U V W T Q' Q δ M (μ ω) (D ω)} ∪
          {ω | ¬ ∀ m : ℕ,
            pinchShiftImp γ (γ / dγ) φ U V W T Q' Q δ M (μ ω) (D ω) (pinchSelectK m)} := by
      intro ω hω
      by_cases hgood : ∀ m : ℕ,
          pinchShiftImp γ (γ / dγ) φ U V W T Q' Q δ M (μ ω) (D ω) (pinchSelectK m)
      · have hE : pinchFirstEvent (D ω) W T Q' Q δ ∧ pinchSecondEvent (μ ω) (D ω) U V δ M :=
          hA0sub hω.1
        have hstr := pinchSelectGood_strict (show pinchSelectGood (D ω) V W δ n from hω.2)
        exact Or.inl (hgood n ⟨hE.1, hE.2, hstr⟩)
      · exact Or.inr hgood
    calc (0 : ℝ≥0∞) < P (A0 ∩ {ω | pinchSelectGood (D ω) V W δ n}) := hnpos
      _ ≤ P ({ω | pinchShiftedEvents γ (γ / dγ) (bumpExponent (γ / dγ) (pinchSelectK n) φ)
            U V W T Q' Q δ M (μ ω) (D ω)} ∪
          {ω | ¬ ∀ m : ℕ,
            pinchShiftImp γ (γ / dγ) φ U V W T Q' Q δ M (μ ω) (D ω) (pinchSelectK m)}) :=
          measure_mono hsub
      _ ≤ P {ω | pinchShiftedEvents γ (γ / dγ) (bumpExponent (γ / dγ) (pinchSelectK n) φ)
            U V W T Q' Q δ M (μ ω) (D ω)} +
          P {ω | ¬ ∀ m : ℕ,
            pinchShiftImp γ (γ / dγ) φ U V W T Q' Q δ M (μ ω) (D ω) (pinchSelectK m)} :=
          measure_union_le _ _
      _ = P {ω | pinchShiftedEvents γ (γ / dγ) (bumpExponent (γ / dγ) (pinchSelectK n) φ)
            U V W T Q' Q δ M (μ ω) (D ω)} := by rw [hBad, add_zero]
  -- Step 17.6, the pair Cameron-Martin transfer through the field-level certificate (hCert, hCMGFF)
  have hfsm : ContDiff ℝ (⊤ : ℕ∞) (bumpExponent (γ / dγ) (pinchSelectK n) φ) := by
    unfold bumpExponent
    exact contDiff_const.mul hφsm
  have hfcs : HasCompactSupport (bumpExponent (γ / dγ) (pinchSelectK n) φ) := by
    unfold bumpExponent
    exact hφcs.mul_left
  have hfcirc : ∀ z : ℂ, ‖z‖ = 1 → bumpExponent (γ / dγ) (pinchSelectK n) φ z = 0 := by
    intro z hz
    unfold bumpExponent
    rw [hφcirc z (mem_sphere_zero_iff_norm.2 hz), mul_zero]
  have hfU : ∀ z ∈ U, bumpExponent (γ / dγ) (pinchSelectK n) φ z = 0 := by
    intro z hz
    unfold bumpExponent
    rw [hφU z (subset_closure hz), mul_zero]
  have hfA : ∀ z ∈ annulus 0 3 6, bumpExponent (γ / dγ) (pinchSelectK n) φ z = 0 := by
    intro z hz
    unfold bumpExponent
    rw [bump_zero_on_annulus hgeo.W_subset hgeo.delta_lt hφsupp z hz, mul_zero]
  have hcirc0 : Real.circleAverage (bumpExponent (γ / dγ) (pinchSelectK n) φ) 0 1 = 0 :=
    circleAverage_zero_of_sphere hfcirc
  have : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  have hSpos' : 0 < P {ω | pinchPairEvent U V W T Q' Q δ M
      (weylShiftPair γ (γ / dγ) (bumpExponent (γ / dγ) (pinchSelectK n) φ) (μ ω, D ω))} := hSpos
  have hcertF := hCert U V W T Q' Q δ hgeo γ α₀ (γ / dγ) hγ hγ₂ hα hξ
    (bumpExponent (γ / dγ) (pinchSelectK n) φ) hfsm hfcs hfcirc hfU hfA M hM Ω P hC hcirc μ D hgff hμ hD
  exact pinchPair_transfer_of_certificate hCMGFF P hC hcirc hgff γ (γ / dγ)
    (bumpExponent (γ / dγ) (pinchSelectK n) φ) hfsm hfcs hcirc0 U V W T Q' Q δ M μ D hcertF hSpos'

end HarmonicBalls

#print axioms HarmonicBalls.firstPass_11_17_of_11_16
