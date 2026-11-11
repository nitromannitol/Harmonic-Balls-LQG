import HarmonicBalls.Proofs.Sec11.Closure.FixedOutsideRepresentatives
import HarmonicBalls.Proofs.Sec11.Closure.FixedRawPositiveDerived
import HarmonicBalls.Proofs.Sec11.Closure.NullConditionalGrowth
import HarmonicBalls.Proofs.Sec11.Closure.PinchedSigmaLe
import HarmonicBalls.Proofs.Sec11.Closure.FixedMassDiameterOutside
import HarmonicBalls.Proofs.Sec11.ConditionalPinchRepresentatives
import HarmonicBalls.Proofs.Sec11.ConditionalCoreMeasurability
import HarmonicBalls.Proofs.Sec9.WeakUniquenessDerivedInputs
import HarmonicBalls.Steps.Sec11.WholePlaneWeylShift

/-!
# Raw positivity of the fixed configuration from outside representatives (Section 11)

The null-measurable chain `IsCorrectedPinchConfiguration.positive_wholePlane_first_second_null`
(`Proofs/Sec11/CorrectedPinchFirstSecondNull.lean`) and its three successors take the outside observables
`A`, `ha`, `hb` as exact measurability premises for the pinned σ-algebra. The almost-sure outside lemma
(`Closure/FixedOutsideRepresentatives.lean`) supplies only almost-sure representatives.
Positivity of `P` of an event is invariant under almost-sure modification, so the chain is repeated here with
the representatives `a`, `b` (with `a =ᵐ[P] ofReal (setDist …)` and `b =ᵐ[P] ofReal M · S`) in place of the exact
functions. The top-level theorem `fixed_raw_positive_null_of_staged_volume_growth_outside` then discharges the
premises `A hA hArep ha hb` of `fixed_raw_positive_null_of_staged_volume_growth_derived`
(`Closure/FixedRawPositiveDerived.lean:55`). Its remaining premises are the staged inputs `hDG hCC hE`, the square
tail input `hdata` and the zero-charge measure `hμ`; the carrier stays `Ω : Type`.

The chain is the one for Lemma 11.12 (`PinchEventPositiveProbabilityStmt`, `Draft/Section11.lean:246`) in
`Closure/FixedRawPositiveNull.lean`; only the premises change.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

/-- Level 1 with almost-sure representatives: the second pinch event with outside representatives. -/
theorem IsCorrectedPinchConfiguration.positive_wholePlane_first_second_null_representatives
    {U V W T Q' Q : Set ℂ} {δ ξ γ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (M : ℝ)
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (A : Set Ω)
    (hA : MeasurableSet[m] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ})
    (a b : Ω → ℝ≥0∞)
    (ha : @Measurable Ω ℝ≥0∞ m _ a)
    (hb : @Measurable Ω ℝ≥0∞ m _ b)
    (hae : a =ᵐ[P] fun ω => ENNReal.ofReal
      (setDist (𝔇 (hC ω)) (sphere 0 δ) (sphere 0 (2 * δ))))
    (hbe : b =ᵐ[P] fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6)
    (hgreen : ∀ᵐ ω ∂P, annulusGreenPotentialSup (μ ω) 0 3 6 ≠ ∞)
    (hinside : ∀ n k : ℕ, 0 < n →
      @NullMeasurableSet Ω m₀ {ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
  let : MeasurableSpace Ω := m₀
  let : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  have hp := h.positive_wholePlane_open_first hξ P (by simp) γ hC hcirc 𝔇 h𝔇
    hgff h.outer_piece_isConnected ψ hψ hψint
  have hAp : 0 < P A := by rw [measure_congr hArep]; exact hp
  have hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
    filter_upwards [ae_wholePlane_weylScaling_shift P γ ξ hC hcirc 𝔇 h𝔇 hgff
      (fun _ _ => 0) (by intro ω; fun_prop) (by intro x; fun_prop)] with ω hω
    exact hω.1
  have hpos := positive_pinchSecondEvent_of_conditional_null_massDiameter_representatives P m hm A
    (fun ω => 𝔇 (hC ω)) μ U V h.δ₀_mem.1 M a b hA hAp ha hb hae hbe hmetric hgreen hinside
  have heq : {ω | ω ∈ A ∧ pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} =ᵐ[P]
      {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
        pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
    filter_upwards [hArep] with ω hω
    rw [hω]
  rwa [measure_congr heq] at hpos

/-- Level 2 with almost-sure representatives: the volume-growth input supplies the Green finiteness `hgreen`. -/
theorem IsCorrectedPinchConfiguration.positive_wholePlane_first_second_of_growth_null_representatives
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {U V W T Q' Q : Set ℂ} {δ ξ γ α₀ : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (M : ℝ)
    (m : MeasurableSpace Ω) (hm : m ≤ m₀) (A : Set Ω)
    (hA : MeasurableSet[m] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ})
    (a b : Ω → ℝ≥0∞)
    (ha : @Measurable Ω ℝ≥0∞ m _ a)
    (hb : @Measurable Ω ℝ≥0∞ m _ b)
    (hae : a =ᵐ[P] fun ω => ENNReal.ofReal
      (setDist (𝔇 (hC ω)) (sphere 0 δ) (sphere 0 (2 * δ))))
    (hbe : b =ᵐ[P] fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6)
    (hinside : ∀ n k : ℕ, 0 < n →
      @NullMeasurableSet Ω m₀ {ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ ∧
      pinchSecondEvent (μ ω) (𝔇 (hC ω)) U V δ M} := by
  let : MeasurableSpace Ω := m₀
  exact h.positive_wholePlane_first_second_null_representatives hξ P hC hcirc 𝔇 μ h𝔇 hgff M m hm A
    hA hArep a b ha hb hae hbe
    (ae_annulusGreenPotentialSup_ne_top_of_lqgVolumeGrowth hgrowth hγ hγ₂ hα hgff hμ 3 (b := 6)
      (by norm_num))
    hinside

/-- Level 3 with almost-sure representatives: the conditional growth input and the open first event. -/
theorem IsCorrectedPinchConfiguration.positive_internal_pinch_of_conditional_growth_null_representatives
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {U V W T Q' Q : Set ℂ} {δ ξ γ α : ℝ}
    (h : IsCorrectedPinchConfiguration U V W T Q' Q δ) (hξ : 0 < ξ)
    (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ)
    {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (M : ℝ) (m : MeasurableSpace Ω) (hm : m ≤ m₀) (A : Set Ω)
    (hA : MeasurableSet[m] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) W T Q' Q δ})
    (a b : Ω → ℝ≥0∞)
    (ha : @Measurable Ω ℝ≥0∞ m _ a)
    (hb : @Measurable Ω ℝ≥0∞ m _ b)
    (hae : a =ᵐ[P] fun ω => ENNReal.ofReal
      (setDist (𝔇 (hC ω)) (sphere 0 δ) (sphere 0 (2 * δ))))
    (hbe : b =ᵐ[P] fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6)
    (hinside : ∀ n k : ℕ, 0 < n →
      @NullMeasurableSet Ω m₀ {ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) δ V < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω U}).indicator (fun _ => (1 : ℝ)) | m]) ω) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) U T Q' Q M 1 0} := by
  let : MeasurableSpace Ω := m₀
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α hγ hγ₂ hα
    Ω P hC hcirc μ hgff hμ
  obtain ⟨ψ, hψ, hψint⟩ := IsTestFunction.exists_integral_eq_one
    (isOpen_univ : IsOpen (univ : Set ℂ)) ⟨0, mem_univ _⟩
  exact h.positive_internal_pinch_of_open_first_second hξ P M hC hcirc 𝔇 μ h𝔇 hgff
    hμ hfull ψ hψ hψint
    (h.positive_wholePlane_first_second_of_growth_null_representatives hgrowth hξ hγ hγ₂ hα P
      hC hcirc 𝔇 μ h𝔇 hgff hμ M m hm A hA hArep a b ha hb hae hbe hinside)

/-- Level 4 (fixed configuration) with almost-sure outside representatives of `A`, `a₀` and `M·S`. The
null-measurable inside clause is discharged as in `fixed_raw_positive_outside_null`
(`Closure/FixedRawPositiveNull.lean`). -/
theorem fixed_raw_positive_outside_null_representatives (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {γ ξ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hξ : 0 < ξ)
    {Ω : Type} {m₀ : MeasurableSpace Ω} (P : Measure Ω)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (M : ℝ)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare fixedSquareCorner fixedSquareSide)) = 0)
    (hdata : SquareDyadicTailInput P ξ hC hcirc 𝔇 fixedSquareCorner fixedSquareSide)
    (A : Set Ω) (hA : MeasurableSet[fixedPinnedSigma hC] A)
    (hArep : A =ᵐ[P] {ω | correctedOpenFirstCertificate (𝔇 (hC ω)) fixedW fixedT fixedQ' fixedQ fixedDelta})
    (a b : Ω → ℝ≥0∞)
    (ha : @Measurable Ω ℝ≥0∞ (fixedPinnedSigma hC) _ a)
    (hb : @Measurable Ω ℝ≥0∞ (fixedPinnedSigma hC) _ b)
    (hae : a =ᵐ[P] fun ω => ENNReal.ofReal
      (setDist (𝔇 (hC ω)) (sphere 0 fixedDelta) (sphere 0 (2 * fixedDelta))))
    (hbe : b =ᵐ[P] fun ω => ENNReal.ofReal M * annulusGreenPotentialSup (μ ω) 0 3 6) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) fixedU fixedT fixedQ' fixedQ M 1 0} := by
  let : MeasurableSpace Ω := m₀
  have hα : (0 : ℝ) < lqgQ γ := by
    unfold lqgQ
    exact add_pos (div_pos two_pos hγ) (half_pos hγ)
  have hfull := lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ 0 hγ hγ₂ hα Ω P hC hcirc μ hgff hμ
  have hδ : (0 : ℝ) < fixedDelta := by
    rw [fixedDelta_eq]
    norm_num
  have hU : MeasurableSet fixedU := isOpen_ball.measurableSet
  have hinside : ∀ n k : ℕ, 0 < n →
      @NullMeasurableSet Ω m₀ {ω | internalDiam (𝔇 (hC ω)) fixedDelta fixedV < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω fixedU} P ∧
      ∀ᵐ ω ∂P, 0 < (P[({ω | internalDiam (𝔇 (hC ω)) fixedDelta fixedV < (n : ℝ≥0∞)⁻¹ ∧
        (k : ℝ≥0∞) < μ ω fixedU}).indicator (fun _ => (1 : ℝ)) | fixedPinnedSigma hC]) ω := by
    intro n k hn
    refine ⟨?_, ?_⟩
    · have hnull := IsWholePlaneGFF.nullMeasurableSet_mass_internalDiam hgff hμ hδ 𝔇 h𝔇 fixedU fixedV
        hU (k : ℝ≥0∞) ((n : ℝ≥0∞)⁻¹)
      have hset : {ω | internalDiam (𝔇 (hC ω)) fixedDelta fixedV < (n : ℝ≥0∞)⁻¹ ∧
          (k : ℝ≥0∞) < μ ω fixedU} = {ω | (k : ℝ≥0∞) < μ ω fixedU ∧
          internalDiam (𝔇 (hC ω)) fixedDelta fixedV < (n : ℝ≥0∞)⁻¹} := by
        ext ω
        exact and_comm
      rw [hset]
      exact hnull
    · exact @fixed_outside_hinside_of_square_dyadic_tail Ω m₀ P 0 γ ξ hC hcirc μ hgff hμ hγ hξ 𝔇 h𝔇
        hfull hfront hdata n hn k
  exact IsCorrectedPinchConfiguration.positive_internal_pinch_of_conditional_growth_null_representatives
    hgrowth isCorrectedPinchConfiguration_fixed hξ hγ hγ₂ hα P hC hcirc 𝔇 μ h𝔇 hgff hμ M
    (fixedPinnedSigma hC) (fixedPinnedSigma_le hgff) A hA hArep a b ha hb hae hbe hinside

/-- **Raw strengthened positivity of the fixed corrected configuration at zero log-charge, over `Ω : Type`, with
the outside certificate premises discharged.** This is `fixed_raw_positive_null_of_staged_volume_growth_derived`
(`Closure/FixedRawPositiveDerived.lean:55`) without its premises `A hA hArep ha hb`: they are supplied by the
outside representatives (`Closure/FixedOutsideRepresentatives.lean`). Kept explicit: the
staged inputs `hDG hCC hE` (`Proposed/LQG.lean`), the square tail input `hdata`, the zero-charge measure
`hμ`, and the metric `h𝔇`. The square frontier premise and the sign `0 < ξ` are derived. -/
theorem fixed_raw_positive_null_of_staged_volume_growth_outside
    (hDG : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hCC : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ α hC hcirc)
    {γ ξ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω : Type} [m₀ : MeasurableSpace Ω] (P : Measure Ω)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (M : ℝ)
    (hdata : SquareDyadicTailInput P ξ hC hcirc 𝔇 fixedSquareCorner fixedSquareSide) :
    0 < P {ω | pinchPointEventWithInternalBounds (μ ω) (𝔇 (hC ω)) fixedU fixedT fixedQ' fixedQ M 1 0} := by
  have hξ : 0 < ξ := IsLQGMetric.weylExponent_pos h𝔇 hγ
  have hfront : ∀ᵐ ω ∂P, μ ω (frontier (closedSquare fixedSquareCorner fixedSquareSide)) = 0 :=
    hgff.ae_lqgMeasure_frontier_closedSquare_eq_zero hγ hγ₂ hμ fixedSquareCorner fixedSquareSide_pos.le
  have hgrowth : LQGVolumeGrowthAllScalesStmt.{0} :=
    lqgVolumeGrowthAllScalesStmt_of_staged_inputs.{0} hDG hCC hE
  obtain ⟨A, hA, hArep⟩ := fixed_outside_first_certificate_rep hξ hgff 𝔇 h𝔇
  obtain ⟨a, ha, hae⟩ := fixed_outside_sphere_rep hgff 𝔇 h𝔇
  obtain ⟨b, hb, hbe⟩ := fixed_outside_green_rep hγ hγ₂ hgrowth hgff hμ M
  exact fixed_raw_positive_outside_null_representatives hgrowth hγ hγ₂ hξ P 𝔇 h𝔇 hgff hμ M hfront
    hdata A hA hArep a b ha hb hae hbe


end HarmonicBalls
