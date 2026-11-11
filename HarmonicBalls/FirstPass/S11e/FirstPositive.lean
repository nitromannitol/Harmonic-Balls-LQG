import HarmonicBalls.FirstPass.S11e.FirstEvent
import HarmonicBalls.FirstPass.S11e.GFFTransfer
import HarmonicBalls.FirstPass.S11e.MeasurableVersion
import HarmonicBalls.FirstPass.Frozen.S11e
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstPositive
import HarmonicBalls.Proofs.Sec11.CorrectedPinchFirstMeasurable
import HarmonicBalls.Steps.Sec11.WholePlaneWeylShift
import HarmonicBalls.Steps.Sec11.ProperMetricDyadic

/-!
# Positivity of the first pinch event

Lemma 11.15 (`lemma:first-event-proof`, paper line 3277): `P[Ẽ₁] > 0` for a pinch configuration. The proof transfers
the open-certificate positivity of the Type proof `IsCorrectedPinchConfiguration.positive_open_first` to the Type-0 carrier
`PinchCarrier` (`GFFTransfer.lean`), where the certificate event is measurable after a measurable version of the metric
(`MeasurableVersion.lean`, frozen a.e. measurability `LQGMetricPointwiseAEMeasurableFrozen`), and pulls the positive
measure back to the field.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Classical

/-- An almost sure property has a measurable null exceptional set. -/
lemma exists_null_measurable_of_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p : Ω → Prop}
    (h : ∀ᵐ ω ∂P, p ω) : ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧ ∀ ω, ω ∉ N → p ω :=
  ⟨toMeasurable P {ω | ¬ p ω}, measurableSet_toMeasurable _ _, by rw [measure_toMeasurable]; exact ae_iff.1 h,
    fun ω hω => by
      by_contra hc
      exact hω (subset_toMeasurable _ _ hc)⟩

/-- The good points of the carrier: the zero-shift metric is a Euclidean length metric with the Weyl identity, and the
measurable version agrees with it at every point. -/
def GoodY (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ : ℝ) (D' : PinchCarrier → ℂ × ℂ → ℝ) (y : PinchCarrier) : Prop :=
  IsEuclideanLengthMetric (𝔇 y.pair) ∧ (∀ x z : ℂ, weylScaling (𝔇 y.pair) ξ 0 x z = ENNReal.ofReal (𝔇 y.pair x z)) ∧
    ∀ q : ℂ × ℂ, D' y q = 𝔇 y.pair q.1 q.2

/-- A Euclidean length metric is nonnegative. -/
lemma nonneg_of_isEuclideanLengthMetric {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x z : ℂ) :
    0 ≤ D x z := by
  have ht := hD.triangle x z x
  rw [hD.self_eq_zero, hD.symm z x] at ht
  linarith

/-- Lemma 11.15 at the level of a whole-plane GFF realization: the certificate event has positive measure, with a
measurable witness inside the Draft event `pinchFirstEvent`. -/
theorem pinchFirst_positive_of_frozen (hfr : LQGMetricPointwiseAEMeasurableFrozen)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (h : IsCorrectedPinchConfiguration U V W T Q' Q δ)
    {γ ξ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (D : Ω → ℂ → ℂ → ℝ) (hgff : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ 0 hC D) :
    ∃ A ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ}, MeasurableSet A ∧ 0 < P A := by
  have : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  obtain ⟨𝔇, h𝔇, hDω⟩ := hD
  have hξ : 0 < ξ := weylExponent_pos_of_gamma_pos h𝔇 hγ
  -- circle continuity off a measurable null set, and the carrier map
  obtain ⟨N₀, hN₀m, hN₀0, hcont⟩ := exists_null_measurable_of_ae hgff.ae_continuousOn_circle
  have hΦm : Measurable (carrierMap hC hcirc N₀ hcont) := measurable_carrierMap hgff N₀ hN₀m hcont
  have hgff' := isWholePlaneGFF_carrierMap hgff N₀ hN₀m hN₀0 hcont
  set Φ := carrierMap hC hcirc N₀ hcont with hΦdef
  set ν : Measure PinchCarrier := P.map Φ with hνdef
  -- Step 1: positivity of the open certificate on the carrier (existing Type proof)
  have hpos : 0 < ν {y | correctedOpenFirstCertificate (𝔇 y.pair) W T Q' Q δ} :=
    h.positive_open_first hξ ν γ (fun y : PinchCarrier => y.pair) (fun y : PinchCarrier => y.circ) 𝔇 h𝔇 hgff'
  -- Step 2: almost sure facts of the carrier realization
  have hYae := ae_wholePlane_weylScaling_shift ν γ ξ (fun y : PinchCarrier => y.pair)
    (fun y : PinchCarrier => y.circ) 𝔇 h𝔇 hgff' (fun _ => fun _ => (0 : ℝ))
    (fun _ => continuous_const) (fun _ => measurable_const)
  have hYgood : ∀ᵐ y ∂ν, IsEuclideanLengthMetric (𝔇 y.pair) ∧
      ∀ x z : ℂ, weylScaling (𝔇 y.pair) ξ 0 x z = ENNReal.ofReal (𝔇 y.pair x z) :=
    hYae.mono fun y hy => ⟨hy.1, hy.2.2.1⟩
  have hzero : (fun x : ℂ => -(0 : ℝ) * Real.log ‖x‖) = (0 : ℂ → ℝ) := by
    funext x
    simp
  -- Step 3: the carrier realization satisfies the realized-metric hypothesis
  have hDν : IsLQGMetricOfField ν γ ξ 0 (fun y : PinchCarrier => y.pair) (fun y u v => 𝔇 y.pair u v) := by
    refine ⟨𝔇, h𝔇, ?_⟩
    filter_upwards [hYgood] with y hy
    intro u v
    refine ⟨nonneg_of_isEuclideanLengthMetric hy.1 u v, ?_⟩
    rw [hzero]
    exact (hy.2 u v).symm
  -- Step 4: measurable version of the metric on the carrier (frozen a.e. measurability + countable representation)
  have hae : ∀ x z : ℂ, AEMeasurable (fun y : PinchCarrier => 𝔇 y.pair x z) ν :=
    fun x z => hfr γ ξ PinchCarrier ν (fun y => y.pair) (fun y => y.circ) (fun y u v => 𝔇 y.pair u v) hgff' hγ hγ2
      hDν x z
  have hcontY : ∀ᵐ y ∂ν, Continuous (fun p : ℂ × ℂ => 𝔇 y.pair p.1 p.2) :=
    hYgood.mono fun y hy => hy.1.continuous_pair
  obtain ⟨D', hD'm, hD'eq⟩ :=
    exists_measurable_version_of_continuous ν (fun y p => 𝔇 y.pair p.1 p.2) hcontY (fun q => hae q.1 q.2)
  -- Step 5: a measurable null set off which everything is good
  have hGood : ∀ᵐ y ∂ν, GoodY 𝔇 ξ D' y := by
    filter_upwards [hYgood, hD'eq] with y hy hy'
    exact ⟨hy.1, hy.2, hy'⟩
  obtain ⟨M, hMm, hM0, hM⟩ := exists_null_measurable_of_ae hGood
  -- Step 6: the modified metric, everywhere a Euclidean length metric and measurable
  let Dm : PinchCarrier → ℂ → ℂ → ℝ := fun y u v => if y ∈ M then dist u v else D' y (u, v)
  have hDm_meas : ∀ x z : ℂ, Measurable fun y => Dm y x z := fun x z =>
    Measurable.ite hMm measurable_const (hD'm (x, z))
  have hDm_eq : ∀ y, y ∉ M → Dm y = fun u v => 𝔇 y.pair u v := by
    intro y hy
    funext u v
    have hgy := hM y hy
    simp only [Dm, hy, ↓reduceIte]
    exact hgy.2.2 (u, v)
  have hDm_len : ∀ y, IsEuclideanLengthMetric (Dm y) := by
    intro y
    by_cases hy : y ∈ M
    · have hfun : Dm y = fun u v => dist u v := by
        funext u v
        simp only [Dm, hy, ↓reduceIte]
      rw [hfun]
      exact isEuclideanLengthMetric_dist
    · rw [hDm_eq y hy]
      exact (hM y hy).1
  -- Step 7: the certificate event of the modified metric is measurable
  have hSm : MeasurableSet {y : PinchCarrier | correctedOpenFirstCertificate (Dm y) W T Q' Q δ} :=
    h.measurableSet_open_first_certificate hDm_meas hDm_len
  -- Step 8: the field certificate event lies in the modified one up to the null set `M`
  have hsub : {y : PinchCarrier | correctedOpenFirstCertificate (𝔇 y.pair) W T Q' Q δ} ⊆
      {y : PinchCarrier | correctedOpenFirstCertificate (Dm y) W T Q' Q δ} ∪ M := by
    intro y hy
    by_cases hyM : y ∈ M
    · exact Or.inr hyM
    · left
      show correctedOpenFirstCertificate (Dm y) W T Q' Q δ
      rw [hDm_eq y hyM]
      exact hy
  have hSpos : 0 < ν {y : PinchCarrier | correctedOpenFirstCertificate (Dm y) W T Q' Q δ} := by
    refine lt_of_lt_of_le hpos ?_
    calc ν {y | correctedOpenFirstCertificate (𝔇 y.pair) W T Q' Q δ}
        ≤ ν ({y : PinchCarrier | correctedOpenFirstCertificate (Dm y) W T Q' Q δ} ∪ M) := measure_mono hsub
      _ ≤ ν {y : PinchCarrier | correctedOpenFirstCertificate (Dm y) W T Q' Q δ} + ν M := measure_union_le _ _
      _ = ν {y : PinchCarrier | correctedOpenFirstCertificate (Dm y) W T Q' Q δ} := by rw [hM0, add_zero]
  -- Step 9: pull back to the field
  obtain ⟨N, hNm, hN0, hNgood⟩ := exists_null_measurable_of_ae hDω
  let S : Set PinchCarrier := {y | correctedOpenFirstCertificate (Dm y) W T Q' Q δ}
  let A : Set Ω := Φ ⁻¹' S \ (Φ ⁻¹' M ∪ N)
  have hAm : MeasurableSet A := (hΦm hSm).diff ((hΦm hMm).union hNm)
  have hAsub : A ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ} := by
    intro ω hω
    obtain ⟨hωS, hωnot⟩ := hω
    have hΦM : Φ ω ∉ M := fun hc => hωnot (Or.inl hc)
    have hωN : ω ∉ N := fun hc => hωnot (Or.inr hc)
    have hc : correctedOpenFirstCertificate (Dm (Φ ω)) W T Q' Q δ := hωS
    rw [hDm_eq (Φ ω) hΦM] at hc
    have hGY := hM (Φ ω) hΦM
    have hDeq : D ω = fun u v => 𝔇 (hC ω) u v := by
      funext u v
      have hval := hNgood ω hωN u v
      have hw : ENNReal.ofReal (𝔇 (hC ω) u v) =
          weylScaling (𝔇 (hC ω)) ξ (fun x => -0 * Real.log ‖x‖) u v := by
        rw [hzero]
        exact (hGY.2.1 u v).symm
      have hEq : ENNReal.ofReal (D ω u v) = ENNReal.ofReal (𝔇 (hC ω) u v) := hval.2.trans hw.symm
      exact (ENNReal.ofReal_eq_ofReal_iff hval.1 (nonneg_of_isEuclideanLengthMetric hGY.1 u v)).1 hEq
    show pinchFirstEvent (D ω) W T Q' Q δ
    rw [hDeq]
    exact pinchFirstEvent_of_correctedOpenFirstCertificate hc
  have hPA : 0 < P A := by
    have hsub2 : Φ ⁻¹' S ⊆ A ∪ (Φ ⁻¹' M ∪ N) := by
      intro ω hω
      by_cases hωM : ω ∈ Φ ⁻¹' M ∪ N
      · exact Or.inr hωM
      · exact Or.inl ⟨hω, hωM⟩
    have hpos2 : 0 < P (Φ ⁻¹' S) := by
      rw [← Measure.map_apply hΦm hSm]
      exact hSpos
    have hPM : P (Φ ⁻¹' M) = 0 := by
      rw [← Measure.map_apply hΦm hMm]
      exact hM0
    calc (0 : ℝ≥0∞) < P (Φ ⁻¹' S) := hpos2
      _ ≤ P (A ∪ (Φ ⁻¹' M ∪ N)) := measure_mono hsub2
      _ ≤ P A + P (Φ ⁻¹' M ∪ N) := measure_union_le _ _
      _ ≤ P A + (P (Φ ⁻¹' M) + P N) := add_le_add le_rfl (measure_union_le _ _)
      _ = P A := by rw [hPM, hN0]; simp
  exact ⟨A, hAsub, hAm, hPA⟩

#print axioms pinchFirst_positive_of_frozen

end HarmonicBalls
