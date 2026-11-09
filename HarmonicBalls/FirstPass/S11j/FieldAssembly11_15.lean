import HarmonicBalls.FirstPass.S11j.FieldLevel11_15
import HarmonicBalls.FirstPass.S11j.CertificateTransfer
import HarmonicBalls.FirstPass.S11j.CoreShift11_15
import HarmonicBalls.FirstPass.S11j.ShiftMetric11_15
import HarmonicBalls.FirstPass.S11j.PositiveWeylBump
import HarmonicBalls.FirstPass.S11j.PositiveWeylInverse
import HarmonicBalls.FirstPass.S11j.PositiveWeylFinite
import HarmonicBalls.FirstPass.S11h.Faithful
import HarmonicBalls.FirstPass.S11e.FirstEvent
import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.Proposed.LQG

/-!
# Lemma 11.15 at the field level: conditional assembly (worker n4, task fp-S11j)

Positivity of the first event `pinchFirstEvent` (Armstrong-Kuusi-Mourrat style open first certificate, paper
Lemma 11.15, corrected form) for the LQG metric of a whole-plane GFF with a log singularity at `0`.

Route: the threshold event `Θ` (`exists_thresholds_fieldLevel`) has positive probability; on `Θ`, the core shift
`f` (`exists_core_shift`, deterministic) gives the certificate of the Weyl-shifted metric; the field-level event
`fieldFirstEvent` of the shifted field then holds (`ae_fieldFirstEvent_iff`); the Cameron-Martin transfer
(`cameronMartinFieldCertificateTransfer`) gives a positive measurable subset of the base event; a null trimming
yields `pinchFirstEvent` for the base metric.

Named hypotheses still open (see reports/n4.md): `hLen` (universe-`Type` item I for the unshifted metric),
`hM2a`, `hM2b` (almost sure finiteness), `haxioms` (Proposed input, pending source-check), the frozen inputs
`hCM`, `hfr`, `hQ1`, `hFW`, `hEx`, and the instance `[IsProbabilityMeasure P]` (not in `IsWholePlaneGFF`).
-/

namespace HarmonicBalls

universe u

open MeasureTheory Set Metric Filter
open scoped ENNReal Topology

/-- A function vanishing on the unit circle has zero circle average over the unit circle. -/
theorem circleAverage_eq_zero_of_zero_on_circle {f : ℂ → ℝ} (hf : ∀ z : ℂ, ‖z‖ = 1 → f z = 0) :
    Real.circleAverage f 0 1 = 0 := by
  have h0 : ∀ θ : ℝ, f (circleMap 0 1 θ) = 0 := fun θ => hf _ (by simp)
  simp [Real.circleAverage, h0]

/-- The sphere of radius `5` lies in the corridor `𝔸`-complement of the closed `2δ`-neighbourhoods of `Q` and `W`:
the buffers of `IsBufferedPinchGeometry` put the closed `10δ`-neighbourhoods of `Q` and `W` inside `𝔸_{4,5}` and
`𝔸_{1,2}`. -/
theorem sphere_five_subset_corridor {U V W T Q' Q : Set ℂ} {δ : ℝ}
    (h : IsBufferedPinchGeometry U V W T Q' Q δ) (hδ : 0 < δ) :
    sphere (0 : ℂ) 5 ⊆ ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)) := by
  intro z hz
  have hz5 : ‖z‖ = 5 := by simpa using hz
  refine ⟨by simp only [mem_ball, dist_zero_right, hz5]; norm_num, ?_⟩
  rintro (hc | hc)
  · have hsub : closure (thickening (2 * δ) Q) ⊆ annulus 0 4 5 :=
      (closure_mono ((thickening_mono (by linarith) Q).trans
        (thickening_subset_of_subset (10 * δ) subset_closure))).trans
        (h.buffer_Q.trans Set.sdiff_subset)
    have hlt : z ∈ Metric.ball (0 : ℂ) 5 \ Metric.closedBall (0 : ℂ) 4 := hsub hc
    have h5 := hlt.1
    rw [Metric.mem_ball, dist_zero_right] at h5
    linarith
  · have hsub : closure (thickening (2 * δ) W) ⊆ annulus 0 1 2 :=
      (closure_mono ((thickening_mono (by linarith) W).trans
        (thickening_subset_of_subset (10 * δ) subset_closure))).trans
        (h.buffer_W.trans inter_subset_right)
    have hlt : z ∈ Metric.ball (0 : ℂ) 2 \ Metric.closedBall (0 : ℂ) 1 := hsub hc
    have h2 := hlt.1
    rw [Metric.mem_ball, dist_zero_right] at h2
    linarith

/-- The second buffered pinch set is nonempty: `Q'` is connected (`IsBufferedPinchGeometry.isConnected_Q'`). -/
theorem Q'_nonempty_of_geometry {U V W T Q' Q : Set ℂ} {δ : ℝ} (h : IsBufferedPinchGeometry U V W T Q' Q δ) :
    Q'.Nonempty :=
  h.isConnected_Q'.nonempty

/-- The frontier of `Q` is nonempty: `Q` is nonempty, connected and open, and bounded (its closed `10δ`-thickening
lies in the annulus `𝔸_{4,5}`), so `Q` is neither empty nor the whole plane, and `ℂ` is connected. -/
theorem frontier_Q_nonempty {U V W T Q' Q : Set ℂ} {δ : ℝ} (h : IsBufferedPinchGeometry U V W T Q' Q δ)
    (hδ : 0 < δ) : (frontier Q).Nonempty := by
  by_contra hne
  have hcl : IsClopen Q := isClopen_iff_frontier_eq_empty.2 (Set.not_nonempty_iff_eq_empty.1 hne)
  rcases isClopen_iff.1 hcl with hQe | hQu
  · exact h.isConnected_Q.nonempty.ne_empty hQe
  · have hQsub : Q ⊆ annulus 0 4 5 :=
      (subset_closure.trans (self_subset_thickening (by linarith) (closure Q))).trans
        (subset_closure.trans (h.buffer_Q.trans Set.sdiff_subset))
    have h10 : (10 : ℂ) ∈ Q := by rw [hQu]; exact mem_univ _
    have hlt : (10 : ℂ) ∈ Metric.ball (0 : ℂ) 5 \ Metric.closedBall (0 : ℂ) 4 := hQsub h10
    have h1 := hlt.1
    rw [Metric.mem_ball, dist_zero_right] at h1
    norm_num at h1

/-- Lemma 11.15 at the field level, conditional on the named inputs: for a buffered pinch geometry, `γ ∈ (0,2)`,
`α₀ < Q`, and the LQG metric `D` of the whole-plane GFF `hC`, the event `pinchFirstEvent` has positive inner measure. -/
theorem pinchFirstEvent_positive_fieldLevel
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    (hQ1 : WeylMetricCompositionFrozen) (hFW : WeylScalingCompositionFrozen.{u})
    (hEx : LQGMetricExponentPositive)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (h : IsBufferedPinchGeometry U V W T Q' Q δ)
    {γ α₀ ξ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ α₀ hC D)
    (haxioms : LQGMetricFieldAxioms P γ ξ α₀ hC hcirc)
    (hLen : ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)))
    (hM2a : ∀ᵐ ω ∂P, (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (D ω)
      (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y) < ⊤)
    (hM2b : ∀ᵐ ω ∂P, internalDiam (D ω) δ (T \ thickening (3 * δ) W) < ⊤) :
    ∃ A ⊆ {ω | pinchFirstEvent (D ω) W T Q' Q δ}, MeasurableSet A ∧ 0 < P A := by
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hD
  have hD' : IsLQGMetricOfField P γ ξ α₀ hC D := ⟨𝔇, h𝔇, hrepr⟩
  have hξ : 0 < ξ := hEx γ ξ 𝔇 hγ hγ₂ h𝔇
  have hδ : 0 < δ := h.delta_pos
  have hU : U.Nonempty := h.U_nonempty
  have hQne : Q'.Nonempty := Q'_nonempty_of_geometry h
  have hFrQ : (frontier Q).Nonempty := frontier_Q_nonempty h hδ
  -- measurability of the base field and the field-level decoders
  have hmC : @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace hC :=
    measurable_into_distributionMeasurableSpace fun φ hφ => hGFF.measurable_pairing φ hφ
  obtain ⟨Φ, hΦ⟩ := exists_fieldDecoders hfr hGFF hγ hγ₂ hα h𝔇
  have hΦm : ∀ W' : Set ℂ, IsOpen W' → ∀ q q' : ℂ, Measurable[distributionMeasurableSpace] (Φ W' q q') :=
    fun W' hW q q' => (hΦ W' hW q q').1
  have hdecF : ∀ f : ℂ → ℝ, Continuous f → ∀ W' : Set ℂ, IsOpen W' → ∀ q q' : ℂ, ∀ᵐ ω ∂P,
      Φ W' q q' (addFunPairing (hC ω) f) =
        internalMetric (insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)) W' q q' :=
    fun f hf W' hW q q' => (hΦ W' hW q q').2 f hf
  -- the base metric is the inserted metric of the unshifted field, almost surely
  have hbase : ∀ᵐ ω ∂P, D ω = insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) (fun _ => 0)) :=
    ae_base_eq_inserted hrepr
  have hD_len : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) :=
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α₀ hC hcirc D haxioms hGFF hγ hγ₂ hα hD'
  have hnn : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y := by
    filter_upwards [hrepr] with ω hω
    exact fun x y => (hω x y).1
  have hdecD : ∀ W' : Set ℂ, IsOpen W' → ∀ q q' : ℂ, ∀ᵐ ω ∂P,
      Φ W' q q' (hC ω) = internalMetric (D ω) W' q q' := by
    intro W' hW q q'
    filter_upwards [hdecF (fun _ => 0) continuous_const W' hW q q', hbase] with ω h1 h2
    simp only [addFunPairing_zero_shift] at h1 h2
    rw [h2]
    exact h1
  -- the sets of the countable reductions
  obtain ⟨Sp, hSpC, hSp, hSpc⟩ := TopologicalSpace.exists_countable_dense_subset (sphere (0 : ℂ) 5)
  obtain ⟨Qp, hQpC, hQp, hQpc⟩ := TopologicalSpace.exists_countable_dense_subset Q'
  obtain ⟨Fp, hFpC, hFp, hFpc⟩ := TopologicalSpace.exists_countable_dense_subset (frontier Q)
  obtain ⟨Cp, hCpC, hCp, hCpc⟩ :=
    TopologicalSpace.exists_countable_dense_subset (T \ thickening (3 * δ) W)
  obtain ⟨Ep, hEpC, hEp, hEpc⟩ := TopologicalSpace.exists_countable_dense_subset (sphere (0 : ℂ) δ)
  obtain ⟨Ep2, hEp2C, hEp2, hEp2c⟩ :=
    TopologicalSpace.exists_countable_dense_subset (sphere (0 : ℂ) (δ / 2))
  have hS5 : sphere (0 : ℂ) 5 ⊆ ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)) :=
    sphere_five_subset_corridor h hδ
  have hOopen : IsOpen (ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) :=
    isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)
  have hTdopen : IsOpen (thickening δ (T \ thickening (3 * δ) W)) := isOpen_thickening
  -- thresholds: positive probability (paper M2 finiteness as named inputs)
  obtain ⟨n, k, m, l, hn, hk, hΘpos⟩ :=
    exists_thresholds_fieldLevel h hU hδ hQne hFrQ hmC hΦm hdecD hD_len hnn hS5 hSp hSpc hQp hQpc hFp hFpc
      hCp hCpc hEp2 hEp2c hSpC hQpC hFpC hCpC hEp2C hM2a hM2b
  -- the deterministic core shift
  obtain ⟨f, hfsm, hfcs, hfnn, hfunit, hcore⟩ := exists_core_shift h hU hδ hξ n m k l hn hk
  have hfcont : Continuous f := hfsm.continuous
  have hfcOn : ContinuousOn f {z | z ≠ 0} := hfcont.continuousOn
  obtain ⟨Mf, hMf⟩ := hfcont.bounded_above_of_compact_support hfcs
  have hcirc0 : Real.circleAverage f 0 1 = 0 := circleAverage_eq_zero_of_zero_on_circle hfunit
  -- almost sure facts about the Weyl-shifted metric
  have hfin : ∀ᵐ ω ∂P, ∀ x y, weylScaling (D ω) ξ f x y < ⊤ ∧
      ENNReal.ofReal ((weylScaling (D ω) ξ f x y).toReal) = weylScaling (D ω) ξ f x y := by
    filter_upwards [ae_singularField_bounded_weylScaling_finite P γ ξ α₀ hC hcirc D haxioms hGFF hγ hγ₂ hα hD'
      hξ.le] with ω hω
    exact fun x y => hω f Mf (fun z => (Real.le_norm_self (f z)).trans (hMf z)) x y
  have hLenE : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (fun x y => (weylScaling (D ω) ξ f x y).toReal) :=
    ae_fixedWeylBump_isEuclideanLengthMetric P γ ξ α₀ hC hcirc D haxioms hGFF hγ hγ₂ hα hD' hξ.le f hfcont
      hfcs hfnn
  have hinv : ∀ᵐ ω ∂P, ∀ x y, ENNReal.ofReal (D ω x y) =
      weylScaling (fun u v => (weylScaling (D ω) ξ f u v).toReal) ξ (fun z => -f z) x y :=
    ae_fixedWeylBump_inverse P γ ξ α₀ hC hcirc D haxioms hGFF hγ hγ₂ hα hD' hξ.le f hfcont hfcs hfnn
  have hshift : ∀ᵐ ω ∂P, (fun x y => (weylScaling (D ω) ξ f x y).toReal) =
      insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f) :=
    ae_shift_metric_eq hQ1 hFW hGFF hγ hγ₂ hα h𝔇 hξ hrepr (hLen 𝔇 h𝔇) hfcont hfcOn
  -- the field-level event of the shifted field, and of the base field
  have hEfEv : ∀ᵐ ω ∂P, addFunPairing (hC ω) f ∈ fieldFirstEvent Φ
      (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)))
      (thickening δ (T \ thickening (3 * δ) W)) Sp Qp Fp Cp Ep ↔
      correctedOpenFirstCertificate (insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)) W T Q' Q δ :=
    ae_fieldFirstEvent_iff hδ hQne hFrQ hS5 hSp hSpc hQp hQpc hFp hFpc hCp hCpc hEp hEpc hSpC hQpC hFpC hCpC hEpC
      (fun W' q q' hW => hdecF f hfcont W' hW q q')
      (by
        filter_upwards [hshift, hLenE] with ω h1 h2
        rw [← h1]
        exact ⟨h2, fun x y => ENNReal.toReal_nonneg⟩)
  have hBase : ∀ᵐ ω ∂P, hC ω ∈ fieldFirstEvent Φ
      (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)))
      (thickening δ (T \ thickening (3 * δ) W)) Sp Qp Fp Cp Ep ↔ correctedOpenFirstCertificate (D ω) W T Q' Q δ := by
    have h0 := ae_fieldFirstEvent_iff hδ hQne hFrQ hS5 hSp hSpc hQp hQpc hFp hFpc hCp hCpc hEp hEpc hSpC hQpC
      hFpC hCpC hEpC (fun W' q q' hW => hdecF (fun _ => 0) continuous_const W' hW q q')
      (by
        filter_upwards [hbase, hD_len, hnn] with ω h1 h2 h3
        rw [← h1]
        exact ⟨h2, h3⟩)
    filter_upwards [h0, hbase] with ω h1 h2
    simp only [addFunPairing_zero_shift] at h1 h2
    rw [h2]
    exact h1
  -- the field-level event `B` is measurable for the distribution σ-algebra
  have hB := measurableSet_fieldFirstEvent Φ hΦm hOopen hTdopen hSpC hQpC hFpC hCpC hEpC
  -- the event of positive probability on which the core shift gives the certificate
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | (n : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (setDist (D ω) Q' (frontier Q)) ∧
      (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (D ω)
        (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y) ≤ (m : ℝ≥0∞) ∧
      (k : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (setDist (D ω) {0} (sphere 0 (δ / 2))) ∧
      internalDiam (D ω) δ (T \ thickening (3 * δ) W) ≤ (l : ℝ≥0∞)} →
      ω ∈ {ω | addFunPairing (hC ω) f ∈ fieldFirstEvent Φ
        (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)))
        (thickening δ (T \ thickening (3 * δ) W)) Sp Qp Fp Cp Ep} := by
    filter_upwards [hD_len, hfin, hLenE, hinv, hshift, hEfEv] with ω hlenω hfinω hLenω hinvω hshiftω hEvω hΘω
    obtain ⟨hn', hm', hk', hl'⟩ := hΘω
    have hcore' := hcore (D ω) (fun x y => (weylScaling (D ω) ξ f x y).toReal) hlenω hLenω
      (fun x y => ENNReal.toReal_nonneg) (fun x y => (hfinω x y).2) hinvω hn' hm' hk' hl'
    have hcert : correctedOpenFirstCertificate (fun x y => (weylScaling (D ω) ξ f x y).toReal) W T Q' Q δ :=
      ⟨hcore'.2, hcore'.1.2⟩
    rw [hshiftω] at hcert
    exact hEvω.2 hcert
  -- the Cameron-Martin transfer from the base event to the shifted event
  generalize hBdef : fieldFirstEvent Φ (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)))
    (thickening δ (T \ thickening (3 * δ) W)) Sp Qp Fp Cp Ep = B at hBase hEfEv hB hsub
  have hPosEf := lt_of_lt_of_le hΘpos (measure_mono_ae hsub)
  obtain ⟨-, -, -, htr⟩ := cameronMartinFieldCertificateTransfer hCM Ω P hC hcirc f hGFF hfsm hfcs hcirc0
    {ω | hC ω ∈ B} {ω | addFunPairing (hC ω) f ∈ B}
    ⟨B, hB, ae_of_all _ fun ω => Iff.rfl, ae_of_all _ fun ω => Iff.rfl⟩
  obtain ⟨A, hAE0, hAm, hAp⟩ := htr hPosEf
  -- null trimming: the base certificate holds almost surely on `hC ⁻¹' B`
  obtain ⟨N, hNbad, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hBase)
  refine ⟨A \ N, ?_, hAm.diff hNm, ?_⟩
  · intro ω hω
    have hωB : hC ω ∈ B := hAE0 hω.1
    have hωgood : hC ω ∈ B ↔ correctedOpenFirstCertificate (D ω) W T Q' Q δ := by
      by_contra hne
      exact hω.2 (hNbad hne)
    exact pinchFirstEvent_of_correctedOpenFirstCertificate (hωgood.1 hωB)
  · rw [measure_sdiff_null hN0]
    exact hAp
