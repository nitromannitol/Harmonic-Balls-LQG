import HarmonicBalls.FirstPass.S11j.CertificateE1
import HarmonicBalls.FirstPass.Frozen.S11d
import HarmonicBalls.FirstPass.S11j.Thresholds4
import HarmonicBalls.FirstPass.S11j.ThresholdsAE

/-!
# First pass, Section 11: field-level events for the faithful Lemma 11.15 (fp-S11j, owner n4)

The open first certificate `correctedOpenFirstCertificate` of the inserted LQG metric `e^{-ξ α₀ log|·|} · 𝔇(T)` is a
countable formula in internal metrics (`openFirstCountable`, `CertificateE1.lean`). Here the internal metrics are
replaced by field-level decoders `Φ` (frozen input `LQGInternalMetricWeylAeMeasurableFrozen`,
`FirstPass/Frozen/S11d.lean`). The event "the open certificate holds for the inserted metric of the field" becomes a
measurable set of pairing functionals in `distributionMeasurableSpace`, which the Cameron-Martin transfer
`cameronMartinFieldCertificateTransfer` needs. Potential theory and LQG terminology: Armitage-Gardiner (internal
distance), Duplantier-Sheffield and Berestycki-Powell (Weyl scaling `e^{ξ h} D`).
-/

namespace HarmonicBalls

universe u

open MeasureTheory Set Metric Filter
open scoped ENNReal

/-- The inserted LQG metric `e^{-ξ α₀ log|·|} · 𝔇(T)` of a pairing functional `T` (real form, as in
`LQGInternalMetricWeylAeMeasurableFrozen`). -/
noncomputable def insertedLQGMetric (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ξ α₀ : ℝ) (T : (ℂ → ℝ) → ℝ) :
    ℂ → ℂ → ℝ :=
  fun u v => (weylScaling (𝔇 T) ξ (fun z => -α₀ * Real.log ‖z‖) u v).toReal

/-- The pairing functional of the zero shift is the pairing functional itself. -/
theorem addFunPairing_zero_shift (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => 0) = T := by
  funext φ
  simp [addFunPairing]

/-- Field-level decoders of the internal metrics of the inserted LQG metric (frozen input), one for each open domain
and pair of points, chosen once and for all. -/
theorem exists_fieldDecoders (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u})
    {γ ξ α₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α₀ < lqgQ γ)
    (hL : IsLQGMetric γ ξ 𝔇) :
    ∃ Φ : Set ℂ → ℂ → ℂ → ((ℂ → ℝ) → ℝ) → ℝ≥0∞, ∀ W : Set ℂ, IsOpen W → ∀ q q' : ℂ,
      Measurable[distributionMeasurableSpace] (Φ W q q') ∧
      ∀ f : ℂ → ℝ, Continuous f → ∀ᵐ ω ∂P,
        Φ W q q' (addFunPairing (hC ω) f) =
          internalMetric (insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)) W q q' := by
  unfold LQGInternalMetricWeylAeMeasurableFrozen at hfr
  have h := hfr γ ξ α₀ Ω P hC hcirc 𝔇 hGFF hγ hγ₂ hα hL
  choose! Φ hΦ using h
  exact ⟨Φ, hΦ⟩

/-- The countable first-certificate formula evaluated at the decoders: corridor domain `O` for the sup over `∂B₅`, the
domain `univ` for the distances to `Q'`, `∂Q` and `{0}`, and the domain `Td` for the internal diameter. -/
def fieldFirstEvent (Φ : Set ℂ → ℂ → ℂ → ((ℂ → ℝ) → ℝ) → ℝ≥0∞) (O Td : Set ℂ) (Sp Qp Fp Cp Ep : Set ℂ) :
    Set ((ℂ → ℝ) → ℝ) :=
  {F | openFirstCountable Sp Qp Fp Cp Ep (fun y => Φ O 0 y F) (fun a b => Φ univ a b F)
    (fun x y => Φ Td x y F)}

/-- The field-level event is measurable for the distribution σ-algebra, for measurable decoders and countable index
sets. -/
theorem measurableSet_fieldFirstEvent (Φ : Set ℂ → ℂ → ℂ → ((ℂ → ℝ) → ℝ) → ℝ≥0∞) {O Td : Set ℂ}
    (hΦ : ∀ W : Set ℂ, IsOpen W → ∀ q q' : ℂ, Measurable[distributionMeasurableSpace] (Φ W q q'))
    (hO : IsOpen O) (hTd : IsOpen Td) {Sp Qp Fp Cp Ep : Set ℂ}
    (hSp : Sp.Countable) (hQp : Qp.Countable) (hFp : Fp.Countable) (hCp : Cp.Countable) (hEp : Ep.Countable) :
    MeasurableSet[distributionMeasurableSpace] (fieldFirstEvent Φ O Td Sp Qp Fp Cp Ep) :=
  @measurableSet_openFirstCountable ((ℂ → ℝ) → ℝ) distributionMeasurableSpace Sp Qp Fp Cp Ep hSp hQp hFp hCp hEp
    (fun y F => Φ O 0 y F) (fun a b F => Φ univ a b F) (fun x y F => Φ Td x y F)
    (fun y => hΦ O hO 0 y) (fun a b => hΦ univ isOpen_univ a b) (fun x y => hΦ Td hTd x y)

/-- Almost surely, the field-level event of the shifted field `addFunPairing (hC ω) f` is the open first certificate
of its inserted LQG metric, once the decoders agree a.s. with the internal metrics at countably many index pairs. -/
theorem ae_fieldFirstEvent_iff {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {Φ : Set ℂ → ℂ → ℂ → ((ℂ → ℝ) → ℝ) → ℝ≥0∞} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {W T Q' Q : Set ℂ} {δ : ℝ} (hδ : 0 < δ)
    (hQ' : Q'.Nonempty) (hFr : (frontier Q).Nonempty)
    (hS : sphere (0 : ℂ) 5 ⊆ ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)))
    {Sp Qp Fp Cp Ep : Set ℂ}
    (hSp : Sp ⊆ sphere (0 : ℂ) 5) (hSpc : sphere (0 : ℂ) 5 ⊆ closure Sp)
    (hQp : Qp ⊆ Q') (hQpc : Q' ⊆ closure Qp) (hFp : Fp ⊆ frontier Q) (hFpc : frontier Q ⊆ closure Fp)
    (hCp : Cp ⊆ T \ thickening (3 * δ) W) (hCpc : T \ thickening (3 * δ) W ⊆ closure Cp)
    (hEp : Ep ⊆ sphere (0 : ℂ) δ) (hEpc : sphere (0 : ℂ) δ ⊆ closure Ep)
    (hCountS : Sp.Countable) (hCountQ : Qp.Countable) (hCountF : Fp.Countable) (hCountC : Cp.Countable)
    (hCountE : Ep.Countable) {f : ℂ → ℝ}
    (hdec : ∀ (W' : Set ℂ) (q q' : ℂ), IsOpen W' → ∀ᵐ ω ∂P, Φ W' q q' (addFunPairing (hC ω) f) =
      internalMetric (insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)) W' q q')
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)) ∧
      ∀ x y, 0 ≤ insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f) x y) :
    ∀ᵐ ω ∂P, addFunPairing (hC ω) f ∈
      fieldFirstEvent Φ (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)))
        (thickening δ (T \ thickening (3 * δ) W)) Sp Qp Fp Cp Ep ↔
      correctedOpenFirstCertificate (insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)) W T Q' Q δ := by
  have hO : IsOpen (ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) :=
    isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)
  have key := ae_openFirstCountable_iff (P := P) (M := fun ω => insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f))
    (vO := fun y ω => Φ (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y
      (addFunPairing (hC ω) f))
    (vU := fun a b ω => Φ univ a b (addFunPairing (hC ω) f))
    (vT := fun x y ω => Φ (thickening δ (T \ thickening (3 * δ) W)) x y (addFunPairing (hC ω) f))
    hδ hQ' hFr hS hSp hSpc hQp hQpc hFp hFpc hCp hCpc hEp hEpc hCountS hCountQ hCountF hCountC hCountE hmetric
    (fun y _ => hdec _ 0 y hO)
    (fun a _ b _ => hdec univ a b isOpen_univ)
    (fun b _ => hdec univ 0 b isOpen_univ)
    (fun x _ y _ => hdec _ x y isOpen_thickening)
  filter_upwards [key] with ω hω
  exact hω

/-- The base metric is the inserted metric of the unshifted field, almost surely (IsLQGMetricOfField). -/
theorem ae_base_eq_inserted {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {ξ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {D : Ω → ℂ → ℂ → ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) = weylScaling (𝔇 (hC ω)) ξ (fun x => -α₀ * Real.log ‖x‖) u v) :
    ∀ᵐ ω ∂P, D ω = insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) (fun _ => 0)) := by
  filter_upwards [hD] with ω hω
  rw [addFunPairing_zero_shift]
  funext u v
  obtain ⟨h0, h1⟩ := hω u v
  unfold insertedLQGMetric
  rw [← h1, ENNReal.toReal_ofReal h0]

/-- Almost-everywhere measurability of `ω ↦ ofReal (setDist (D ω) A B)` (a threshold variable of the first event): the
distance is a countable infimum of internal distances over `univ`, which are the decoders at the unshifted field. -/
theorem aemeasurable_ofReal_setDist {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {Φ : Set ℂ → ℂ → ℂ → ((ℂ → ℝ) → ℝ) → ℝ≥0∞} {hC : Ω → (ℂ → ℝ) → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hmC : @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace hC)
    (hΦ : ∀ W : Set ℂ, IsOpen W → ∀ q q' : ℂ, Measurable[distributionMeasurableSpace] (Φ W q q'))
    (hdec : ∀ q q' : ℂ, ∀ᵐ ω ∂P, Φ univ q q' (hC ω) = internalMetric (D ω) univ q q')
    (hD_len : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {A B A' B' : Set ℂ} (hA : A.Nonempty) (hB : B.Nonempty) (hAA : A' ⊆ A) (hBB : B' ⊆ B)
    (hAc : A ⊆ closure A') (hBc : B ⊆ closure B') (hCA : A'.Countable) (hCB : B'.Countable) :
    AEMeasurable (fun ω => ENNReal.ofReal (setDist (D ω) A B)) P := by
  have hmeas : Measurable fun ω => ⨅ a ∈ A', ⨅ b ∈ B', Φ univ a b (hC ω) :=
    measurable_iInf_mem_of_countable hCA fun a =>
      measurable_iInf_mem_of_countable hCB fun b => (hΦ univ isOpen_univ a b).comp hmC
  have hae : ∀ᵐ ω ∂P, ∀ a ∈ A', ∀ b ∈ B', Φ univ a b (hC ω) = internalMetric (D ω) univ a b :=
    ae_forall_mem_of_countable hCA fun a _ => ae_forall_mem_of_countable hCB fun b _ => hdec a b
  have hX : (fun ω => ENNReal.ofReal (setDist (D ω) A B)) =ᵐ[P]
      fun ω => ⨅ a ∈ A', ⨅ b ∈ B', Φ univ a b (hC ω) := by
    filter_upwards [hD_len, hae] with ω hlen hω
    rw [ofReal_setDist_eq_countable hlen hA hB hAA hBB hAc hBc]
    refine iInf_congr fun a => iInf_congr fun ha => iInf_congr fun b => iInf_congr fun hb => ?_
    exact (hω a ha b hb).symm
  exact hmeas.aemeasurable.congr hX.symm

/-- The decoder identity at the unshifted field: `Φ W q q' (hC ω) = internalMetric (D ω) W q q'` almost surely. -/
theorem ae_decoder_base {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {ξ α₀ : ℝ}
    {Φ : Set ℂ → ℂ → ℂ → ((ℂ → ℝ) → ℝ) → ℝ≥0∞} {hC : Ω → (ℂ → ℝ) → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (hΦ : ∀ W : Set ℂ, IsOpen W → ∀ q q' : ℂ, Measurable[distributionMeasurableSpace] (Φ W q q') ∧
      ∀ f : ℂ → ℝ, Continuous f → ∀ᵐ ω ∂P, Φ W q q' (addFunPairing (hC ω) f) =
        internalMetric (insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) f)) W q q')
    (hbase : ∀ᵐ ω ∂P, D ω = insertedLQGMetric 𝔇 ξ α₀ (addFunPairing (hC ω) (fun _ => 0)))
    {W : Set ℂ} (hW : IsOpen W) (q q' : ℂ) :
    ∀ᵐ ω ∂P, Φ W q q' (hC ω) = internalMetric (D ω) W q q' := by
  filter_upwards [((hΦ W hW q q').2 (fun _ => 0) continuous_const), hbase] with ω h1 h2
  rw [addFunPairing_zero_shift] at h1 h2
  rw [h2]
  exact h1

/-- Almost-everywhere measurability of the sup over the sphere `∂B₅` of the internal distances in the corridor `O`
(threshold `X₂`), via a countable dense subset `Sp` and the continuity of `y ↦ D(0, y; O)` on `O`. -/
theorem aemeasurable_sup_sphere_five {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {Φ : Set ℂ → ℂ → ℂ → ((ℂ → ℝ) → ℝ) → ℝ≥0∞} {hC : Ω → (ℂ → ℝ) → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hmC : @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace hC)
    (hΦ : ∀ W : Set ℂ, IsOpen W → ∀ q q' : ℂ, Measurable[distributionMeasurableSpace] (Φ W q q'))
    (hD_len : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) (hnn : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    {O : Set ℂ} (hO : IsOpen O) (hS : sphere (0 : ℂ) 5 ⊆ O)
    {Sp : Set ℂ} (hSp : Sp ⊆ sphere (0 : ℂ) 5) (hSpc : sphere (0 : ℂ) 5 ⊆ closure Sp) (hCountS : Sp.Countable)
    (hdec : ∀ y : ℂ, ∀ᵐ ω ∂P, Φ O 0 y (hC ω) = internalMetric (D ω) O 0 y) :
    AEMeasurable (fun ω => ⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (D ω) O 0 y) P := by
  have hmeas : Measurable fun ω => ⨆ y ∈ Sp, Φ O 0 y (hC ω) :=
    measurable_iSup_mem_of_countable hCountS fun y => (hΦ O hO 0 y).comp hmC
  have hae : ∀ᵐ ω ∂P, ∀ y ∈ Sp, Φ O 0 y (hC ω) = internalMetric (D ω) O 0 y :=
    ae_forall_mem_of_countable hCountS fun y _ => hdec y
  have hX : (fun ω => ⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (D ω) O 0 y) =ᵐ[P]
      fun ω => ⨆ y ∈ Sp, Φ O 0 y (hC ω) := by
    filter_upwards [hD_len, hae, hnn] with ω hlen hω hnω
    have hcont : ContinuousOn (fun y => internalMetric (D ω) O 0 y) O :=
      IsEuclideanLengthMetric.continuousOn_internalMetric hlen hnω hO 0
    refine (iSup_eq_iSup_of_dense_of_continuousOn hO hS hSp hSpc hcont).trans ?_
    exact iSup_congr fun y => iSup_congr fun hy => (hω y hy).symm
  exact hmeas.aemeasurable.congr hX.symm

/-- Almost-everywhere measurability of the internal diameter (threshold `X₄`) via a countable dense subset `A'` of `A`
and the decoders on the domain `thickening δ A`. -/
theorem aemeasurable_internalDiam {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {Φ : Set ℂ → ℂ → ℂ → ((ℂ → ℝ) → ℝ) → ℝ≥0∞} {hC : Ω → (ℂ → ℝ) → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hmC : @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace hC)
    (hΦ : ∀ W : Set ℂ, IsOpen W → ∀ q q' : ℂ, Measurable[distributionMeasurableSpace] (Φ W q q'))
    (hD_len : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) (hnn : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    {δ : ℝ} (hδ : 0 < δ) {A A' : Set ℂ} (hAA : A' ⊆ A) (hAc : A ⊆ closure A') (hCA : A'.Countable)
    (hdec : ∀ W' : Set ℂ, IsOpen W' → ∀ q q' : ℂ, ∀ᵐ ω ∂P, Φ W' q q' (hC ω) = internalMetric (D ω) W' q q') :
    AEMeasurable (fun ω => internalDiam (D ω) δ A) P := by
  have hmeas : Measurable fun ω => ⨆ x ∈ A', ⨆ y ∈ A', Φ (thickening δ A) x y (hC ω) :=
    measurable_iSup_mem_of_countable hCA fun x =>
      measurable_iSup_mem_of_countable hCA fun y => (hΦ _ isOpen_thickening x y).comp hmC
  have hae : ∀ᵐ ω ∂P, ∀ x ∈ A', ∀ y ∈ A', Φ (thickening δ A) x y (hC ω) =
      internalMetric (D ω) (thickening δ A) x y :=
    ae_forall_mem_of_countable hCA fun x _ => ae_forall_mem_of_countable hCA fun y _ =>
      hdec _ isOpen_thickening x y
  have hX : (fun ω => internalDiam (D ω) δ A) =ᵐ[P] fun ω => ⨆ x ∈ A', ⨆ y ∈ A', Φ (thickening δ A) x y (hC ω) := by
    filter_upwards [hD_len, hae, hnn] with ω hlen hω hnω
    rw [internalDiam_eq_countable hlen hnω hδ hAA hAc]
    exact iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy => (hω x hx y hy).symm
  exact hmeas.aemeasurable.congr hX.symm

/-- The four threshold variables of the base metric (paper line 3659-3667) are almost everywhere measurable, positive
(`p₁`, `p₃`, from the length-metric property of `D`) and finite (`M2`, pending input); hence the thresholds
`n, k, m, l` exist with positive probability (`exists_thresholds_measure_pos_of_aemeasurable`). -/
theorem exists_thresholds_fieldLevel {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Φ : Set ℂ → ℂ → ℂ → ((ℂ → ℝ) → ℝ) → ℝ≥0∞} {hC : Ω → (ℂ → ℝ) → ℝ} {D : Ω → ℂ → ℂ → ℝ}
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (h : IsBufferedPinchGeometry U V W T Q' Q δ) (hU : U.Nonempty)
    (hδ : 0 < δ) (hQ' : Q'.Nonempty) (hFr : (frontier Q).Nonempty)
    (hmC : @Measurable Ω ((ℂ → ℝ) → ℝ) _ distributionMeasurableSpace hC)
    (hΦ : ∀ W' : Set ℂ, IsOpen W' → ∀ q q' : ℂ, Measurable[distributionMeasurableSpace] (Φ W' q q'))
    (hdec : ∀ W' : Set ℂ, IsOpen W' → ∀ q q' : ℂ, ∀ᵐ ω ∂P, Φ W' q q' (hC ω) = internalMetric (D ω) W' q q')
    (hD_len : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω)) (hnn : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y)
    (hS : sphere (0 : ℂ) 5 ⊆ ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W)))
    {Sp Qp Fp Cp Ep : Set ℂ} (hSp : Sp ⊆ sphere (0 : ℂ) 5) (hSpc : sphere (0 : ℂ) 5 ⊆ closure Sp)
    (hQp : Qp ⊆ Q') (hQpc : Q' ⊆ closure Qp) (hFp : Fp ⊆ frontier Q) (hFpc : frontier Q ⊆ closure Fp)
    (hCp : Cp ⊆ T \ thickening (3 * δ) W) (hCpc : T \ thickening (3 * δ) W ⊆ closure Cp)
    (hEp : Ep ⊆ sphere (0 : ℂ) (δ / 2)) (hEpc : sphere (0 : ℂ) (δ / 2) ⊆ closure Ep)
    (hCountS : Sp.Countable) (hCountQ : Qp.Countable) (hCountF : Fp.Countable) (hCountC : Cp.Countable)
    (hCountE : Ep.Countable)
    -- (M2) almost sure finiteness of `X₂` and `X₄` (paper line 3664-3667; not proved, see reports/n4.md)
    (hM2a : ∀ᵐ ω ∂P, (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (D ω)
      (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y) < ⊤)
    (hM2b : ∀ᵐ ω ∂P, internalDiam (D ω) δ (T \ thickening (3 * δ) W) < ⊤) :
    ∃ n k m l : ℕ, 0 < n ∧ 0 < k ∧
      0 < P {ω | (n : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (setDist (D ω) Q' (frontier Q)) ∧
        (⨆ y ∈ sphere (0 : ℂ) 5, internalMetric (D ω)
          (ball 0 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) 0 y) ≤ (m : ℝ≥0∞) ∧
        (k : ℝ≥0∞)⁻¹ ≤ ENNReal.ofReal (setDist (D ω) {0} (sphere 0 (δ / 2))) ∧
        internalDiam (D ω) δ (T \ thickening (3 * δ) W) ≤ (l : ℝ≥0∞)} := by
  have hδ2 : 0 < δ / 2 := by positivity
  have hOopen : IsOpen (ball (0 : ℂ) 6 \ (closure (thickening (2 * δ) Q) ∪ closure (thickening (2 * δ) W))) :=
    isOpen_ball.sdiff (isClosed_closure.union isClosed_closure)
  have hUniv : ∀ q q' : ℂ, ∀ᵐ ω ∂P, Φ univ q q' (hC ω) = internalMetric (D ω) univ q q' :=
    fun q q' => hdec univ isOpen_univ q q'
  have h1 := aemeasurable_ofReal_setDist hmC hΦ hUniv hD_len hQ' hFr hQp hFp hQpc hFpc hCountQ hCountF
  have h3 := aemeasurable_ofReal_setDist (A := {0}) (B := sphere (0 : ℂ) (δ / 2)) (A' := {0}) (B' := Ep)
    hmC hΦ hUniv hD_len (singleton_nonempty 0) (NormedSpace.sphere_nonempty.2 hδ2.le) subset_rfl hEp
    (singleton_subset_iff.2 (subset_closure rfl)) hEpc (countable_singleton 0) hCountE
  have h2 := aemeasurable_sup_sphere_five hmC hΦ hD_len hnn hOopen hS hSp hSpc hCountS
    (fun y => hdec _ hOopen 0 y)
  have h4 := aemeasurable_internalDiam hmC hΦ hD_len hnn hδ hCp hCpc hCountC hdec
  have p1 : ∀ᵐ ω ∂P, 0 < ENNReal.ofReal (setDist (D ω) Q' (frontier Q)) := by
    filter_upwards [hD_len] with ω hlen
    exact ENNReal.ofReal_pos.2 (h.setDist_Q'_frontier_pos hU hlen)
  have p3 : ∀ᵐ ω ∂P, 0 < ENNReal.ofReal (setDist (D ω) {0} (sphere 0 (δ / 2))) := by
    filter_upwards [hD_len] with ω hlen
    exact ENNReal.ofReal_pos.2 (setDist_zero_sphere_pos_of_isEuclideanLengthMetric hlen hδ2)
  exact exists_thresholds_measure_pos_of_aemeasurable h1 h2 h3 h4 p1 hM2a p3 hM2b

end HarmonicBalls
