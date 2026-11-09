import HarmonicBalls.FirstPass.S11j.CertificateE1
import HarmonicBalls.FirstPass.Frozen.S11d

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

end HarmonicBalls
