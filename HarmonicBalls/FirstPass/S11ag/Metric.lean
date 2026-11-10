import HarmonicBalls.FirstPass.S11ae

/-! # Metric part of the second local event (fp-S11ag)

The metric clause `d₁ < a₁` of the second local event `E₂` (`pinchSecondEventLocal`, `FirstPass/S11h/LocalEvents.lean`):
`diam^δ_D(K₁) < D(∂B_δ, ∂B_{2δ})` with `K₁ = closure V`. Its countable form is `localThirdCount` (`FirstPass/S11ae/Count.lean`)
with the domain `B_δ(K₁)` and the dense sets `Sp2 ⊆ ∂B_δ`, `Sp3 ⊆ ∂B_{2δ}`, `Cp ⊆ K₁`. The field-level certificate is the
third-event proof of `FirstPass/S11ae.lean` (`metricEventCertificate_thirdLocal`) with these index sets.
-/

namespace HarmonicBalls.S11ag

open MeasureTheory Set Metric Filter
open scoped ENNReal

universe u

/-- Deterministic form of the metric clause of the second local event for a Euclidean length metric `d`: the internal
diameter of `K₁ = closure V` at scale `δ` is below the distance `D(∂B_δ, ∂B_{2δ})`, equivalently the countable form over the
dense sets. -/
theorem secondMetric_iff_count {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d)
    (hnn : ∀ x y, 0 ≤ d x y) {δ : ℝ} (hδ : 0 < δ) (V : Set ℂ)
    {Sp2 Sp3 Cp : Set ℂ} (hS2 : Sp2 ⊆ sphere (0 : ℂ) δ) (hS2c : sphere (0 : ℂ) δ ⊆ closure Sp2)
    (hS3 : Sp3 ⊆ sphere (0 : ℂ) (2 * δ)) (hS3c : sphere (0 : ℂ) (2 * δ) ⊆ closure Sp3)
    (hCp : Cp ⊆ closure V) (hCpc : closure V ⊆ closure Cp) :
    internalDiam d δ (closure V) <
        ENNReal.ofReal (setDist d (sphere (0 : ℂ) δ) (sphere (0 : ℂ) (2 * δ))) ↔
      S11ae.localThirdCount (fun O x y => internalMetric d O x y) (thickening δ (closure V)) Sp2 Sp3 Cp := by
  have h1 : internalDiam d δ (closure V) =
      ⨆ x ∈ Cp, ⨆ y ∈ Cp, internalMetric d (thickening δ (closure V)) x y :=
    internalDiam_eq_countable hd hnn hδ hCp hCpc
  have h2 : ENNReal.ofReal (setDist d (sphere (0 : ℂ) δ) (sphere (0 : ℂ) (2 * δ))) =
      ⨅ a ∈ Sp2, ⨅ b ∈ Sp3, internalMetric d univ a b :=
    ofReal_setDist_eq_countable hd (NormedSpace.sphere_nonempty.mpr hδ.le)
      (NormedSpace.sphere_nonempty.mpr (by linarith)) hS2 hS3 hS2c hS3c
  simp only [S11ae.localThirdCount]
  rw [h1, h2]

/-- The metric clause of the second local event is a field-level event: for the insertion-`α` metric `D` of a whole-plane
GFF `hC` there is a `distributionMeasurableSpace`-measurable set `B` of distributions such that, almost surely,
`hC ω ∈ B` iff `internalDiam (D ω) δ (closure V) < D(∂B_δ, ∂B_{2δ})`. Proof as in `metricEventCertificate_thirdLocal`
(`FirstPass/S11ae.lean`), with the index sets of `secondMetric_iff_count`. Uses only the frozen inputs
`LQGInternalMetricWeylAeMeasurableFrozen` and `LQGMetricFieldAxiomsUnivFrozen`. -/
theorem metricSecond_certificate {δ γ ξ : ℝ} (V : Set ℂ) (hδ : 0 < δ) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hfr : LQGInternalMetricWeylAeMeasurableFrozen.{u}) (hax : LQGMetricFieldAxiomsUnivFrozen.{u})
    (α : ℝ) (hα : α < lqgQ γ) {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (D : Ω → ℂ → ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hD : IsLQGMetricOfField P γ ξ α hC D) :
    ∃ B : Set ((ℂ → ℝ) → ℝ), MeasurableSet[distributionMeasurableSpace] B ∧
      ∀ᵐ ω ∂P, hC ω ∈ B ↔
        internalDiam (D ω) δ (closure V) <
          ENNReal.ofReal (setDist (D ω) (sphere (0 : ℂ) δ) (sphere (0 : ℂ) (2 * δ))) := by
  have hD0 := hD
  unfold IsLQGMetricOfField at hD0
  obtain ⟨𝔇, hL, hrep⟩ := hD0
  have hlen : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω) :=
    ae_isEuclideanLengthMetric_of_metricFieldAxioms P γ ξ α hC hcirc D
      (hax Ω P γ ξ α hC hcirc) hGFF hγ hγ₂ hα hD
  have hnn : ∀ᵐ ω ∂P, ∀ x y, 0 ≤ D ω x y := by
    filter_upwards [hrep] with ω hω
    exact fun x y => (hω x y).1
  have hDrep : ∀ᵐ ω ∂P, D ω = insertedLQGMetric 𝔇 ξ α (hC ω) := by
    filter_upwards [hrep] with ω hω
    funext x y
    have h0 := (hω x y).1
    have h1 := (hω x y).2
    show D ω x y = (weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) x y).toReal
    rw [← h1, ENNReal.toReal_ofReal h0]
  obtain ⟨Φ, hΦ⟩ := exists_fieldDecoders hfr hGFF hγ hγ₂ hα hL
  have hdec : ∀ W : Set ℂ, IsOpen W → ∀ x y : ℂ,
      ∀ᵐ ω ∂P, Φ W x y (hC ω) = internalMetric (D ω) W x y := by
    intro W hW x y
    filter_upwards [(hΦ W hW x y).2 (fun _ => 0) continuous_const, hDrep] with ω h1 h2
    rw [addFunPairing_zero_shift] at h1
    rw [h2]
    exact h1
  obtain ⟨Sp2, hS2A, hS2N, hS2D⟩ := S11ae.exists_countable_dense_sub (sphere (0 : ℂ) δ)
  obtain ⟨Sp3, hS3A, hS3N, hS3D⟩ := S11ae.exists_countable_dense_sub (sphere (0 : ℂ) (2 * δ))
  obtain ⟨Cp, hCpA, hCpN, hCpD⟩ := S11ae.exists_countable_dense_sub (closure V)
  refine ⟨{F | S11ae.localThirdCount (fun W' x y => Φ W' x y F) (thickening δ (closure V)) Sp2 Sp3 Cp},
    ?_, ?_⟩
  · exact S11ae.measurableSet_localThirdCount (fun W' hW' x y => (hΦ W' hW' x y).1) isOpen_thickening
      hS2N hS3N hCpN
  · have hT1 : ∀ᵐ ω ∂P, ∀ x ∈ Cp, ∀ y ∈ Cp,
        Φ (thickening δ (closure V)) x y (hC ω) = internalMetric (D ω) (thickening δ (closure V)) x y :=
      ae_forall_mem_of_countable hCpN (fun x _ =>
        ae_forall_mem_of_countable hCpN (fun y _ => hdec _ isOpen_thickening x y))
    have hT2 : ∀ᵐ ω ∂P, ∀ a ∈ Sp2, ∀ b ∈ Sp3, Φ univ a b (hC ω) = internalMetric (D ω) univ a b :=
      ae_forall_mem_of_countable hS2N (fun a _ =>
        ae_forall_mem_of_countable hS3N (fun b _ => hdec univ isOpen_univ a b))
    filter_upwards [hT1, hT2, hlen, hnn] with ω h1 h2 hl hn
    have key := S11ae.localThirdCount_congr (g := fun W' x y => Φ W' x y (hC ω))
      (h := fun W' x y => internalMetric (D ω) W' x y)
      (fun x hx y hy => h1 x hx y hy) (fun a ha b hb => h2 a ha b hb)
    exact key.trans (secondMetric_iff_count hl hn hδ V hS2A hS2D hS3A hS3D hCpA hCpD).symm

end HarmonicBalls.S11ag
