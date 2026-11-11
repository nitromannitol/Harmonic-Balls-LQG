import HarmonicBalls.FirstPass.S11i.CertCanonMeasurable
import HarmonicBalls.FirstPass.S11i.AlphaCanonical
import HarmonicBalls.FirstPass.Frozen.S11n

/-!
# Canonical certificate event with a Euclidean length decoder metric for every field


The canonical decoders `d L` of `LQGCanonicalDecodersMeasurableExistStmt` (`FirstPass/Frozen/S11n.lean`) are Euclidean
length metrics only for `L` in a measurable conull set `G`. The canonical metric `canonMetric G d` agrees with `d` on `G`
and is the Euclidean metric `dist` off `G` (`modifiedMetric`, `FirstPass/S11i/CertCanonMeasurable.lean`). Every hypothesis
of `measurableSet_certificateEvent` (`FirstPass/S11i/CertMeasurable.lean`) holds for `canonMetric G d` at every field `L`,
and the certificate event of `canonMetric G d` agrees with that of `d` almost surely along any whole-plane GFF model, since
`alphaCanon α₀ hC ω ∈ G` almost surely, so for almost every `ω` the certificate event of `d` coincides with that of
`canonMetric G d` (`ae_canonCertificateEvent_iff_decoder`).
-/

namespace FirstPassS11z

open MeasureTheory Metric Set Filter
open HarmonicBalls FirstPassS11i

universe u

/-- The canonical certificate metric: `d L` for `L ∈ G` (where `d L` is a Euclidean length metric), and the Euclidean
metric `dist` off `G`. It is the `modifiedMetric` of `CertCanonMeasurable.lean` applied to the decoders `d`. -/
noncomputable def canonMetric (G : Set HarmonicBalls.S11n.CanonSpace)
    (d : HarmonicBalls.S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ) :
    HarmonicBalls.S11n.CanonSpace → ℂ → ℂ → ℝ :=
  modifiedMetric G (fun L x y => d L (x, y))

/-- For every canonical field `L` (not only `L ∈ G`), `canonMetric G d L` satisfies the hypotheses of
`measurableSet_certificateEvent`: joint measurability in `(L, x, y)`, continuity in `(x, y)`, the Euclidean length property,
and nonnegativity. -/
theorem canonMetric_spec {G : Set HarmonicBalls.S11n.CanonSpace}
    {d : HarmonicBalls.S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ}
    (hd : Measurable d) (hG : MeasurableSet G)
    (hmet : ∀ L ∈ G, IsEuclideanLengthMetric (fun x y => d L (x, y))) :
    Measurable (fun q : HarmonicBalls.S11n.CanonSpace × (ℂ × ℂ) => canonMetric G d q.1 q.2.1 q.2.2) ∧
      (∀ L, Continuous fun q : ℂ × ℂ => canonMetric G d L q.1 q.2) ∧
      (∀ L, IsEuclideanLengthMetric (canonMetric G d L)) ∧
      (∀ L x y, 0 ≤ canonMetric G d L x y) := by
  classical
  have hm1 : Measurable fun q : HarmonicBalls.S11n.CanonSpace × (ℂ × ℂ) => d q.1 q.2 :=
    HarmonicBalls.PinchMeasurable.measurable_uncurry_of_continuousMap hd
  have hm2 : Measurable fun q : HarmonicBalls.S11n.CanonSpace × (ℂ × ℂ) => dist q.2.1 q.2.2 :=
    continuous_dist.measurable.comp measurable_snd
  have hDm : Measurable fun q : HarmonicBalls.S11n.CanonSpace × (ℂ × ℂ) =>
      canonMetric G d q.1 q.2.1 q.2.2 :=
    Measurable.ite (p := fun q : HarmonicBalls.S11n.CanonSpace × (ℂ × ℂ) => q.1 ∈ G) (measurable_fst hG) hm1 hm2
  have hDc : ∀ L, Continuous fun q : ℂ × ℂ => canonMetric G d L q.1 q.2 := by
    intro L
    by_cases h : L ∈ G
    · have hEq : canonMetric G d L = fun x y => d L (x, y) := modifiedMetric_of_mem h
      rw [hEq]
      exact (d L).continuous.comp (continuous_fst.prodMk continuous_snd)
    · have hEq : canonMetric G d L = fun x y => dist x y := modifiedMetric_of_notMem h
      rw [hEq]
      exact continuous_dist
  have hD : ∀ L, IsEuclideanLengthMetric (canonMetric G d L) := by
    intro L
    by_cases h : L ∈ G
    · have hEq : canonMetric G d L = fun x y => d L (x, y) := modifiedMetric_of_mem h
      rw [hEq]
      exact hmet L h
    · have hEq : canonMetric G d L = fun x y => dist x y := modifiedMetric_of_notMem h
      rw [hEq]
      exact isEuclideanLengthMetric_dist
  exact ⟨hDm, hDc, hD, fun L x y => lengthMetric_nonneg (hD L) x y⟩

/-- **Measurability of the canonical certificate event (c1').** The certificate event of the canonical metric
`canonMetric G d`, at every canonical field, is measurable in `(L, z)`. This is `measurableSet_certificateEvent` applied to
the modified decoders, whose hypotheses hold for every `L` by `canonMetric_spec`. -/
theorem measurableSet_canonCertificateEvent
    (κ : ProbabilityTheory.Kernel HarmonicBalls.S11n.CanonSpace ℂ) [ProbabilityTheory.IsSFiniteKernel κ]
    {G : Set HarmonicBalls.S11n.CanonSpace} {d : HarmonicBalls.S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ}
    (hd : Measurable d) (hG : MeasurableSet G)
    (hmet : ∀ L ∈ G, IsEuclideanLengthMetric (fun x y => d L (x, y)))
    {Ostar U V W T Q' Q : Set ℂ} (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar)
    (hsph : sphere (0 : ℂ) 5 ⊆ Ostar) (hU : MeasurableSet U) {η M : ℝ} (hη : 0 < η) {r : ℝ} (hr : 0 < r) :
    MeasurableSet {p : HarmonicBalls.S11n.CanonSpace × ℂ |
      CertificateEvent (κ p.1) (canonMetric G d p.1) Ostar U V W T Q' Q η M r p.2} := by
  obtain ⟨hDm, hDc, hD, hnn⟩ := canonMetric_spec hd hG hmet
  exact measurableSet_certificateEvent (D := canonMetric G d) (Ostar := Ostar) (U := U) (V := V) (W := W) (T := T)
    (Q' := Q')
    (Q := Q) (η := η) (M := M) (r := r) κ hDm hDc hD hnn hOstar h0 hsph hU hη hr

/-- **Almost sure agreement of the metrics.** If `α ω ∈ G` almost surely, then `canonMetric G d (α ω)` equals the decoder
metric `d (α ω)` almost surely. -/
theorem ae_canonMetric_eq_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {G : Set HarmonicBalls.S11n.CanonSpace} {d : HarmonicBalls.S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ}
    {α : Ω → HarmonicBalls.S11n.CanonSpace} (hα : ∀ᵐ ω ∂P, α ω ∈ G) :
    ∀ᵐ ω ∂P, canonMetric G d (α ω) = fun x y => d (α ω) (x, y) := by
  filter_upwards [hα] with ω hω
  exact modifiedMetric_of_mem hω

/-- **Almost sure agreement of the certificate events.** If `α ω ∈ G` almost surely, then the canonical metric and the
decoder metric `d (α ω)` give the same certificate event at every point `z`, for almost every `ω`. -/
theorem ae_canonCertificateEvent_iff_decoder
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (κ : ProbabilityTheory.Kernel HarmonicBalls.S11n.CanonSpace ℂ)
    {G : Set HarmonicBalls.S11n.CanonSpace} {d : HarmonicBalls.S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ}
    {α : Ω → HarmonicBalls.S11n.CanonSpace} (hα : ∀ᵐ ω ∂P, α ω ∈ G)
    {Ostar U V W T Q' Q : Set ℂ} {η M r : ℝ} :
    ∀ᵐ ω ∂P, ∀ z : ℂ,
      (CertificateEvent (κ (α ω)) (canonMetric G d (α ω)) Ostar U V W T Q' Q η M r z ↔
        CertificateEvent (κ (α ω)) (fun x y => d (α ω) (x, y)) Ostar U V W T Q' Q η M r z) := by
  filter_upwards [ae_canonMetric_eq_decoder (d := d) hα] with ω hω
  intro z
  rw [hω]

/-- **The canonical decoders of `LQGCanonicalDecodersMeasurableExistStmt`, packaged for `measurableSet_certificateEvent`.**
For `0 < γ < 2` and `α₀ < Q_γ`, the frozen existence statement gives a kernel `K`, decoders `d`, and a measurable conull set
`G`. For these, the modified metric `canonMetric G d` satisfies every hypothesis of `measurableSet_certificateEvent` at every
canonical field, its certificate event is measurable in `(L, z)`, and `alphaCanon α₀ hC ω ∈ G` almost surely along every
whole-plane GFF model, so that `canonMetric G d` and `d` agree almost surely. -/
theorem canonical_certificateEvent_measurable_of_exist (hE : HarmonicBalls.LQGCanonicalDecodersMeasurableExistStmt.{u})
    {γ ξ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hαQ : α₀ < HarmonicBalls.lqgQ γ) :
    ∃ (K : ProbabilityTheory.Kernel HarmonicBalls.S11n.CanonSpace ℂ)
      (d : HarmonicBalls.S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ) (G : Set HarmonicBalls.S11n.CanonSpace),
      ProbabilityTheory.IsSFiniteKernel K ∧ Measurable d ∧ MeasurableSet G ∧
      (∀ L ∈ G, IsEuclideanLengthMetric (fun x y => d L (x, y))) ∧
      (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
          (hcirc : Ω → ℝ → ℂ → ℝ),
          HarmonicBalls.IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P, alphaCanon α₀ hC ω ∈ G) ∧
      (∀ {Ostar U V W T Q' Q : Set ℂ} {η M r : ℝ}, IsOpen Ostar → (0 : ℂ) ∈ Ostar →
          sphere (0 : ℂ) 5 ⊆ Ostar → MeasurableSet U → 0 < η → 0 < r →
          MeasurableSet {p : HarmonicBalls.S11n.CanonSpace × ℂ |
            CertificateEvent (K p.1) (canonMetric G d p.1) Ostar U V W T Q' Q η M r p.2}) := by
  obtain ⟨K, d, hK, _hKfin, hd, _hid, G, hG, hae, hmet⟩ := hE γ ξ α₀ hγ0 hγ2 hαQ
  refine ⟨K, d, G, hK, hd, hG, fun L hL => (hmet L hL).2, hae, ?_⟩
  intro Ostar U V W T Q' Q η M r hOstar h0 hsph hU hη hr
  exact measurableSet_canonCertificateEvent K hd hG (fun L hL => (hmet L hL).2) hOstar h0 hsph hU hη hr

end FirstPassS11z

#print axioms FirstPassS11z.canonMetric_spec
#print axioms FirstPassS11z.measurableSet_canonCertificateEvent
#print axioms FirstPassS11z.ae_canonMetric_eq_decoder
#print axioms FirstPassS11z.ae_canonCertificateEvent_iff_decoder
#print axioms FirstPassS11z.canonical_certificateEvent_measurable_of_exist
