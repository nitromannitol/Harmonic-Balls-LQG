import HarmonicBalls.FirstPass.S11ah.Step5Closed
import HarmonicBalls.FirstPass.S11ah.FailureSet
import HarmonicBalls.FirstPass.S11ah.LocalCert
import HarmonicBalls.FirstPass.S11ao

/-!
# Steps 4-5 in the form of the local certificate sequence (J)

Step 4 (formula (J)): `localCert` (`S11ah/LocalCert.lean`) is
`c_n(ℓ, z) = 1_{E_{2^{-n}}(κ ℓ, D ℓ; z, M)}` when `closedBall z (7 · 2^{-n}) ⊆ ball c R`, and `0` otherwise, for a local
decoder `D ℓ` on the disc `ball c R` and a local measure `κ ℓ`. Step 5: the failure set `S = {(z, ℓ) | z ∈ A, the window
averages of c_n(·, ℓ) at z do not converge to q}` (`failureSet`, `S11ah/FailureSet.lean`) is measurable.

This file gives the observable-indexed form used by `FirstPass/S11ai/RootedInstance.lean`:

* `localCert_eq_localCertLoc`: on the cutoff event `localCert` is the lifted-disc indicator `localCertLoc`
  (`S11ah/LocalMeasurable.lean`) of the same decoder, under the locality hypothesis `CertificateEventLocality`;
* `measurable_localCert_disc` (hc): joint measurability of `(z, ℓ) ↦ localCert … n ℓ z` for a decoder family measurable in
  `ℓ` and a length metric on the disc for every `ℓ`;
* `measurableSet_failureSet_disc`: measurability of the failure set `S` of the local decoders;
* `exists_modified_failureSet_localCert`: for any measure `Pm` on the index space with the length property `Pm`-a.s., there is a
  modification `D'` which is a length metric for every `ℓ`, whose failure set is measurable and agrees with that of `D` on
  the sections over a measurable set `H` of full `Pm`-measure (`exists_measurable_localLengthModification`,
  `S11ao.lean:44`);
* `exists_modified_failureSet_closed_localCert`: the instance for the model sample space, with identity (18) as the only
  input (the LQG length property, `ae_isLengthMetricOn_decoderOn`, and the cutoff R1 `cutoffInternalLengthStmt` are proved).

Not covered here: the rooted decoders (identity (20) of `LocalMetricReplacementStmt`), whose length property for a.e. root
is not yet available.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology HarmonicBalls
open scoped ENNReal

noncomputable section

namespace FirstPassS11ah

/-- A radial lift is the identity on the disc `closedBall c ρ`, so `liftMetric` agrees with the metric `D` on every
closed ball `closedBall z s` contained in `ball c ρ`. -/
theorem liftMetric_eq_on_closedBall {c : ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (D : ℂ → ℂ → ℝ) {z : ℂ} {s : ℝ}
    (hs : closedBall z s ⊆ ball c ρ) :
    ∀ x ∈ closedBall z s, ∀ y ∈ closedBall z s, liftMetric c ρ R D x y = D x y := by
  intro x hx y hy
  have hx' : ‖x - c‖ ≤ ρ := by
    have := hs hx
    rw [mem_ball, dist_eq_norm] at this
    exact this.le
  have hy' : ‖y - c‖ ≤ ρ := by
    have := hs hy
    rw [mem_ball, dist_eq_norm] at this
    exact this.le
  unfold liftMetric
  rw [radialLift_eq_self_of_le hρ hx', radialLift_eq_self_of_le hρ hy']

/-- Membership in the local certificate set of the disc `ball c R` is the certificate event of the decoder itself, when the
closed ball `closedBall p.2 (7 r)` lies in the disc (locality `CertificateEventLocality`, `S11ah/LocalMeasurable.lean`). -/
theorem mem_localCertSet_iff_certificateEvent {Ω : Type*} [MeasurableSpace Ω] {c : ℂ} {R : ℝ} (hR : 0 < R)
    (κ : Kernel Ω ℂ)
    (D : Ω → ℂ → ℂ → ℝ) {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    (hloc : CertificateEventLocality Ostar U V W T Q' Q η M)
    {r : ℝ} (hr : 0 < r) (p : Ω × ℂ) (hp : closedBall p.2 (7 * r) ⊆ ball c R) :
    p ∈ localCertSet c R κ D Ostar U V W T Q' Q η M r ↔
      FirstPassS11i.CertificateEvent (κ p.1) (D p.1) Ostar U V W T Q' Q η M r p.2 := by
  rw [localCertSet_iff_of_locality hR κ D hloc hr p hp]
  obtain ⟨j₀, hj₀⟩ := exists_radialSeq_of_closedBall_subset hR (by linarith) hp
  constructor
  · intro h
    exact (hloc (κ p.1) r hr p.2 _ _ (liftMetric_eq_on_closedBall (radialSeq_pos hR j₀) (D p.1) hj₀)).1 (h j₀ hj₀)
  · intro h j hj
    exact (hloc (κ p.1) r hr p.2 _ _ (liftMetric_eq_on_closedBall (radialSeq_pos hR j) (D p.1) hj)).2 h

/-- **Step 4: the local certificate sequence (J) is the lifted-disc indicator.** On the cutoff event
`closedBall z (7 · certScale n) ⊆ ball c R`, the decoder's certificate event at `(ℓ, z)` is the membership of `(ℓ, z)` in
`localCertSet`; off the event both sides are `0`. -/
theorem localCert_eq_localCertLoc {Ω : Type*} [MeasurableSpace Ω] {c : ℂ} {R : ℝ} (hR : 0 < R)
    (κ : Kernel Ω ℂ)
    (D : Ω → ℂ → ℂ → ℝ) {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ}
    (hloc : CertificateEventLocality Ostar U V W T Q' Q η M) (n : ℕ) (ℓ : Ω) (z : ℂ) :
    localCert (ball c R) (fun ω => κ ω) D Ostar U V W T Q' Q η M n ℓ z =
      localCertLoc c R κ D Ostar U V W T Q' Q η M n (ℓ, z) := by
  classical
  have hr : 0 < certScale n := certScale_pos n
  unfold localCert localCertLoc
  dsimp only
  by_cases hs : closedBall z (cutRadius n) ⊆ ball c R
  · have hs' : closedBall z (7 * certScale n) ⊆ ball c R := hs
    by_cases h : FirstPassS11i.CertificateEvent (κ ℓ) (D ℓ) Ostar U V W T Q' Q η M (certScale n) z
    · have hmem := (mem_localCertSet_iff_certificateEvent hR κ D hloc hr (ℓ, z) hs').2 h
      simp only [hs, hs', h, hmem, ↓reduceIte]
    · have hmem : (ℓ, z) ∉ localCertSet c R κ D Ostar U V W T Q' Q η M (certScale n) :=
        fun hm => h ((mem_localCertSet_iff_certificateEvent hR κ D hloc hr (ℓ, z) hs').1 hm)
      simp only [hs, hs', h, hmem, ↓reduceIte]
  · have hs' : ¬ closedBall z (7 * certScale n) ⊆ ball c R := hs
    simp only [hs, hs', ↓reduceIte]

/-- **Step 4-5, hc: joint measurability of the local certificate sequence (J) for a local decoder family.** The decoders
`D ω` are measurable in `ω` at each pair of points of the disc, and are length metrics on the disc for every `ω`
(this is the hypothesis that the modification of `exists_modified_failureSet_localCert` supplies). -/
theorem measurable_localCert_disc {Ω : Type*} [MeasurableSpace Ω] {c : ℂ} {R : ℝ} (hR : 0 < R)
    (κ : Kernel Ω ℂ) [IsSFiniteKernel κ] {D : Ω → ℂ → ℂ → ℝ}
    (hDm : ∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D ω x y)
    (hD : ∀ ω, IsLengthMetricOn (ball c R) (D ω))
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ} (hloc : CertificateEventLocality Ostar U V W T Q' Q η M)
    (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar) (hsph : sphere (0 : ℂ) 5 ⊆ Ostar)
    (hU : MeasurableSet U) (hη : 0 < η) (n : ℕ) :
    Measurable fun p : ℂ × Ω => localCert (ball c R) (fun ω => κ ω) D Ostar U V W T Q' Q η M n p.2 p.1 := by
  have h : Measurable (localCertLoc c R κ D Ostar U V W T Q' Q η M n) :=
    measurable_localCertLoc hR κ hDm hD hOstar h0 hsph hU hη n
  have hsw : Measurable fun p : ℂ × Ω => ((p.2, p.1) : Ω × ℂ) := measurable_snd.prodMk measurable_fst
  have heq : (fun p : ℂ × Ω => localCert (ball c R) (fun ω => κ ω) D Ostar U V W T Q' Q η M n p.2 p.1) =
      fun p => localCertLoc c R κ D Ostar U V W T Q' Q η M n (p.2, p.1) := by
    funext p
    exact localCert_eq_localCertLoc hR κ D hloc n p.2 p.1
  rw [heq]
  exact h.comp hsw

/-- **Step 5: measurability of the failure set of the local decoders.** For a measurable root set `A`, the failure set
`{(z, ℓ) | z ∈ A, the window averages of c_n(·, ℓ) at z do not converge to q}` is measurable. -/
theorem measurableSet_failureSet_disc {Ω : Type*} [MeasurableSpace Ω] {c : ℂ} {R : ℝ} (hR : 0 < R)
    (κ : Kernel Ω ℂ) [IsSFiniteKernel κ] {D : Ω → ℂ → ℂ → ℝ}
    (hDm : ∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D ω x y)
    (hD : ∀ ω, IsLengthMetricOn (ball c R) (D ω))
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ} (hloc : CertificateEventLocality Ostar U V W T Q' Q η M)
    (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar) (hsph : sphere (0 : ℂ) 5 ⊆ Ostar)
    (hU : MeasurableSet U) (hη : 0 < η) {A : Set ℂ} (hA : MeasurableSet A) (q : ℝ) :
    MeasurableSet (failureSet A (fun n x => localCert (ball c R) (fun ω => κ ω) D Ostar U V W T Q' Q η M n x.2 x.1) q) :=
  measurableSet_failureSet hA
    (fun n => measurable_localCert_disc hR κ hDm hD hloc hOstar h0 hsph hU hη n) q

/-- **Step 5 for local decoders, a.e. form.** Let `D ω` be local decoders on `ball c R`, measurable in `ω`, and a length
metric on the disc for `Pm`-almost every `ω`. Then there are a measurable set `H` with `Pm Hᶜ = 0` and a modification `D'`,
which is a length metric on the disc for every `ω` and measurable in `ω`, such that the failure set of `D'` is measurable and
agrees with that of `D` on every section over `H`. -/
theorem exists_modified_failureSet_localCert {Ω : Type*} [MeasurableSpace Ω] {c : ℂ} {R : ℝ} (hR : 0 < R)
    (κ : Kernel Ω ℂ) [IsSFiniteKernel κ] (Pm : Measure Ω) {D : Ω → ℂ → ℂ → ℝ}
    (hDm : ∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D ω x y)
    (hae : ∀ᵐ ω ∂Pm, IsLengthMetricOn (ball c R) (D ω))
    {Ostar U V W T Q' Q : Set ℂ} {η M : ℝ} (hloc : CertificateEventLocality Ostar U V W T Q' Q η M)
    (hOstar : IsOpen Ostar) (h0 : (0 : ℂ) ∈ Ostar) (hsph : sphere (0 : ℂ) 5 ⊆ Ostar)
    (hU : MeasurableSet U) (hη : 0 < η) {A : Set ℂ} (hA : MeasurableSet A) (q : ℝ) :
    ∃ H : Set Ω, MeasurableSet H ∧ Pm Hᶜ = 0 ∧ ∃ D' : Ω → ℂ → ℂ → ℝ,
      (∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D' ω x y) ∧
      (∀ ω, IsLengthMetricOn (ball c R) (D' ω)) ∧
      MeasurableSet (failureSet A (fun n x => localCert (ball c R) (fun ω => κ ω) D' Ostar U V W T Q' Q η M n x.2 x.1) q) ∧
      ∀ ω ∈ H, ∀ z : ℂ,
        ((z, ω) ∈ failureSet A (fun n x => localCert (ball c R) (fun ω => κ ω) D Ostar U V W T Q' Q η M n x.2 x.1) q ↔
          (z, ω) ∈ failureSet A (fun n x => localCert (ball c R) (fun ω => κ ω) D' Ostar U V W T Q' Q η M n x.2 x.1) q) := by
  obtain ⟨H, hH, hPH, D', hm, hl, hagree, -⟩ :=
    FirstPassS11ao.exists_measurable_localLengthModification (P := Pm) (convex_ball c R) isOpen_ball hDm hae
  refine ⟨H, hH, hPH, D', hm, hl,
    measurableSet_failureSet_disc hR κ hm hl hloc hOstar h0 hsph hU hη hA q, fun ω hω z => ?_⟩
  have hDD : D' ω = D ω := (hagree ω hω).2
  refine mem_failureSet_congr (z, ω) fun n => ?_
  dsimp only
  unfold localCert
  rw [hDD]

/-- **Step 4-5 for the model sample space, unrooted, LocalCert form.** For the whole-plane GFF model `(P, hC, hcirc)` and an
LQG metric `𝔇` of exponent `ξ`, with the decoder `m` of identity (18) (`hid`, the clause of `LocalMetricReplacementStmt`), the
local certificate sequence of the decoders `decoderOn (ball c R) (m (localMeanZeroObs α (ball c R) (hC ω)))` has a modification
`D'` with the length property for every sample, measurable, whose failure set is measurable and agrees a.s. with that of the
decoders (on the sections over `P`-a.e. `ω`). No named input: the length property is `ae_isLengthMetricOn_decoderOn` with the
cutoff `cutoffInternalLengthStmt`. -/
theorem exists_modified_failureSet_closed_localCert {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hL : IsLQGMetric γ ξ 𝔇) (hG : IsWholePlaneGFF P hC hcirc)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (h0ball : (0 : ℂ) ∉ closedBall c R)
    (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c R) φ ∧ ∫ x, φ x = 0} → ℝ) →
      ContinuousMap ↥(ball c R ×ˢ ball c R : Set (ℂ × ℂ)) ℝ)
    (hm : Measurable m) (α : ℝ)
    (hid : ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧ ∀ p : ↥(ball c R ×ˢ ball c R : Set (ℂ × ℂ)),
      ENNReal.ofReal (m (localMeanZeroObs α (ball c R) (hC ω)) p) =
        ENNReal.ofReal b * internalMetric (weylLogReal (𝔇 (hC ω)) ξ α) (ball c R) p.1.1 p.1.2)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {M : ℝ} (hU : MeasurableSet U) {A : Set ℂ} (hA : MeasurableSet A) (q : ℝ) :
    ∃ D' : Ω → ℂ → ℂ → ℝ,
      (∀ x ∈ ball c R, ∀ y ∈ ball c R, Measurable fun ω => D' ω x y) ∧
      (∀ ω, IsLengthMetricOn (ball c R) (D' ω)) ∧
      MeasurableSet (failureSet A (fun n x => localCert (ball c R) (fun ω => κ ω) D' (pinchOmegaGeom W Q δ)
        U V W T Q' Q δ M n x.2 x.1) q) ∧
      ∀ᵐ ω ∂P, ∀ z : ℂ,
        ((z, ω) ∈ failureSet A (fun n x => localCert (ball c R) (fun ω => κ ω)
            (fun ω => decoderOn (ball c R) (m (localMeanZeroObs α (ball c R) (hC ω)))) (pinchOmegaGeom W Q δ)
            U V W T Q' Q δ M n x.2 x.1) q ↔
          (z, ω) ∈ failureSet A (fun n x => localCert (ball c R) (fun ω => κ ω) D' (pinchOmegaGeom W Q δ)
            U V W T Q' Q δ M n x.2 x.1) q) := by
  have hBc : IsConnected (ball c R) := (convex_ball c R).isConnected (Metric.nonempty_ball.mpr hR)
  have hBcpt : IsCompact (closure (ball c R)) :=
    (isCompact_closedBall c R).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall
  have h0c : (0 : ℂ) ∉ closure (ball c R) := fun h => h0ball (closure_ball_subset_closedBall h)
  have hLen : ∀ᵐ ω ∂P, IsLengthMetricOn (ball c R)
      (decoderOn (ball c R) (m (localMeanZeroObs α (ball c R) (hC ω)))) :=
    ae_isLengthMetricOn_decoderOn hL hG (cutoffInternalLengthStmt ξ α) isOpen_ball hBc hBcpt h0c
      (fun ω => m (localMeanZeroObs α (ball c R) (hC ω))) hid
  have hm' : Measurable fun ω => m (localMeanZeroObs α (ball c R) (hC ω)) :=
    hm.comp (measurable_localMeanZeroObs_ae hG α (ball c R))
  have hDm := measurable_decoderOn hm'
  obtain ⟨hOo, h0O, hsph, -⟩ := FirstPassS11ap.pinchOmegaGeom_certificate_data hgeo
  obtain ⟨H, hH, hPH, D', hm', hl', hmeas, hagree⟩ :=
    exists_modified_failureSet_localCert hR κ P hDm hLen (certificateEventLocality_pinch hgeo) hOo h0O hsph hU
      hgeo.delta_pos hA q
  refine ⟨D', hm', hl', hmeas, ?_⟩
  have hHae : ∀ᵐ ω ∂P, ω ∈ H := by
    rw [ae_iff]
    exact hPH
  filter_upwards [hHae] with ω hω
  intro z
  exact hagree ω hω z

end FirstPassS11ah

end
