import HarmonicBalls.FirstPass.S11i.Step8Modified
import HarmonicBalls.FirstPass.S11i.Step8Exhaustion
import HarmonicBalls.FirstPass.S11asLocal
import HarmonicBalls.FirstPass.S11ap
import HarmonicBalls.FirstPass.S11ae
import HarmonicBalls.FirstPass.S11at
import HarmonicBalls.FirstPass.S11r.RootedHe
import HarmonicBalls.FirstPass.S11r.LocalMetricReplacement
import HarmonicBalls.FirstPass.S11r.Frozen

/-!
# Per-ball decoders of the unit-ball frequency (Step 8, fp-S11i-hzoom-scale-e, n4)

Building blocks for the doubled-disc inputs `Step8UnitBallInputs2` (HzoomUnitBallDoubled.lean), chat 238 steps 1-6, 9-11,
with the rulings of the operator (2026-11-10 15:12 UTC):

* root disc `U_p = ball c r`, decoder disc `D_p = ball c (2 r)`, `c = ballCen p`, `r = ballRad p` (`ValidBall p`);
* kernel: `κ_p := discNormalizedKernel κF_p`, where `κF_p` is the finite kernel of `exists_finite_localMeasureKernel`
  (`FirstPassS11ahFinite`, FiniteLocalKernel.lean:64) on the disc `D_p` (chat 243 Q2);
* metric: `m_p 𝔇 ℓ` is the decoder `decoderOn D_p (m₀ ℓ)` of the metric replacement `m₀` of `LocalMetricReplacementStmt`
  (S11r/LocalMetricReplacement.lean:58) for the LQG metric `𝔇`, on the good set `H_good` (the set where it is a length metric),
  and the Euclidean distance off `H_good`. The metric index `𝔇` is an explicit argument (ruling B1).

`validBall_facts`: the geometry of `ValidBall`. `ballKernel`, `ballMetric`: the decoders. `ballMetric_isLengthMetric`,
`ballMetric_measurable`: their length-metric property and measurability. `ballKernel`, `ballMetric`, `measurable_ballBad`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls.FirstPassS11iStep8Exhaustion ProbabilityTheory
open scoped Classical

namespace HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders

universe u

/-- Geometry of a valid ball: `0 < r`, the root disc `ball c r` lies in the decoder disc `ball c (2 r)`, the decoder disc
lies in the unit disc, and `0` lies outside the closed decoder disc (`ValidBall`, Step8Exhaustion.lean:44). -/
lemma validBall_facts {p : ℚ × ℚ × ℚ} (hp : ValidBall p) :
    0 < ballRad p ∧ closedBall (ballCen p) (ballRad p) ⊆ ball (ballCen p) (2 * ballRad p) ∧
      closedBall (ballCen p) (2 * ballRad p) ⊆ ball (0 : ℂ) 1 ∧ (0 : ℂ) ∉ closedBall (ballCen p) (2 * ballRad p) := by
  have hp' : 0 < ballRad p ∧ 2 * ballRad p < ‖ballCen p‖ ∧ ‖ballCen p‖ + 2 * ballRad p < 1 := hp
  obtain ⟨hr, h2, hc⟩ := hp'
  refine ⟨hr, ?_, ?_, ?_⟩
  · intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball]
    linarith
  · intro x hx
    rw [mem_closedBall] at hx
    rw [mem_ball, dist_zero_right]
    have h1 := dist_triangle x (ballCen p) (0 : ℂ)
    simp only [dist_zero_right] at h1
    linarith
  · intro h
    rw [mem_closedBall, dist_comm, dist_zero_right] at h
    linarith

/-- The finite decoder kernel `κF_p` on the decoder disc `ball c (2 r)` (`exists_finite_localMeasureKernel`, chat 243 Q2);
the zero kernel off `ValidBall`. -/
noncomputable def kernelF {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{u} γ c₁ c₂ r₁ r₂) (p : ℚ × ℚ × ℚ) :
    Kernel (FirstPassS11ahFinite.LocalObs (ballCen p) (2 * ballRad p)) ℂ :=
  if hp : ValidBall p then
    Classical.choose (FirstPassS11ahFinite.exists_finite_localMeasureKernel
      (hK (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p)) hγ0 hγ2 (validBall_facts hp).1
      (by linarith [(validBall_facts hp).1]) (validBall_facts hp).2.1 (validBall_facts hp).2.2.1
      (validBall_facts hp).2.2.2)
  else 0

/-- The normalized kernel `κ_p = discNormalizedKernel κF_p` (n3's href uses this normalization, Step8Modified.lean:51). -/
noncomputable def ballKernel {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{u} γ c₁ c₂ r₁ r₂) (p : ℚ × ℚ × ℚ) :
    Kernel (FirstPassS11ahFinite.LocalObs (ballCen p) (2 * ballRad p)) ℂ :=
  FirstPassS11iStep8Modified.discNormalizedKernel (fun ℓ => kernelF hγ0 hγ2 hK p ℓ) (kernelF hγ0 hγ2 hK p).measurable

/-- The metric replacement `m₀` of `LocalMetricReplacementStmt` for the LQG metric `𝔇` on the decoder disc of `p`
(`Classical.choose`; the constant zero map off `ValidBall`). -/
noncomputable def metricCont {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (p : ℚ × ℚ × ℚ) :
    FirstPassS11ahFinite.LocalObs (ballCen p) (2 * ballRad p) →
      ContinuousMap ↥(ball (ballCen p) (2 * ballRad p) ×ˢ ball (ballCen p) (2 * ballRad p) : Set (ℂ × ℂ)) ℝ :=
  if hp : ValidBall p then
    Classical.choose (hR (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p) hγ0 hγ2 (validBall_facts hp).1
      (by linarith [(validBall_facts hp).1]) (validBall_facts hp).2.1 (validBall_facts hp).2.2.1
      (validBall_facts hp).2.2.2 𝔇 h𝔇)
  else fun _ => 0

open Classical in
/-- The metric decoder at a valid ball: `decoderOn D_p (metricCont ℓ)` when this is a length metric on `D_p`
(the set `H_good`), the Euclidean distance otherwise. -/
noncomputable def ballMetric {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (p : ℚ × ℚ × ℚ)
    (ℓ : FirstPassS11ahFinite.LocalObs (ballCen p) (2 * ballRad p)) : ℂ → ℂ → ℝ :=
  if FirstPassS11ah.IsLengthMetricOn (ball (ballCen p) (2 * ballRad p))
      (FirstPassS11ah.decoderOn (ball (ballCen p) (2 * ballRad p)) (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p ℓ))
  then FirstPassS11ah.decoderOn (ball (ballCen p) (2 * ballRad p)) (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p ℓ)
  else fun x y => dist x y

/-- `ballMetric` is a length metric on the decoder disc, for every observation (valid or not). -/
theorem ballMetric_isLengthMetric {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (p : ℚ × ℚ × ℚ)
    (ℓ : FirstPassS11ahFinite.LocalObs (ballCen p) (2 * ballRad p)) :
    FirstPassS11ah.IsLengthMetricOn (ball (ballCen p) (2 * ballRad p)) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p ℓ) := by
  unfold ballMetric
  split_ifs with h
  · exact h
  · exact FirstPassS11ao.isLengthMetricOn_dist (convex_ball _ _) isOpen_ball

/-- The metric decoder of a valid ball is measurable in the observation, at every pair of points of the decoder disc. -/
theorem ballMetric_measurable {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇) (p : ℚ × ℚ × ℚ) (hp : ValidBall p) :
    ∀ x ∈ ball (ballCen p) (2 * ballRad p), ∀ y ∈ ball (ballCen p) (2 * ballRad p),
      Measurable fun ℓ => ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p ℓ x y := by
  classical
  have hr2 : (0 : ℝ) < 2 * ballRad p := by linarith [(validBall_facts hp).1]
  have hmc : Measurable (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p) := by
    unfold metricCont
    simp only [hp, dite_true]
    exact (Classical.choose_spec (hR (ballCen p) (ballCen p) (ballRad p) (2 * ballRad p) hγ0 hγ2
      (validBall_facts hp).1 (by linarith [(validBall_facts hp).1]) (validBall_facts hp).2.1
      (validBall_facts hp).2.2.1 (validBall_facts hp).2.2.2 𝔇 h𝔇)).1
  have hG := FirstPassS11ahLocalObsHaeGood.hGood_of_measurable hr2 hmc
  intro x hx y hy
  have hdec := FirstPassS11iStep8Modified.measurable_decoderOn_apply hmc hx hy
  have heq : (fun ℓ => ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p ℓ x y) = fun ℓ =>
      if FirstPassS11ah.IsLengthMetricOn (ball (ballCen p) (2 * ballRad p))
          (FirstPassS11ah.decoderOn (ball (ballCen p) (2 * ballRad p)) (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p ℓ))
      then FirstPassS11ah.decoderOn (ball (ballCen p) (2 * ballRad p)) (metricCont hγ0 hγ2 hR 𝔇 h𝔇 p ℓ) x y
      else dist x y := by
    funext ℓ
    unfold ballMetric
    split_ifs <;> rfl
  rw [heq]
  exact Measurable.ite hG hdec measurable_const

/-- **The local failure set is measurable** (`hBad`, chat 238 section 1; `measurable_localCert_disc` and
`measurableSet_refBadWindowSet`). Uses the buffered pinch geometry `hgeo` for the locality of the certificate event
(`certificateEventLocality_of_containments`), for the open set `Ostar` and for the sphere in `Ostar`. -/
theorem measurableSet_ballBad {γ ξ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hK : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMeasureKernelStmt.{u} γ c₁ c₂ r₁ r₂)
    (hR : ∀ c₁ c₂ : ℂ, ∀ r₁ r₂ : ℝ, HarmonicBalls.LocalMetricReplacementStmt.{u} γ ξ c₁ c₂ r₁ r₂)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    {U V W T Q' Q : Set ℂ} {δ M : ℝ} (hgeo : HarmonicBalls.IsBufferedPinchGeometry U V W T Q' Q δ)
    (q : ℝ) (p : ℚ × ℚ × ℚ) (hp : ValidBall p) :
    MeasurableSet (HarmonicBalls.ReferenceNullS11i.refBadWindowSet
      (FirstPassS11ai.localCertSeq (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ) (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p)
        (pinchOmegaGeom W Q δ) U V W T Q' Q δ M) q) := by
  have hr2 : (0 : ℝ) < 2 * ballRad p := by linarith [(validBall_facts hp).1]
  have hz := FirstPassS11ap.zero_union_sphere_subset_pinchOmegaGeom hgeo
  have h0 : (0 : ℂ) ∈ pinchOmegaGeom W Q δ := hz (Set.mem_insert _ _)
  have hsph : sphere (0 : ℂ) 5 ⊆ pinchOmegaGeom W Q δ :=
    (Set.subset_insert _ _).trans hz
  have hloc := FirstPassS11ah.certificateEventLocality_of_containments (U := U) (M := M)
    (FirstPassS11ap.certificateContainments_of_buffered hgeo)
  have hfin : IsFiniteKernel (ballKernel hγ0 hγ2 hK p) :=
    FirstPassS11iStep8Modified.isFiniteKernel_discNormalizedKernel _ _
  have hseq : ∀ n : ℕ, Measurable (FirstPassS11ai.localCertSeq (fun ℓ => ballKernel hγ0 hγ2 hK p ℓ)
      (ballMetric hγ0 hγ2 hR 𝔇 h𝔇 p) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M n) := fun n =>
    haveI := hfin
    FirstPassS11ah.measurable_localCert_disc hr2 (ballKernel hγ0 hγ2 hK p)
      (ballMetric_measurable hγ0 hγ2 hR 𝔇 h𝔇 p hp) (fun ℓ => ballMetric_isLengthMetric hγ0 hγ2 hR 𝔇 h𝔇 p ℓ)
      hloc (FirstPassS11ap.isOpen_pinchOmegaGeom W Q δ) h0 hsph hgeo.isOpen_U.measurableSet hgeo.delta_pos n
  exact HarmonicBalls.ReferenceNullS11i.measurableSet_refBadWindowSet _ hseq q

/-- **Scalar invariance of the certificate event at a centre `z`.** Centred form of
`FirstPassS11asLocal.certificateEvent_of_restrict_scalar` (S11asLocal.lean:96), same proof with `0` replaced by `z`. -/
theorem certificateEvent_of_restrict_scalar_at (μ μ' : Measure ℂ) (D D' : ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ)
    (η M r : ℝ) (z : ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hC : FirstPassS11i.CertificateContainments η Ostar V W T Q' Q) (hU : U ⊆ closedBall 0 7) (hr : 0 < r)
    (hμ : μ.restrict (closedBall z (7 * r)) = (ENNReal.ofReal a • μ').restrict (closedBall z (7 * r)))
    (hD : Set.EqOn (Function.uncurry D) (Function.uncurry (fun x y => b * D' x y))
      (closedBall z (7 * r) ×ˢ closedBall z (7 * r))) :
    FirstPassS11i.CertificateEvent μ D Ostar U V W T Q' Q η M r z ↔
      FirstPassS11i.CertificateEvent μ' D' Ostar U V W T Q' Q η M r z := by
  refine Iff.trans (FirstPassS11i.certificateEvent_congr_of_eqOn_closedBall (U := U) hC hr hD) ?_
  refine Iff.trans (FirstPassS11aq.certificateEvent_measure_congr (fun x y => b * D' x y) Ostar U V W T Q' Q η M r z
    hr hU hμ) ?_
  exact FirstPassS11asLocal.certificateEvent_smul_iff μ' D' Ostar U V W T Q' Q η M r z ha hb

end HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders

#print axioms HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders.ballMetric_isLengthMetric
#print axioms HarmonicBalls.FirstPassS11iHzoomUnitBallDecoders.certificateEvent_of_restrict_scalar_at
