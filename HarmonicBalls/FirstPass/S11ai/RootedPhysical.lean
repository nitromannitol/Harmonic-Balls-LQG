import HarmonicBalls.FirstPass.S11ai.RootedInstance
import HarmonicBalls.FirstPass.S11ai.RootedCovariance
import HarmonicBalls.FirstPass.S11ai.ShiftCutoff
import HarmonicBalls.FirstPass.S11ap
import HarmonicBalls.FirstPass.S11aq

/-!
# Local rooted covariance: the physical rooted pair from the frozen decoders (fp-S11ai-11-13-steps-6-7c, hCov)

Operator note 05:52 UTC (chat 181): no new decoder hypothesis. The physical rooted pair at a root `z` is defined from the
canonical decoders `Dμ`, `Dd` (`LQGCanonicalDecodersExistStmt` at `α₀ := γ`), applied to the root-shifted canonical field
`canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) v)`, where `v` is a smooth shift equal to `-α₀ log|z + ·|`
on a ball about `0` (`rootShift`). Its certificate at scale `2^{-n}` about `z` is compared with the unit-scale certificate of
the dilated canonical pair:
* `certificateEvent_rootedPhys_congr`: the certificate depends only on the measure on `closedBall z (7r)` and on the metric
  on its square, for `Ostar = pinchOmegaGeom W Q δ` and `η = δ` (`FirstPassS11aq.certificateEvent_measure_congr_buffered`,
  `FirstPassS11ap.certificateEvent_pinch_congr`);
* `FirstPassS11ai.certificateEvent_rooted_iff` (deterministic translation and dilation).

Two decoder-level local identities are NOT provided by the frozen decoder identification, which is stated for whole-plane
GFF models only (`LQGCanonicalIdentificationStmt`): window locality of the decoders of the root-shifted fields, and the
dilation identity of `ae_decoders_dilOp_iterate` for the root-shifted (Cameron-Martin shifted) canonical field. They are
explicit hypotheses of `rooted_covariance_window`; they are reported as blockers, not assumed silently.
-/

namespace FirstPassS11ai

open MeasureTheory Set Metric
open scoped ENNReal
open HarmonicBalls HarmonicBalls.S11c

/-- The root shift at `α₀` and `z`: smooth, compactly supported, zero unit-circle average, equal to `-α₀ log|z + ·|` on
`ball 0 (rootRadius z)` (`exists_shift_cutoff`). Defined as `0` when `z = 0` (never used there). -/
noncomputable def rootShift (α₀ : ℝ) (z : ℂ) : ℂ → ℝ :=
  if hz : 0 < ‖z‖ then
    Classical.choose (exists_shift_cutoff z α₀ (rootRadius_pos hz) (two_mul_rootRadius_lt hz)
      (two_mul_rootRadius_lt_one z))
  else fun _ => 0

/-- The root shift is an admissible root shift at `z` with radius `rootRadius z`, for `z ≠ 0`. -/
theorem rootShift_admissible (α₀ : ℝ) {z : ℂ} (hz : 0 < ‖z‖) :
    AdmissibleRootShift α₀ z (rootRadius z) (rootShift α₀ z) := by
  unfold rootShift
  split_ifs
  have hs := Classical.choose_spec (exists_shift_cutoff z α₀ (rootRadius_pos hz) (two_mul_rootRadius_lt hz)
    (two_mul_rootRadius_lt_one z))
  exact ⟨rootRadius_pos hz, two_mul_rootRadius_lt hz, two_mul_rootRadius_lt_one z, hs.1, hs.2.1, hs.2.2.1,
    hs.2.2.2⟩

/-- The root-shifted canonical field `canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) v)`. -/
noncomputable def rootedCanon {Ω : Type*} (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ)
    (v : ℂ → ℝ) (ω : Ω) : ModConstTestPairings (Set.univ : Set ℂ) :=
  canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) v)

/-- The physical rooted measure at `z`: the decoded measure of the root-shifted canonical field, translated to `z`
(the convention `μ.map (· - -z)` of `certificateEvent_translate_iff`). -/
noncomputable def rootedPhysMeasure {Ω : Type*} (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (v : ℂ → ℝ) (ω : Ω) : Measure ℂ :=
  (Dμ (rootedCanon γ hC hcirc z v ω)).map (fun w : ℂ => w - -z)

/-- The physical rooted metric at `z`: the decoded metric of the root-shifted canonical field, translated to `z`. -/
noncomputable def rootedPhysMetric {Ω : Type*} (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ) (γ : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (z : ℂ) (v : ℂ → ℝ) (ω : Ω) : ℂ → ℂ → ℝ :=
  fun x y => Dd (rootedCanon γ hC hcirc z v ω) (x + -z) (y + -z)

/-- **Local certificate congruence.** For `Ostar = pinchOmegaGeom W Q δ` and `η = δ`, the certificate at `(r, z)` depends
only on the measure restricted to `closedBall z (7r)` and on the metric restricted to `closedBall z (7r) × closedBall z (7r)`. -/
theorem certificateEvent_rootedPhys_congr {U V W T Q' Q : Set ℂ} {δ M r : ℝ} {z : ℂ}
    (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ) (hr : 0 < r) (μ μ' : Measure ℂ) (D D' : ℂ → ℂ → ℝ)
    (hμ : μ.restrict (closedBall z (7 * r)) = μ'.restrict (closedBall z (7 * r)))
    (hD : EqOn (Function.uncurry D) (Function.uncurry D') (closedBall z (7 * r) ×ˢ closedBall z (7 * r))) :
    FirstPassS11i.CertificateEvent μ D (pinchOmegaGeom W Q δ) U V W T Q' Q δ M r z ↔
      FirstPassS11i.CertificateEvent μ' D' (pinchOmegaGeom W Q δ) U V W T Q' Q δ M r z :=
  (FirstPassS11aq.certificateEvent_measure_congr_buffered hgeo D (pinchOmegaGeom W Q δ) δ M r z hr
    hμ).trans (FirstPassS11ap.certificateEvent_pinch_congr hgeo hr hD)

/-- **Local rooted covariance (hCov, physical form).** Let `v = rootShift α₀ z` (the root shift of the physical pair) and
`u` any shift with the same window behaviour. Then the certificate of the physical rooted pair at scale `2^{-n}` about `z`
is the unit-scale certificate of the dilated canonical pair at `u`, under the two decoder-level local identities:
* `hLocμ`, `hLocd` (window locality): on the window `closedBall z (cutRadius n)`, the physical measure and metric of the
  shift `v` agree with those of `u` (the two shifts equal `-α₀ log|z + ·|` on the window, `hwin`, `hwinz`);
* `hDil` (dilation): the decoders of the dilated shifted canonical field are the dilations of those of the shifted field,
  as in `ae_decoders_dilOp_iterate`, with the Cameron-Martin transfer to the shifted field. NOT PROVED (blocker). -/
theorem rooted_covariance_window {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    {U V W T Q' Q : Set ℂ} {δ M : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    (z : ℂ) (n : ℕ) (b : ℝ) (u : ℂ → ℝ)
    (hwin : closedBall z (FirstPassS11ah.cutRadius n) ⊆ ball z b)
    (hwinz : closedBall z (FirstPassS11ah.cutRadius n) ⊆ ball z (rootRadius z))
    (hLocμ : closedBall z (FirstPassS11ah.cutRadius n) ⊆ ball z b →
      closedBall z (FirstPassS11ah.cutRadius n) ⊆ ball z (rootRadius z) →
      ∀ᵐ ω ∂P,
        (rootedPhysMeasure Dμ γ hC hcirc z (rootShift α₀ z) ω).restrict (closedBall z (FirstPassS11ah.cutRadius n)) =
          (rootedPhysMeasure Dμ γ hC hcirc z u ω).restrict (closedBall z (FirstPassS11ah.cutRadius n)))
    (hLocd : closedBall z (FirstPassS11ah.cutRadius n) ⊆ ball z b →
      closedBall z (FirstPassS11ah.cutRadius n) ⊆ ball z (rootRadius z) →
      ∀ᵐ ω ∂P, EqOn (Function.uncurry (rootedPhysMetric Dd γ hC hcirc z (rootShift α₀ z) ω))
        (Function.uncurry (rootedPhysMetric Dd γ hC hcirc z u ω))
        (closedBall z (FirstPassS11ah.cutRadius n) ×ˢ closedBall z (FirstPassS11ah.cutRadius n)))
    (hDil : ∀ᵐ ω ∂P, ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      Dμ (dilOp^[n] (rootedCanon γ hC hcirc z u ω)) =
        ENNReal.ofReal a • (Dμ (rootedCanon γ hC hcirc z u ω)).map
          (fun w : ℂ => w / ((FirstPassS11ah.certScale n : ℝ) : ℂ)) ∧
      ∀ x y : ℂ, Dd (dilOp^[n] (rootedCanon γ hC hcirc z u ω)) x y =
        c * Dd (rootedCanon γ hC hcirc z u ω) (((FirstPassS11ah.certScale n : ℝ) : ℂ) * x)
          (((FirstPassS11ah.certScale n : ℝ) : ℂ) * y)) :
    ∀ᵐ ω ∂P,
      FirstPassS11i.CertificateEvent (rootedPhysMeasure Dμ γ hC hcirc z (rootShift α₀ z) ω)
          (rootedPhysMetric Dd γ hC hcirc z (rootShift α₀ z) ω) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M
          (FirstPassS11ah.certScale n) z ↔
        FirstPassS11i.CertificateEvent (Dμ (dilOp^[n] (rootedCanon γ hC hcirc z u ω)))
          (Dd (dilOp^[n] (rootedCanon γ hC hcirc z u ω))) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M 1 0 := by
  have hR : 0 < FirstPassS11ah.certScale n := by
    unfold FirstPassS11ah.certScale
    positivity
  filter_upwards [hLocμ hwin hwinz, hLocd hwin hwinz, hDil] with ω h1 h2 h3
  obtain ⟨a, c, ha, hc, hμd, hdd⟩ := h3
  have hdd' : Dd (dilOp^[n] (rootedCanon γ hC hcirc z u ω)) =
      fun x y => c * Dd (rootedCanon γ hC hcirc z u ω) (((FirstPassS11ah.certScale n : ℝ) : ℂ) * x)
        (((FirstPassS11ah.certScale n : ℝ) : ℂ) * y) :=
    funext fun x => funext fun y => hdd x y
  refine (certificateEvent_rootedPhys_congr hgeo hR _ _ _ _ h1 h2).trans ?_
  have hrooted := certificateEvent_rooted_iff (Dμ (rootedCanon γ hC hcirc z u ω))
    (Dd (rootedCanon γ hC hcirc z u ω)) (pinchOmegaGeom W Q δ) U V W T Q' Q δ M z n ha hc
  rw [hμd, hdd']
  exact hrooted

end FirstPassS11ai
