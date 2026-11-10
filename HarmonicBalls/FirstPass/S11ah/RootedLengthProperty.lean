import HarmonicBalls.FirstPass.S11ah.Step5Rooted
import HarmonicBalls.FirstPass.S11ah.LQGDecoder
import HarmonicBalls.FirstPass.S11r.RootedLengthFields
import HarmonicBalls.FirstPass.S11r.RootedRootFinite
import HarmonicBalls.FirstPass.S11r.RootedDecoder
import HarmonicBalls.FirstPass.S11r.Frozen

/-!
# The rooted length property, and Step 5 for the rooted decoders with it discharged (fp-S11ah-11-13-steps-4-5e, owner n4)

Proves the named hypothesis `RootedLengthPropertyStmt` (`S11ah/Step5Rooted.lean`) from three inputs that are in the
repository: identity (20) of `LocalMetricReplacementStmt` (`S11r/LocalMetricReplacement.lean`), taken as an explicit
hypothesis `hid` (its clause for the insertion `α < Q_γ`); the frozen continuity of the rooted physical metric at the
insertion, `RootedPhysicalMetricContinuousAtInsertionFrozen` (`S11r/Frozen.lean`, DFGPS Proposition 3.17); and the LQG
axiom I, `ae_isEuclideanLengthMetric_of_lqg` (`S11ah/LQGDecoder.lean`). No new input.

Route (ChatGPT PRO verdict on the rooted length property, section 5.1, operator note 2026-11-10):
* `internalPhysicalMetric_lengthFields_full` (n2, `S11r/RootedLengthFields.lean`) gives the seven fields of
  `IsLengthMetricOn B (internalReal (weylPhysicalE d ξ f) B)` for the physical internal metric of the rooted field `f`;
* identity (20) gives `ofReal (decoder p) = ofReal b · internalMetric (weylPhysicalE d ξ f) B p` on `B × B`;
* `isLengthMetricOn_decoderOn` (`S11ah/LQGDecoder.lean`) transports the length property to the decoder. Its proof treats the
  sign of the decoder (positivity off the diagonal, continuity on the diagonal), so identity (20) is not reduced to real
  numbers by a bare `toReal`, as the PRO verdict requires.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology HarmonicBalls
open scoped ENNReal

namespace FirstPassS11ah

/-- **Deterministic rooted transport.** Let `d` be a Euclidean length metric, `B` an open connected set containing the root
`z`, and `f` continuous on `B \ {z}` with `weylScaling d ξ f · z → 0` at `z`. If a continuous decoder `m` on `B × B` satisfies
`ofReal (m p) = ofReal b · internalMetric (weylPhysicalE d ξ f) B p` for some `b > 0`, then `decoderOn B m` is a Euclidean
length metric on `B` (`IsLengthMetricOn B`). -/
theorem isLengthMetricOn_decoderOn_rooted {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ : ℝ) {f : ℂ → ℝ}
    {B : Set ℂ} (hBo : IsOpen B) (hBc : IsConnected B) {z : ℂ} (hz : z ∈ B) (hfc : ContinuousOn f (B \ {z}))
    (hW : Tendsto (fun x => weylScaling d ξ f x z) (𝓝 z) (𝓝 0))
    (m : ContinuousMap ↥(B ×ˢ B : Set (ℂ × ℂ)) ℝ) {b : ℝ} (hb : 0 < b)
    (hid : ∀ p : ↥(B ×ˢ B : Set (ℂ × ℂ)),
      ENNReal.ofReal (m p) = ENNReal.ofReal b * internalMetric (weylPhysicalE d ξ f) B p.1.1 p.1.2) :
    IsLengthMetricOn B (decoderOn B m) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := internalPhysicalMetric_lengthFields_full hd ξ hBo hBc hz hfc hW
  have hR : IsLengthMetricOn B (internalReal (weylPhysicalE d ξ f) B) :=
    { self_eq_zero := h1
      eq_of_eq_zero := h6
      symm := fun x _ y _ => h2 x y
      triangle := h3
      continuousOn := h5
      isOpen_iff := h7
      ofReal_eq_internalMetric := h4 }
  exact isLengthMetricOn_decoderOn hBo (finite_on_disk_root hd ξ hBo hBc hz hfc hW).2 hR m hb hid

/-- **The rooted length property, proved.** Let `γ ∈ (0, 2)`, `α < Q_γ`, `𝔇` an LQG metric, and let `m` be a decoder family
satisfying identity (20) of `LocalMetricReplacementStmt` for this `α` (hypothesis `hid`, for the given probability space).
Then, for Lebesgue-a.e. root `z` in `ball c₁ r₁` and `P`-a.s. `ω`, the rooted decoder is a Euclidean length metric on `ball c₂ r₂`.
The root `z` lies in `ball c₂ r₂` and differs from `0`, since `closedBall c₁ r₁ ⊆ ball c₂ r₂` and `0 ∉ closedBall c₂ r₂`. -/
theorem rootedLengthProperty {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {γ ξ α : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hG : IsWholePlaneGFF P hC hcirc)
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hL : IsLQGMetric γ ξ 𝔇)
    (hfr : RootedPhysicalMetricContinuousAtInsertionFrozen.{0}) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hcl : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) →
      ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ)
    (hid : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
        ENNReal.ofReal (m (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (weylPhysicalE (𝔇 (hC ω)) ξ
            (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)))
            (ball c₂ r₂) p.1.1 p.1.2) :
    RootedLengthPropertyStmt γ α c₁ c₂ r₁ r₂ P hC m := by
  have hbase : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := ae_isEuclideanLengthMetric_of_lqg hL hG
  filter_upwards [hid, ae_restrict_mem isOpen_ball.measurableSet] with z hzid hzU
  have hzB : z ∈ ball c₂ r₂ := hcl (ball_subset_closedBall hzU)
  have hz0 : z ≠ 0 := by
    rintro rfl
    exact h0 (ball_subset_closedBall hzB)
  have hD0 : (0 : ℂ) ∉ ball c₂ r₂ := fun h => h0 (ball_subset_closedBall h)
  have hBc : IsConnected (ball c₂ r₂) := (convex_ball c₂ r₂).isConnected ⟨z, hzB⟩
  have hfc := rootedWeight_continuousOn (D := ball c₂ r₂) (z := z) hD0 α γ
  filter_upwards [hzid, hfr γ ξ α z hγ0 hγ2 hα hz0 Ω P hC hcirc hG 𝔇 hL, hbase] with ω hω hWω hdω
  obtain ⟨b, hb, hbid⟩ := hω
  exact isLengthMetricOn_decoderOn_rooted hdω ξ isOpen_ball hBc hzB hfc hWω
    (m (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2) hb hbid

/-- **Step 5 for the rooted decoders, with the rooted length property discharged.** This is
`exists_modified_failureSet_rooted_localCert` (`S11ah/Step5Rooted.lean`) with its hypothesis `hLen` replaced by
`rootedLengthProperty`; the remaining inputs are identity (20) for the decoder `m` (`hid`, the rooted clause of
`LocalMetricReplacementStmt`), the LQG metric `𝔇`, and the frozen rooted continuity `hfr`. -/
theorem exists_modified_failureSet_rooted_localCert_discharged {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {γ α ξ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC hcirc) {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₂ : 0 < r₂) (κ : Kernel Ω ℂ) [IsSFiniteKernel κ]
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) →
      ContinuousMap ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)) ℝ)
    (hm : Measurable m) {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hL : IsLQGMetric γ ξ 𝔇)
    (hfr : RootedPhysicalMetricContinuousAtInsertionFrozen.{0}) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hcl : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h0 : (0 : ℂ) ∉ closedBall c₂ r₂)
    (hid : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ᵐ ω ∂P, ∃ b : ℝ, 0 < b ∧
      ∀ p : ↥(ball c₂ r₂ ×ˢ ball c₂ r₂ : Set (ℂ × ℂ)),
        ENNReal.ofReal (m (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2 p) =
          ENNReal.ofReal b * internalMetric (weylPhysicalE (𝔇 (hC ω)) ξ
            (fun w => -α * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)))
            (ball c₂ r₂) p.1.1 p.1.2)
    {U V W T Q' Q : Set ℂ} {δ : ℝ} (hgeo : IsBufferedPinchGeometry U V W T Q' Q δ)
    {M : ℝ} (hU : MeasurableSet U) {A : Set ℂ} (hA : MeasurableSet A) (q : ℝ) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∃ D' : Ω → ℂ → ℂ → ℝ,
      (∀ x ∈ ball c₂ r₂, ∀ y ∈ ball c₂ r₂, Measurable fun ω => D' ω x y) ∧
      (∀ ω, IsLengthMetricOn (ball c₂ r₂) (D' ω)) ∧
      MeasurableSet (failureSet A (fun n x => localCert (ball c₂ r₂) (fun ω => κ ω) D' (pinchOmegaGeom W Q δ)
        U V W T Q' Q δ M n x.2 x.1) q) ∧
      ∀ᵐ ω ∂P, ∀ z' : ℂ,
        ((z', ω) ∈ failureSet A (fun n x => localCert (ball c₂ r₂) (fun ω => κ ω)
            (fun ω => decoderOn (ball c₂ r₂) (m (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2))
            (pinchOmegaGeom W Q δ) U V W T Q' Q δ M n x.2 x.1) q ↔
          (z', ω) ∈ failureSet A (fun n x => localCert (ball c₂ r₂) (fun ω => κ ω) D' (pinchOmegaGeom W Q δ)
            U V W T Q' Q δ M n x.2 x.1) q) :=
  exists_modified_failureSet_rooted_localCert hG hr₂ κ m hm
    (rootedLengthProperty hG hL hfr hγ0 hγ2 hα hcl h0 m hid) hgeo hU hA q

end FirstPassS11ah
