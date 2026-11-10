import HarmonicBalls.FirstPass.S11i.CertDilate
import HarmonicBalls.FirstPass.Frozen.S11c

/-!
# Certificate identification for `hId` (fp-S11ai-11-13-steps-6-7, operator note 03:55 UTC)

Source: `notes/fp-gaps/CHATGPT-n1-n2-11-13-inputs.md` §1.2 (identifications (1)-(4)) and §1.3 (Steps 4-6).

Deterministic lemmas proved here:
* `certificateEvent_scale_iff`: the certificate event `𝓔_r(μ, D; z, M)` is invariant under independent positive scalings of
  its measure and of its metric (§1.2(3), invariance clause; used in §1.3 Step 6 to remove the two decoder factors).
  It is the case `R = 1` of `certificateEvent_dilate_iff` (dilation covariance, rule [C43]).
* `campbellReferenceObs_eq_rootedMeanZeroObs`: for `closedBall c₂ r₂ ⊆ ball 0 1` the reference observation of the Campbell
  marked field equals the rooted mean-zero observation `rootedMeanZeroObs`, the input of the frozen common decoder
  `LocalLQGDecoderCommonFrozen` (clause 2, §1.3 Step 4 eq. (6)). The Campbell logarithm `log max(1,|w|)` vanishes on the
  support of every test function on `D ⊆ B_1`.

Not proved here (see the report of the round): the rooted metric decoder identity (§1.3 Step 4 eq. (7)), the
covariance of the rooted LQG measure and metric under `dilOp`, the scale-one identification of `F` (§1.2(2)), and the
translation covariance of the certificate event (§1.3 Step 6).
-/

namespace FirstPassS11ai

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls

/-- **Scaling invariance of the certificate event (§1.2(3), §1.3 Step 6).** Independent positive scalings of the
measure (`a`) and of the metric (`b`) do not change `𝓔_r(μ, D; z, M)`: every strict inequality in the certificate
compares a quantity linear in the measure with one linear in the metric, or a metric quantity with a metric quantity. -/
theorem certificateEvent_scale_iff (μ : Measure ℂ) (D : ℂ → ℂ → ℝ) (Ostar U V W T Q' Q : Set ℂ) (η M r : ℝ) (z : ℂ)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    FirstPassS11i.CertificateEvent (ENNReal.ofReal a • μ) (fun u v => b * D u v) Ostar U V W T Q' Q η M r z ↔
      FirstPassS11i.CertificateEvent μ D Ostar U V W T Q' Q η M r z := by
  have h := HarmonicBalls.FirstPassS11iCertDilate.certificateEvent_dilate_iff μ D Ostar U V W T Q' Q η M r z
    (R := 1) one_pos ha hb
  simpa [Measure.map_id] using h

/-- **Reference observation equals rooted observation on `D ⊆ B_1` (§1.3 Step 4, input of `LocalLQGDecoderCommonFrozen`).**
The extra Campbell term `γ ∫ log max(1,|w|) φ(w) dw` vanishes for every test function `φ` supported in `D`, since
`max(1,|w|) = 1` on `D ⊆ B_1`. -/
theorem campbellReferenceObs_eq_rootedMeanZeroObs (γ α₀ : ℝ) (c₂ : ℂ) (r₂ : ℝ)
    (hsub : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    campbellReferenceObs γ α₀ (ball c₂ r₂) hC z = (z, rootedMeanZeroObs α₀ γ (ball c₂ r₂) z hC) := by
  unfold campbellReferenceObs rootedMeanZeroObs
  refine Prod.ext rfl ?_
  funext φ
  have hint : ∀ w : ℂ, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ.1 w = Real.log ‖w - z‖ * φ.1 w := by
    intro w
    by_cases hw : w ∈ ball c₂ r₂
    · have hw1 : ‖w‖ ≤ 1 := by
        have h1 := hsub (ball_subset_closedBall hw)
        rw [mem_ball_zero_iff] at h1
        exact h1.le
      rw [max_eq_left hw1, Real.log_one, sub_zero]
    · have h0 : φ.1 w = 0 := by
        by_contra hne
        exact hw (φ.2.1.2.2 (subset_tsupport _ (Function.mem_support.2 hne)))
      simp [h0]
  simp only [hint]

end FirstPassS11ai
