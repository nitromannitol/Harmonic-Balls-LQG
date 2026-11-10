import HarmonicBalls.FirstPass.S11ai.RootedIdentification
import HarmonicBalls.FirstPass.S11ah.LocalCert

/-!
# Rooted instance of the shared certificate identification, and the termwise identity `hT` from it
(fp-S11ai-11-13-steps-6-7, operator note 04:20 UTC)

Source: `notes/fp-gaps/CHATGPT-n3-identification.md` §5.2 (instance used by n1) and §5.3, with §1.2-§1.3 of
`notes/fp-gaps/CHATGPT-n1-n2-11-13-inputs.md`.

n3's shared structure `CertificateIdentification` (chat 152 §5) is not yet committed. Its clauses are stated here inline,
with the same content, so that n3's name can replace them when it exists:
* `hSeq` (sequence_eq): `c` is the truncated `localCert` sequence (J) of Step 4;
* `hFit` (fitting_eq, rooted instance): for a.e. root `z ∈ A`, the decoded certificate of the rooted observation equals
  the physical rooted certificate, for every centre and scale whose buffered cutoff ball lies in `D`;
* `hCov` (covariance, §1.3 Step 6): the physical rooted certificate at scale `2^{-n}` equals the unit-scale certificate of
  the dilated, translated canonical pairing. NOT SOURCED: no Prop in External or Proposed; reported as a blocker;
* `hG` (scale_one_eq, transferred): the unit-scale coding identity `unitObs ∈ F ↔ 𝓔_1(μ₀, d₀)` evaluated at the dilated,
  translated canonical pairing, almost surely for the sample field. The transfer from the canonical law `P₀` to the law of
  the translated field needs the Cameron–Martin input (§1.3 Step 5). NOT SOURCED as a transfer; reported.

Proved here: `ae_termwise_of_identification` (hT from these clauses, with the eventual cutoff inclusion
`eventually_closedBall_cutRadius_subset`), and the entry `ae_quantum_bad_mass_eq_zero_of_identification`.
-/

universe u

namespace FirstPassS11ai

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls
open HarmonicBalls.S11c

/-- The admissible shift data of §1.3 Step 2 at a root `z`: radius `b` and smooth, compactly supported `u` with zero
unit-circle average, equal to `-α₀ log ‖z + ·‖` on `ball 0 b`. (Same clauses as `hT` in `ae_rootedId_of_termwise`.) -/
def AdmissibleRootShift (α₀ : ℝ) (z : ℂ) (b : ℝ) (u : ℂ → ℝ) : Prop :=
  0 < b ∧ 2 * b < ‖z‖ ∧ 2 * b < 1 ∧ ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧
    Real.circleAverage u 0 1 = 0 ∧ ∀ w ∈ ball (0 : ℂ) b, u w = -α₀ * Real.log ‖z + w‖

/-- The buffered cutoff balls `closedBall z (7 · 2^{-n})` of (J) eventually lie in any open ball containing `z`. -/
theorem eventually_closedBall_cutRadius_subset {c₂ z : ℂ} {r₂ : ℝ} (hz : z ∈ ball c₂ r₂) :
    ∀ᶠ n : ℕ in atTop, closedBall z (FirstPassS11ah.cutRadius n) ⊆ ball c₂ r₂ := by
  obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.1 (Metric.isOpen_ball : IsOpen (ball c₂ r₂)) z hz
  have ht : Tendsto (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  filter_upwards [ht.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 7 by positivity))] with n hn
  refine (Metric.closedBall_subset_ball ?_).trans hsub
  unfold FirstPassS11ah.cutRadius FirstPassS11ah.certScale
  linarith

/-- **Termwise identity `hT` from the shared identification (§1.3 Steps 4-6, deterministic composition).**
For a.e. root `z ∈ A`, every admissible `(b, u)` and almost surely, the certificate sequence `c` at the rooted observation
equals the scale-one indicator of `F` at the dilated, translated canonical pairing, for all large `n`. -/
theorem ae_termwise_of_identification
    {γ α₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ}
    (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂) (A : Set ℂ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (c : ℕ → (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) → ℝ)
    (hSeq : ∀ (n : ℕ) (z : ℂ) (ℓ : {φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ),
      c n (z, ℓ) = FirstPassS11ah.localCert (ball c₂ r₂) κ m Ostar U V W T Q' Q η M n ℓ z)
    (μR : ℂ → Ω → Measure ℂ) (dR : ℂ → Ω → ℂ → ℂ → ℝ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))}
    (hFit : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ᵐ ω ∂P, ∀ (z' : ℂ) (n : ℕ),
      closedBall z' (FirstPassS11ah.cutRadius n) ⊆ ball c₂ r₂ →
        (FirstPassS11i.CertificateEvent (κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2)
            (m (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2) Ostar U V W T Q' Q η M
            (FirstPassS11ah.certScale n) z' ↔
          FirstPassS11i.CertificateEvent (μR z ω) (dR z ω) Ostar U V W T Q' Q η M
            (FirstPassS11ah.certScale n) z'))
    (hCov : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ, closedBall z (FirstPassS11ah.cutRadius n) ⊆ ball c₂ r₂ →
        (FirstPassS11i.CertificateEvent (μR z ω) (dR z ω) Ostar U V W T Q' Q η M
            (FirstPassS11ah.certScale n) z ↔
          FirstPassS11i.CertificateEvent
            (Dμ (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            (Dd (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            Ostar U V W T Q' Q η M 1 0))
    (hG : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
        (FirstPassS11i.CertificateEvent
            (Dμ (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            (Dd (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            Ostar U V W T Q' Q η M 1 0 ↔
          ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))) ∈ F)) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), 0 < b → 2 * b < ‖z‖ → 2 * b < 1 →
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u → Real.circleAverage u 0 1 = 0 →
      (∀ w ∈ ball (0 : ℂ) b, u w = -α₀ * Real.log ‖z + w‖) → ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀,
        c n (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) =
          (ballRestrictPairing 7 ⁻¹' F).indicator (fun _ => (1 : ℝ))
            (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))) := by
  classical
  filter_upwards [hFit, hCov, hG,
    ae_restrict_mem (μ := (volume : Measure ℂ)) (measurableSet_ball : MeasurableSet (ball c₁ r₁))]
    with z hFz hCz hGz hzB hzA b u hb hbz hb1 hu hcomp hu0 hu_eq
  have hzD : z ∈ ball c₂ r₂ := hsub (ball_subset_closedBall hzB)
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 (eventually_closedBall_cutRadius_subset hzD)
  have hadm : AdmissibleRootShift α₀ z b u := ⟨hb, hbz, hb1, hu, hcomp, hu0, hu_eq⟩
  filter_upwards [hFz hzA, hCz hzA b u hadm, hGz hzA b u hadm] with ω h1 h2 h3
  refine ⟨n₀, fun n hn => ?_⟩
  have hs : closedBall z (FirstPassS11ah.cutRadius n) ⊆ ball c₂ r₂ := hn₀ n hn
  change c n (z, (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2) = _
  rw [hSeq, FirstPassS11ah.localCert_of_subset hs]
  have hkey := (h1 z n hs).trans ((h2 n hs).trans (h3 n))
  rw [Set.indicator_apply]
  simp only [Set.mem_preimage]
  by_cases hE : FirstPassS11i.CertificateEvent
      (κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2)
      (m (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2) Ostar U V W T Q' Q η M
      (FirstPassS11ah.certScale n) z
  · have hF := hkey.1 hE
    simp only [hE, hF, ite_true]
  · have hF : ¬ (ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ (addFunPairing
        (translatedPairing hC hcirc z ω) u))) ∈ F) := fun h => hE (hkey.2 h)
    simp only [hE, hF, ite_false]

/-- **Entry for n3 with the shared identification in place of `hT`.** Same conclusion as
`ae_quantum_bad_mass_eq_zero_of_termwise`; the termwise identity is `ae_termwise_of_identification` applied to the
clauses `hSeq`, `hFit`, `hCov`, `hG`. -/
theorem ae_quantum_bad_mass_eq_zero_of_identification
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : HarmonicBalls.LocalCampbellMarkedRestrictionFrozen.{u})
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (h0 : (0 : ℂ) ∉ closedBall c₂ r₂) (A : Set ℂ) (Ostar U V W T Q' Q : Set ℂ) (η M : ℝ)
    (κ : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → Measure ℂ)
    (m : ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ) → ℂ → ℂ → ℝ)
    (c : ℕ → (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) → ℝ)
    (hSeq : ∀ (n : ℕ) (z : ℂ) (ℓ : {φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ),
      c n (z, ℓ) = FirstPassS11ah.localCert (ball c₂ r₂) κ m Ostar U V W T Q' Q η M n ℓ z)
    (μR : ℂ → Ω → Measure ℂ) (dR : ℂ → Ω → ℂ → ℂ → ℝ)
    (Dμ : ModConstTestPairings (Set.univ : Set ℂ) → Measure ℂ)
    (Dd : ModConstTestPairings (Set.univ : Set ℂ) → ℂ → ℂ → ℝ)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (hFit : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ᵐ ω ∂P, ∀ (z' : ℂ) (n : ℕ),
      closedBall z' (FirstPassS11ah.cutRadius n) ⊆ ball c₂ r₂ →
        (FirstPassS11i.CertificateEvent (κ (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2)
            (m (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z).2) Ostar U V W T Q' Q η M
            (FirstPassS11ah.certScale n) z' ↔
          FirstPassS11i.CertificateEvent (μR z ω) (dR z ω) Ostar U V W T Q' Q η M
            (FirstPassS11ah.certScale n) z'))
    (hCov : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ, closedBall z (FirstPassS11ah.cutRadius n) ⊆ ball c₂ r₂ →
        (FirstPassS11i.CertificateEvent (μR z ω) (dR z ω) Ostar U V W T Q' Q η M
            (FirstPassS11ah.certScale n) z ↔
          FirstPassS11i.CertificateEvent
            (Dμ (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            (Dd (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            Ostar U V W T Q' Q η M 1 0))
    (hG : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ),
      AdmissibleRootShift α₀ z b u → ∀ᵐ ω ∂P, ∀ n : ℕ,
        (FirstPassS11i.CertificateEvent
            (Dμ (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            (Dd (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
            Ostar U V W T Q' Q η M 1 0 ↔
          ballRestrictPairing 7 (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))) ∈ F))
    {S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ))}
    (hS : MeasurableSet S)
    (hSfail : ∀ x, x ∈ S ↔ x.1 ∈ A ∧ ¬ Tendsto (fun N : ℕ => ReferenceNullS11i.refWindowAverage c N x) atTop
      (𝓝 (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal)) :
    ∀ᵐ ω ∂P, ∫⁻ z in ball c₁ r₁,
      S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 :=
  ae_quantum_bad_mass_eq_zero_of_termwise hCM hB hCamp hγ0 hγ2 hα hh hμ hE hr₁ hr₂ hsub h0 A c hF
    (ae_termwise_of_identification hsub A Ostar U V W T Q' Q η M κ m c hSeq μR dR Dμ Dd hFit hCov hG)
    hS hSfail

end FirstPassS11ai
