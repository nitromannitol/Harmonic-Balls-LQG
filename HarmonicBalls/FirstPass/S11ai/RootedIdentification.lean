import HarmonicBalls.FirstPass.S11ai
import HarmonicBalls.FirstPass.S11ai.ShiftCutoff

/-!
# Rooted decoder identification `hId` from the termwise certificate identity (fp-S11ai, operator note 03:55 UTC)

Source: `notes/fp-gaps/CHATGPT-n1-n2-11-13-inputs.md` section 1. The `hId` of `ae_window_limit_at_root` is false for
arbitrary `c` and `F` (§1.1), so the certificate identification is made explicit (§1.2) and `hId` is derived (§1.3).

What is proved here (Lean-sized steps of §1.3):
* Step 2 (`FirstPassS11ai.exists_shift_cutoff`, ShiftCutoff.lean): the smooth shift `u_z`.
* Step 1 (choice of `b` with `2 b < ‖z‖`, `2 b < 1`) and Step 8 (root quantifier, a.e. `z ≠ 0`).
* Step 7 (deterministic): termwise equality for `n ≥ n₀` gives the exact eventual window equality `∀ᶠ N`.
* hence `hId` (`ae_rootedId_of_termwise`) and the entry point `ae_quantum_bad_mass_eq_zero_of_termwise`, which replaces `hId`
  by the termwise hypothesis `hT`.

What is NOT proved here (named hypothesis `hT`, §1.3 Steps 3-6): the termwise identity
`c n (campbellReferenceObs … z) = 1_{ballRestrictPairing 7 ⁻¹' F}(dilOp^[n] (canonFieldOf γ (G ω)))` for all large `n`,
almost surely, where `G ω = addFunPairing (translatedPairing hC hcirc z ω) u`. It is the consequence of the §1.2
certificate identification (1)-(4): `c` is the sequence (J) of the one certificate, `F` its scale-one version, plus the
rooted whole-object decoder identities (§1.3 Step 4) and the certificate covariance under translation and dyadic scaling.
`hT` quantifies over all admissible `(b, u)`; `n₀` may depend on `b`, and only `u` on `ball 0 b` matters.
-/

universe u

namespace FirstPassS11ai

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal
open HarmonicBalls
open HarmonicBalls.S11c

/-- Step 7 of §1.3 (deterministic): termwise equality of the certificate indicators with the dilated scale-one
indicators, for all indices `n ≥ n₀`, gives the exact eventual equality of the reference window average and the
window frequency. Both averages use the same index set `[N+1, 2N]` and the same normalisation `1/N`. -/
theorem eventually_refWindowAverage_eq_windowFreqOf {X : Type*} (γ : ℝ) (c : ℕ → X → ℝ) (x : X)
    (E : Set (ModConstTestPairings (Set.univ : Set ℂ))) (T : (ℂ → ℝ) → ℝ) (n₀ : ℕ)
    (h : ∀ n ≥ n₀, c n x = E.indicator (fun _ => (1 : ℝ)) (dilOp^[n] (canonFieldOf γ T))) :
    ∀ᶠ N : ℕ in atTop, ReferenceNullS11i.refWindowAverage c N x = windowFreqOf γ E T N := by
  filter_upwards [eventually_ge_atTop n₀] with N hN
  unfold ReferenceNullS11i.refWindowAverage windowFreqOf
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_Icc] at hn
  exact h n (by omega)

/-- Step 8 of §1.3 (root quantifier): for almost every root `z`, the origin is excluded. -/
theorem ae_ne_zero_on_ball (c₁ : ℂ) (r₁ : ℝ) : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ≠ 0 := by
  rw [ae_iff]
  have hset : {a : ℂ | ¬ a ≠ 0} = {0} := by ext a; simp
  rw [hset]
  have h0 : (volume : Measure ℂ) {0} = 0 := measure_singleton (0 : ℂ)
  rw [Measure.restrict_apply (measurableSet_singleton (0 : ℂ))]
  exact measure_mono_null Set.inter_subset_left h0

/-- The rooted decoder identification `hId` of `ae_window_limit_at_root`, derived (§1.3 Steps 1, 2, 7, 8) from the termwise
certificate identity `hT` (§1.3 Steps 3-6, named). For each root `z ∈ A` (a.e. `z ≠ 0`) take `b = min (‖z‖/4) (1/4)`
and the shift `u` of `exists_shift_cutoff`; then `hT` at `(b, u)` gives the a.s. termwise identity and Step 7 gives the
exact eventual window equality. -/
theorem ae_rootedId_of_termwise {γ α₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (A : Set ℂ)
    (c : ℕ → (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) → ℝ)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))}
    (hT : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), 0 < b → 2 * b < ‖z‖ → 2 * b < 1 →
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u → Real.circleAverage u 0 1 = 0 →
      (∀ w ∈ ball (0 : ℂ) b, u w = -α₀ * Real.log ‖z + w‖) →
      ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀,
        c n (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) =
          (ballRestrictPairing 7 ⁻¹' F).indicator (fun _ => (1 : ℝ))
            (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u)))) :
    ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∃ (b : ℝ) (u : ℂ → ℝ), 0 < b ∧
      ContDiff ℝ (⊤ : ℕ∞) u ∧ HasCompactSupport u ∧ Real.circleAverage u 0 1 = 0 ∧ ∀ᵐ ω ∂P, ∀ᶠ N in atTop,
        ReferenceNullS11i.refWindowAverage c N (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z)
          = windowFreqOf γ (ballRestrictPairing 7 ⁻¹' F) (addFunPairing (translatedPairing hC hcirc z ω) u) N := by
  filter_upwards [hT, ae_ne_zero_on_ball c₁ r₁] with z hTz hz0 hzA
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hb : 0 < min (‖z‖ / 4) (1 / 4) := lt_min (by positivity) (by norm_num)
  have hbz : 2 * min (‖z‖ / 4) (1 / 4) < ‖z‖ := by
    have := min_le_left (‖z‖ / 4) (1 / 4)
    linarith
  have hb1 : 2 * min (‖z‖ / 4) (1 / 4) < 1 := by
    have := min_le_right (‖z‖ / 4) (1 / 4)
    linarith
  obtain ⟨u, hu, hcomp, hu0, hu_eq⟩ := exists_shift_cutoff z α₀ hb hbz hb1
  refine ⟨min (‖z‖ / 4) (1 / 4), u, hb, hu, hcomp, hu0, ?_⟩
  filter_upwards [hTz hzA _ u hb hbz hb1 hu hcomp hu0 hu_eq] with ω hω
  obtain ⟨n₀, hn₀⟩ := hω
  exact eventually_refWindowAverage_eq_windowFreqOf γ _ _ _ _ n₀ hn₀

/-- Steps 6 and 7 of §1.3 with `hId` replaced by the termwise certificate identity `hT`. This is the entry point of
`ae_quantum_bad_mass_eq_zero_of_rooted_identification` with `hId` discharged by `ae_rootedId_of_termwise`. -/
theorem ae_quantum_bad_mass_eq_zero_of_termwise
    (hCM : CameronMartinGFFMutualAbsCont.{u}) (hB : BirkhoffPointwiseErgodic.{0})
    (hCamp : HarmonicBalls.LocalCampbellMarkedRestrictionFrozen.{u})
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hE : ∀ n : ℕ, LQGMeasureExistence P γ (lqgQ γ - 1 / ((n : ℝ) + 1)) hC hcirc)
    {c₁ c₂ : ℂ} {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hsub : closedBall c₁ r₁ ⊆ ball c₂ r₂)
    (h0 : (0 : ℂ) ∉ closedBall c₂ r₂) (A : Set ℂ)
    (c : ℕ → (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ)) → ℝ)
    {F : Set (ModConstTestPairings (ball (0 : ℂ) 7))} (hF : MeasurableSet F)
    (hT : ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), z ∈ A → ∀ (b : ℝ) (u : ℂ → ℝ), 0 < b → 2 * b < ‖z‖ → 2 * b < 1 →
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u → Real.circleAverage u 0 1 = 0 →
      (∀ w ∈ ball (0 : ℂ) b, u w = -α₀ * Real.log ‖z + w‖) →
      ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n ≥ n₀,
        c n (campbellReferenceObs γ α₀ (ball c₂ r₂) (hC ω) z) =
          (ballRestrictPairing 7 ⁻¹' F).indicator (fun _ => (1 : ℝ))
            (dilOp^[n] (canonFieldOf γ (addFunPairing (translatedPairing hC hcirc z ω) u))))
    {S : Set (ℂ × ({φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ))}
    (hS : MeasurableSet S)
    (hSfail : ∀ x, x ∈ S ↔ x.1 ∈ A ∧ ¬ Tendsto (fun N : ℕ => ReferenceNullS11i.refWindowAverage c N x) atTop
      (𝓝 (P {ω | alphaCanon γ hC ω ∈ ballRestrictPairing 7 ⁻¹' F}).toReal)) :
    ∀ᵐ ω ∂P, ∫⁻ z in ball c₁ r₁,
      S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ (ball c₂ r₂) (hC ω) z) ∂(μ ω) = 0 :=
  ae_quantum_bad_mass_eq_zero_of_rooted_identification hCM hB hCamp hγ0 hγ2 hα hh hμ hE hr₁ hr₂ hsub h0 A c hF
    (ae_rootedId_of_termwise A c hT) hS hSfail

end FirstPassS11ai
