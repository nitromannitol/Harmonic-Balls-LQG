import HarmonicBalls.FirstPass.Frozen.S11c
import HarmonicBalls.FirstPass.S11c.BadSetMeasurable11_7
import HarmonicBalls.Proofs.Potential.Fundamental

/-!
# Lemma 11.7, the Campbell reference observation is the insertion-zero rooted observation shifted by `b`

For a root `z` and a disk `D`, the reference observation `campbellReferenceObs γ α₀ D hC z` (Frozen/S11c.lean) equals the
insertion-zero rooted observation `rootedMeanZeroObs 0 γ D z hC` plus the pairing with the shift
`b(w) = -α₀ log|w| + γ log max(1,|w|)` (`campbellShift`). This is a deterministic identity, read off from the definitions
(the pairing of `h` with `φ` is `hC φ - α₀ ∫ φ log|·|`). Its cut-off form (`χ = 1` on `D`) writes the shift as a
pairing with a function `b χ` that is compactly supported on the plane. The glue
`lintegral_localBadSet_campbellRef_eq_zero` turns an absolute continuity statement between the laws of the two observations
 (a hypothesis here) and the fixed-root null section into the vanishing of
the reference bad-set integral of `Assembly11_7.lean` clause 3.
-/

open MeasureTheory Filter Set
open scoped ENNReal

namespace HarmonicBalls.S11c

/-- The shift `b(w) = -α₀ log|w| + γ log max(1,|w|)` of `campbellReferenceObs` (Frozen/S11c.lean). -/
noncomputable def campbellShift (γ α₀ : ℝ) (w : ℂ) : ℝ :=
  -α₀ * Real.log ‖w‖ + γ * Real.log (max 1 ‖w‖)

/-- For a test function `φ`, the function `w ↦ φ(w) log|w - z|` is integrable (the logarithm is locally integrable). -/
theorem integrable_mul_logNorm_sub {D : Set ℂ} {φ : ℂ → ℝ} (hφ : IsTestFunction D φ) (z : ℂ) :
    Integrable (fun w => φ w * Real.log ‖w - z‖) := by
  obtain ⟨hsm, hcs, -⟩ := hφ
  have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm z
    ).integrable_smul_right_of_hasCompactSupport hsm.continuous hcs
  simpa only [smul_eq_mul, mul_comm] using h

/-- For a test function `φ`, the function `w ↦ φ(w) log max(1,|w|)` is integrable (it is continuous with compact support). -/
theorem integrable_mul_log_max {D : Set ℂ} {φ : ℂ → ℝ} (hφ : IsTestFunction D φ) :
    Integrable (fun w => φ w * Real.log (max 1 ‖w‖)) := by
  obtain ⟨hsm, hcs, -⟩ := hφ
  have hc : Continuous fun w : ℂ => Real.log (max 1 ‖w‖) :=
    (continuous_const.max continuous_norm).log fun w => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  exact (hsm.continuous.mul hc).integrable_of_hasCompactSupport hcs.mul_right

/-- Deterministic identity: the reference observation at `z` is the insertion-zero rooted observation at `z`
shifted by `campbellShift`. Pairings: `fieldPairing α₀ hC φ - γ ∫ (log|w - z| - log max(1,|w|)) φ = fieldPairing 0 hC φ
- γ ∫ log|w - z| φ + ∫ b φ`. -/
theorem campbellReferenceObs_snd_apply (γ α₀ : ℝ) {D : Set ℂ} (hC : (ℂ → ℝ) → ℝ) (z : ℂ)
    (φ : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0}) :
    (campbellReferenceObs γ α₀ D hC z).2 φ =
      (rootedMeanZeroObs 0 γ D z hC) φ + ∫ w, campbellShift γ α₀ w * φ.1 w := by
  have hφ : IsTestFunction D φ.1 := φ.2.1
  have i0 : Integrable (fun w => φ.1 w * Real.log ‖w‖) := by
    simpa only [sub_zero] using integrable_mul_logNorm_sub hφ 0
  have iz : Integrable (fun w => φ.1 w * Real.log ‖w - z‖) := integrable_mul_logNorm_sub hφ z
  have ib : Integrable (fun w => φ.1 w * Real.log (max 1 ‖w‖)) := integrable_mul_log_max hφ
  have hA : ∫ w, campbellShift γ α₀ w * φ.1 w
      = -α₀ * (∫ w, φ.1 w * Real.log ‖w‖) + γ * (∫ w, φ.1 w * Real.log (max 1 ‖w‖)) := by
    have hpt : ∀ w, campbellShift γ α₀ w * φ.1 w
        = -α₀ * (φ.1 w * Real.log ‖w‖) + γ * (φ.1 w * Real.log (max 1 ‖w‖)) := fun w => by
      unfold campbellShift
      ring
    simp only [hpt]
    rw [integral_add (i0.const_mul (-α₀)) (ib.const_mul γ), integral_const_mul, integral_const_mul]
  have hB : ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ.1 w
      = (∫ w, φ.1 w * Real.log ‖w - z‖) - ∫ w, φ.1 w * Real.log (max 1 ‖w‖) := by
    rw [← integral_sub iz ib]
    congr 1
    funext w
    ring
  have hR : ∫ w, Real.log ‖w - z‖ * φ.1 w = ∫ w, φ.1 w * Real.log ‖w - z‖ := by
    congr 1
    funext w
    ring
  simp only [campbellReferenceObs, rootedMeanZeroObs, fieldPairing, hA, hB, hR]
  ring

/-- Cut-off form: if `χ = 1` on `D`, the shift may be taken to be the compactly supported function
`campbellShift · χ`, so the reference observation is the rooted observation shifted by the pairing with `b χ`. -/
theorem campbellReferenceObs_snd_apply_of_cut (γ α₀ : ℝ) {D : Set ℂ} (hC : (ℂ → ℝ) → ℝ) (z : ℂ)
    (χ : ℂ → ℝ) (hχ : ∀ w ∈ D, χ w = 1)
    (φ : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0}) :
    (campbellReferenceObs γ α₀ D hC z).2 φ =
      (rootedMeanZeroObs 0 γ D z hC) φ + ∫ w, campbellShift γ α₀ w * χ w * φ.1 w := by
  rw [campbellReferenceObs_snd_apply]
  have hD : tsupport φ.1 ⊆ D := by
    obtain ⟨-, -, h⟩ := φ.2.1
    exact h
  congr 1
  congr 1
  funext w
  by_cases hw : φ.1 w = 0
  · simp [hw]
  · have hsupp : w ∈ tsupport φ.1 := subset_tsupport _ (Function.mem_support.mpr hw)
    rw [hχ w (hD hsupp), mul_one]

/-- Glue. Let `B` be the local bad set at a fixed root `z`. Assume that almost surely
the insertion-zero rooted observation avoids the section `{x | (z, x) ∈ B}` (the output of `fixedRoot_null_of_origin`), and that the laws of the reference observation and of the rooted observation are absolutely continuous in the
sense: a measurable set of observations that is null for the rooted law is null for the reference law (a hypothesis here). Then the reference bad-set integral vanishes. -/
theorem lintegral_localBadSet_campbellRef_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {γ α₀ : ℝ}
    {D : Set ℂ} {z : ℂ}
    {K : ProbabilityTheory.Kernel ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ) ℂ}
    [ProbabilityTheory.IsSFiniteKernel K] {Q : Set ℂ} (hQ : MeasurableSet Q) {M a : ℝ} {U : Set ℂ}
    (hU : MeasurableSet U) {nD : ℕ}
    (h0 : ∀ᵐ ω ∂P, (z, rootedMeanZeroObs 0 γ D z (hC ω)) ∉ localBadSet K Q M a U nD)
    (hAC : ∀ S : Set ({φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ), MeasurableSet S →
      P {ω | rootedMeanZeroObs 0 γ D z (hC ω) ∈ S} = 0 →
        P {ω | (campbellReferenceObs γ α₀ D (hC ω) z).2 ∈ S} = 0) :
    ∫⁻ ω, (localBadSet K Q M a U nD).indicator (fun _ => (1 : ℝ≥0∞))
      (campbellReferenceObs γ α₀ D (hC ω) z) ∂P = 0 := by
  have hBm : MeasurableSet (localBadSet K Q M a U nD) := measurableSet_localBadSet K hQ M a hU nD
  have hSm : MeasurableSet {x | (z, x) ∈ localBadSet K Q M a U nD} :=
    hBm.preimage measurable_prodMk_left
  have h1 : P {ω | rootedMeanZeroObs 0 γ D z (hC ω) ∈ {x | (z, x) ∈ localBadSet K Q M a U nD}} = 0 :=
    measure_eq_zero_iff_ae_notMem.mpr h0
  have h2 := hAC _ hSm h1
  have h3 : ∀ᵐ ω ∂P, (campbellReferenceObs γ α₀ D (hC ω) z).2 ∉ {x | (z, x) ∈ localBadSet K Q M a U nD} :=
    measure_eq_zero_iff_ae_notMem.mp h2
  have h4 : (fun ω => (localBadSet K Q M a U nD).indicator (fun _ => (1 : ℝ≥0∞))
      (campbellReferenceObs γ α₀ D (hC ω) z)) =ᵐ[P] fun _ => 0 := by
    filter_upwards [h3] with ω hω
    have hω' : (z, (campbellReferenceObs γ α₀ D (hC ω) z).2) ∉ localBadSet K Q M a U nD := hω
    have hpair : campbellReferenceObs γ α₀ D (hC ω) z = (z, (campbellReferenceObs γ α₀ D (hC ω) z).2) := rfl
    rw [hpair, Set.indicator_of_notMem hω']
  rw [lintegral_congr_ae h4]
  simp

end HarmonicBalls.S11c
