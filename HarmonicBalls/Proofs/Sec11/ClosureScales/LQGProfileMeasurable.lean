import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGProfileMeasure
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-!
# Lemma l:r6-transfer, step 3d.3: measurability of the LQG measure of a canonical profile

Source: `notes/sec11-proof/sec11-proof-r7.tex`, Lemma `l:r6-transfer`, measure part (lines 560-600). The measure
`profileMeasure γ α₀ f` (`LQGProfileMeasure.lean`) is the Riesz measure of the limit functional. On an open set `U`, its
mass is the supremum of the integrals of cut-off tests `φ k` increasing to the indicator of `U` (monotone convergence),
and these integrals are the limit functional. The mass on open sets is measurable in the profile, so the Sec5 criterion
`measurable_measure_of_isOpen` (`Sec5/OpenMeasureLaw.lean`) gives the measurability of the Borel map
`f ↦ profileMeasure γ α₀ f`.
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

/-- The cut-off `χ_k` of the closed ball of radius `k + 1`, as a compactly supported continuous function. -/
theorem hasCompactSupport_cutoffBall_mul (k : ℕ) (g : ℂ → ℝ) :
    HasCompactSupport (fun z => g z * cutoffBall k z) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ((k : ℝ) + 1)) fun z hz => by
    have hz' : (k : ℝ) + 1 < ‖z‖ := by
      rw [mem_closedBall, dist_zero_right, not_le] at hz
      exact hz
    simp only [cutoffBall_eq_zero hz'.le, mul_zero]

/-- Monotonicity of the cut-off `χ_k` in the radius index. -/
theorem cutoffBall_mono {k k' : ℕ} (h : k ≤ k') (z : ℂ) : cutoffBall k z ≤ cutoffBall k' z := by
  unfold cutoffBall
  have hk : (k : ℝ) ≤ (k' : ℝ) := Nat.cast_le.mpr h
  exact max_le_max le_rfl (min_le_min_left _ (by linarith))

/-- The cut-off test `χ_k` as a compactly supported continuous function. -/
noncomputable def cutoffBallC (k : ℕ) : CompactlySupportedContinuousMap ℂ ℝ :=
  ⟨⟨cutoffBall k, continuous_cutoffBall k⟩, by
    simpa using hasCompactSupport_cutoffBall_mul k (fun _ => 1)⟩

/-- The cut-off test `z ↦ min 1 (k · dist(z, Uᶜ)) · χ_k(z)` of an open set. -/
noncomputable def cutoffTestC (U : Set ℂ) (k : ℕ) : CompactlySupportedContinuousMap ℂ ℝ :=
  ⟨⟨fun z => min 1 ((k : ℝ) * infDist z Uᶜ) * cutoffBall k z,
    (continuous_const.min (continuous_const.mul (continuous_infDist_pt Uᶜ))).mul (continuous_cutoffBall k)⟩,
    hasCompactSupport_cutoffBall_mul k (fun z => min 1 ((k : ℝ) * infDist z Uᶜ))⟩

/-- **Cut-off tests increasing to the indicator of an open set.** -/
theorem exists_cutoff_seq_open {U : Set ℂ} (hU : IsOpen U) :
    ∃ φ : ℕ → CompactlySupportedContinuousMap ℂ ℝ,
      (∀ k z, 0 ≤ φ k z ∧ φ k z ≤ U.indicator 1 z) ∧
      (∀ z, Monotone (fun k => φ k z)) ∧
      (∀ z, Tendsto (fun k => φ k z) atTop (𝓝 (U.indicator 1 z))) := by
  by_cases hUc : Uᶜ.Nonempty
  · have hcl : IsClosed Uᶜ := hU.isClosed_compl
    refine ⟨fun k => cutoffTestC U k, ?_, ?_, ?_⟩
    · intro k z
      show 0 ≤ min 1 ((k : ℝ) * infDist z Uᶜ) * cutoffBall k z ∧
        min 1 ((k : ℝ) * infDist z Uᶜ) * cutoffBall k z ≤ U.indicator 1 z
      by_cases hz : z ∈ U
      · rw [indicator_of_mem hz, Pi.one_apply]
        have hd : 0 ≤ infDist z Uᶜ := infDist_nonneg
        refine ⟨mul_nonneg (le_min zero_le_one (mul_nonneg (Nat.cast_nonneg k) hd)) (cutoffBall_nonneg k z), ?_⟩
        calc min 1 ((k : ℝ) * infDist z Uᶜ) * cutoffBall k z ≤ 1 * 1 :=
              mul_le_mul (min_le_left _ _) (cutoffBall_le_one k z) (cutoffBall_nonneg k z) zero_le_one
          _ = 1 := one_mul 1
      · rw [indicator_of_notMem hz, infDist_zero_of_mem (mem_compl hz), mul_zero, min_eq_right zero_le_one,
          zero_mul]
        exact ⟨le_rfl, le_rfl⟩
    · intro z k k' hkk'
      show min 1 ((k : ℝ) * infDist z Uᶜ) * cutoffBall k z ≤
        min 1 ((k' : ℝ) * infDist z Uᶜ) * cutoffBall k' z
      have hd : 0 ≤ infDist z Uᶜ := infDist_nonneg
      have hk : (k : ℝ) * infDist z Uᶜ ≤ (k' : ℝ) * infDist z Uᶜ :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hkk') hd
      exact mul_le_mul (min_le_min_left _ hk) (cutoffBall_mono hkk' z) (cutoffBall_nonneg k z)
        (le_min zero_le_one (mul_nonneg (Nat.cast_nonneg _) hd))
    · intro z
      by_cases hz : z ∈ U
      · rw [indicator_of_mem hz, Pi.one_apply]
        have hd : 0 < infDist z Uᶜ := (hcl.notMem_iff_infDist_pos hUc).mp (fun h => h hz)
        obtain ⟨N, hN⟩ := exists_nat_ge (max ‖z‖ (1 / infDist z Uᶜ))
        refine tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨N, fun k hk => ?_⟩)
        have hNk : (N : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
        have hk1 : ‖z‖ ≤ (k : ℝ) := le_trans (le_trans (le_max_left _ _) hN) hNk
        have hk2 : 1 / infDist z Uᶜ ≤ (k : ℝ) :=
          le_trans (le_trans (le_max_right _ _) hN) hNk
        have hk3 : 1 ≤ (k : ℝ) * infDist z Uᶜ := (div_le_iff₀ hd).mp hk2
        show (1 : ℝ) = min 1 ((k : ℝ) * infDist z Uᶜ) * cutoffBall k z
        rw [cutoffBall_eq_one hk1, mul_one, min_eq_left hk3]
      · rw [indicator_of_notMem hz]
        refine tendsto_const_nhds.congr' (Filter.Eventually.of_forall fun k => ?_)
        show (0 : ℝ) = min 1 ((k : ℝ) * infDist z Uᶜ) * cutoffBall k z
        rw [infDist_zero_of_mem (mem_compl hz), mul_zero, min_eq_right zero_le_one, zero_mul]
  · have hU' : U = univ := Set.eq_univ_of_forall fun z => by
      by_contra hz
      exact hUc ⟨z, hz⟩
    subst hU'
    refine ⟨fun k => cutoffBallC k, ?_, ?_, ?_⟩
    · intro k z
      show 0 ≤ cutoffBall k z ∧ cutoffBall k z ≤ univ.indicator 1 z
      rw [indicator_univ, Pi.one_apply]
      exact ⟨cutoffBall_nonneg k z, cutoffBall_le_one k z⟩
    · intro z k k' hkk'
      exact cutoffBall_mono hkk' z
    · intro z
      rw [indicator_univ, Pi.one_apply]
      refine tendsto_const_nhds.congr' (Filter.eventually_atTop.mpr ⟨⌈‖z‖⌉₊, fun k hk => ?_⟩)
      have hk1 : ‖z‖ ≤ (k : ℝ) := le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hk)
      show (1 : ℝ) = cutoffBall k z
      rw [cutoffBall_eq_one hk1]

/-- The mass of an open set under the LQG measure is the supremum of the integrals of the cut-off tests. -/
theorem profileMeasure_apply_open_eq (γ α₀ : ℝ) (f : CanonicalProfile) {U : Set ℂ} (hU : IsOpen U)
    (φ : ℕ → CompactlySupportedContinuousMap ℂ ℝ) (hbd : ∀ k z, 0 ≤ φ k z ∧ φ k z ≤ U.indicator 1 z)
    (hmono : ∀ z, Monotone (fun k => φ k z))
    (htend : ∀ z, Tendsto (fun k => φ k z) atTop (𝓝 (U.indicator 1 z))) :
    profileMeasure γ α₀ f U = ⨆ k : ℕ, ENNReal.ofReal (profileLimit γ α₀ f (φ k)) := by
  have hmeas : ∀ k : ℕ, Measurable fun z => ENNReal.ofReal (φ k z) := fun k =>
    ENNReal.measurable_ofReal.comp (φ k).continuous.measurable
  have hmono' : Monotone fun (k : ℕ) (z : ℂ) => ENNReal.ofReal (φ k z) := fun k k' hkk' z =>
    ENNReal.ofReal_le_ofReal (hmono z hkk')
  have hsup : ∀ z, ⨆ k : ℕ, ENNReal.ofReal (φ k z) = U.indicator 1 z := by
    intro z
    have hmonoz : Monotone fun k : ℕ => ENNReal.ofReal (φ k z) := fun k k' h =>
      ENNReal.ofReal_le_ofReal (hmono z h)
    have ht : Tendsto (fun k : ℕ => ENNReal.ofReal (φ k z)) atTop
        (𝓝 (ENNReal.ofReal (U.indicator 1 z))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp (htend z)
    rw [tendsto_nhds_unique (tendsto_atTop_iSup hmonoz) ht]
    by_cases hz : z ∈ U <;> simp [hz]
  calc profileMeasure γ α₀ f U = ∫⁻ z, U.indicator 1 z ∂(profileMeasure γ α₀ f) :=
        (lintegral_indicator_one hU.measurableSet).symm
    _ = ∫⁻ z, ⨆ k : ℕ, ENNReal.ofReal (φ k z) ∂(profileMeasure γ α₀ f) :=
        lintegral_congr fun z => (hsup z).symm
    _ = ⨆ k : ℕ, ∫⁻ z, ENNReal.ofReal (φ k z) ∂(profileMeasure γ α₀ f) :=
        lintegral_iSup hmeas hmono'
    _ = ⨆ k : ℕ, ENNReal.ofReal (profileLimit γ α₀ f (φ k)) := by
        refine iSup_congr fun k => ?_
        have hint : Integrable (φ k) (profileMeasure γ α₀ f) :=
          (φ k).continuous.integrable_of_hasCompactSupport (φ k).hasCompactSupport
        rw [← integral_profileMeasure γ α₀ f (φ k),
          ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => (hbd k z).1)]

/-- The mass of an open set under the LQG measure is measurable in the canonical profile. -/
theorem measurable_profileMeasure_apply_open (γ α₀ : ℝ) {U : Set ℂ} (hU : IsOpen U) :
    Measurable fun f : CanonicalProfile => profileMeasure γ α₀ f U := by
  obtain ⟨φ, hbd, hmono, htend⟩ := exists_cutoff_seq_open hU
  have h : (fun f : CanonicalProfile => profileMeasure γ α₀ f U) =
      fun f => ⨆ k : ℕ, ENNReal.ofReal (profileLimit γ α₀ f (φ k)) :=
    funext fun f => profileMeasure_apply_open_eq γ α₀ f hU φ hbd hmono htend
  rw [h]
  exact Measurable.iSup fun k => ENNReal.measurable_ofReal.comp (measurable_profileLimit γ α₀ (φ k))

/-- **The LQG measure is a measurable function of the canonical profile** (Lemma l:r6-transfer, measure part): the
Borel map `m_{γ,α₀}` of the canonical profile is `f ↦ profileMeasure γ α₀ f`. -/
theorem measurable_profileMeasure (γ α₀ : ℝ) : Measurable (profileMeasure γ α₀) :=
  measurable_measure_of_isOpen (fun f => isLocallyFiniteMeasure_profileMeasure γ α₀ f)
    fun _ hU => measurable_profileMeasure_apply_open γ α₀ hU

end HarmonicBalls
