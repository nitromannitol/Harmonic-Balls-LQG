import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGGoodProfiles

/-!
# The limit functional and the Riesz measure of a canonical profile

The LQG measure is
the vague limit of the approximations `profileApprox γ α₀ n f` along the dyadic scales. On the good set
`goodProfiles γ α₀` (`LQGGoodProfiles.lean`), the integrals of every compactly supported continuous test converge; their
limit defines a positive linear functional on `C_c(ℂ, ℝ)` (`profileFunctional`), and the Riesz–Markov–Kakutani measure of
this functional is the LQG measure `profileMeasure γ α₀ f` (Mathlib, `RealRMK.rieszMeasure`). Off the good set the
functional is zero, so every canonical profile has a Radon measure, and measurability is handled in step 3d.3.

The LQG density is the one of `IsLQGLimit` (Defs/LQG.lean): the vague limit of `ε^{γ²/2} e^{γ h_ε(z)} dz` (Duplantier-Sheffield
2011, Prop. 1.1).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Classical

/-- The limit of the integrals of the compactly supported continuous test `ψ` against the LQG approximations of the
canonical profile `f`, on the good set; zero off the good set. -/
noncomputable def profileLimit (γ α₀ : ℝ) (f : CanonicalProfile)
    (ψ : CompactlySupportedContinuousMap ℂ ℝ) : ℝ :=
  if f ∈ goodProfiles γ α₀ then
    limUnder atTop (fun n : ℕ => ∫ z, ψ z ∂(profileApprox γ α₀ n f)) else 0

/-- On the good set, the limit functional is the limit of the integrals of the approximations. -/
theorem profileLimit_eq_of_tendsto {γ α₀ : ℝ} {f : CanonicalProfile} (hf : f ∈ goodProfiles γ α₀)
    {ψ : CompactlySupportedContinuousMap ℂ ℝ} {L : ℝ}
    (hL : Tendsto (fun n : ℕ => ∫ z, ψ z ∂(profileApprox γ α₀ n f)) atTop (𝓝 L)) :
    profileLimit γ α₀ f ψ = L := by
  simp only [profileLimit, hf, ↓reduceIte]
  exact hL.limUnder_eq

/-- On the good set, the approximations converge against every compactly supported continuous test. -/
theorem exists_profileLimit_tendsto {γ α₀ : ℝ} {f : CanonicalProfile} (hf : f ∈ goodProfiles γ α₀)
    (ψ : CompactlySupportedContinuousMap ℂ ℝ) :
    Tendsto (fun n : ℕ => ∫ z, ψ z ∂(profileApprox γ α₀ n f)) atTop (𝓝 (profileLimit γ α₀ f ψ)) := by
  obtain ⟨L, hL⟩ := exists_tendsto_profile_integral_of_good hf ψ.continuous ψ.hasCompactSupport
  rw [profileLimit_eq_of_tendsto hf hL]
  exact hL

/-- The limit functional of the canonical profile `f`: a positive linear map on `C_c(ℂ, ℝ)`. -/
noncomputable def profileFunctional (γ α₀ : ℝ) (f : CanonicalProfile) :
    CompactlySupportedContinuousMap ℂ ℝ →ₚ[ℝ] ℝ where
  toFun := profileLimit γ α₀ f
  map_add' ψ₁ ψ₂ := by
    show profileLimit γ α₀ f (ψ₁ + ψ₂) = profileLimit γ α₀ f ψ₁ + profileLimit γ α₀ f ψ₂
    by_cases hf : f ∈ goodProfiles γ α₀
    · have hint : ∀ n : ℕ, ∫ z, (ψ₁ + ψ₂) z ∂(profileApprox γ α₀ n f) =
          (∫ z, ψ₁ z ∂(profileApprox γ α₀ n f)) + ∫ z, ψ₂ z ∂(profileApprox γ α₀ n f) := by
        intro n
        have := isLocallyFiniteMeasure_profileApprox γ α₀ n f
        simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
        exact integral_add (ψ₁.continuous.integrable_of_hasCompactSupport ψ₁.hasCompactSupport)
          (ψ₂.continuous.integrable_of_hasCompactSupport ψ₂.hasCompactSupport)
      have h₁ := exists_profileLimit_tendsto hf ψ₁
      have h₂ := exists_profileLimit_tendsto hf ψ₂
      have hsum : Tendsto (fun n : ℕ => ∫ z, (ψ₁ + ψ₂) z ∂(profileApprox γ α₀ n f)) atTop
          (𝓝 (profileLimit γ α₀ f ψ₁ + profileLimit γ α₀ f ψ₂)) := by
        simp only [hint]
        exact h₁.add h₂
      exact profileLimit_eq_of_tendsto hf hsum
    · simp only [profileLimit, hf, ↓reduceIte, add_zero]
  map_smul' c ψ := by
    show profileLimit γ α₀ f (c • ψ) = c • profileLimit γ α₀ f ψ
    by_cases hf : f ∈ goodProfiles γ α₀
    · have hint : ∀ n : ℕ, ∫ z, (c • ψ) z ∂(profileApprox γ α₀ n f) =
          c • ∫ z, ψ z ∂(profileApprox γ α₀ n f) := by
        intro n
        simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply]
        exact integral_smul c _
      have hsmul : Tendsto (fun n : ℕ => ∫ z, (c • ψ) z ∂(profileApprox γ α₀ n f)) atTop
          (𝓝 (c • profileLimit γ α₀ f ψ)) := by
        simp only [hint]
        exact (exists_profileLimit_tendsto hf ψ).const_smul c
      exact profileLimit_eq_of_tendsto hf hsmul
    · simp only [profileLimit, hf, ↓reduceIte, smul_zero]
  monotone' ψ₁ ψ₂ h := by
    show profileLimit γ α₀ f ψ₁ ≤ profileLimit γ α₀ f ψ₂
    by_cases hf : f ∈ goodProfiles γ α₀
    · have hmono : ∀ n : ℕ, ∫ z, ψ₁ z ∂(profileApprox γ α₀ n f) ≤ ∫ z, ψ₂ z ∂(profileApprox γ α₀ n f) := by
        intro n
        have := isLocallyFiniteMeasure_profileApprox γ α₀ n f
        exact integral_mono
          (ψ₁.continuous.integrable_of_hasCompactSupport ψ₁.hasCompactSupport)
          (ψ₂.continuous.integrable_of_hasCompactSupport ψ₂.hasCompactSupport)
          (fun z => CompactlySupportedContinuousMap.le_def.mp h z)
      exact le_of_tendsto_of_tendsto' (exists_profileLimit_tendsto hf ψ₁) (exists_profileLimit_tendsto hf ψ₂) hmono
    · simp only [profileLimit, hf, ↓reduceIte, le_refl]

/-- The LQG measure of the canonical profile `f`: the Riesz–Markov–Kakutani measure of the limit functional
`profileFunctional γ α₀ f`. -/
noncomputable def profileMeasure (γ α₀ : ℝ) (f : CanonicalProfile) : Measure ℂ :=
  RealRMK.rieszMeasure (profileFunctional γ α₀ f)

/-- The LQG measure is locally finite (it is regular, hence finite on compact sets). -/
instance isLocallyFiniteMeasure_profileMeasure (γ α₀ : ℝ) (f : CanonicalProfile) :
    IsLocallyFiniteMeasure (profileMeasure γ α₀ f) := by
  unfold profileMeasure
  infer_instance

/-- The integral of a compactly supported continuous test against the LQG measure is the limit functional. -/
theorem integral_profileMeasure (γ α₀ : ℝ) (f : CanonicalProfile)
    (ψ : CompactlySupportedContinuousMap ℂ ℝ) :
    ∫ z, ψ z ∂(profileMeasure γ α₀ f) = profileLimit γ α₀ f ψ :=
  RealRMK.integral_rieszMeasure (profileFunctional γ α₀ f) ψ

/-- **Measurability of the limit functional in the profile.** Each value `profileLimit γ α₀ · ψ` is a measurable function
of the canonical profile, as the pointwise limit of measurable functions (the good set is measurable). -/
theorem measurable_profileLimit (γ α₀ : ℝ) (ψ : CompactlySupportedContinuousMap ℂ ℝ) :
    Measurable fun f : CanonicalProfile => profileLimit γ α₀ f ψ := by
  have hm : ∀ n : ℕ, Measurable fun f : CanonicalProfile =>
      (if f ∈ goodProfiles γ α₀ then ∫ z, ψ z ∂(profileApprox γ α₀ n f) else 0) := fun n =>
    Measurable.ite (measurableSet_goodProfiles γ α₀)
      (measurable_integral_profileApprox γ α₀ n ψ.continuous ψ.hasCompactSupport) measurable_const
  refine measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.mpr fun f => ?_)
  by_cases hf : f ∈ goodProfiles γ α₀
  · simp only [hf, ↓reduceIte]
    exact exists_profileLimit_tendsto hf ψ
  · simp only [profileLimit, hf, ↓reduceIte]
    exact tendsto_const_nhds

end HarmonicBalls
