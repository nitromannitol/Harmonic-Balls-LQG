import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleDecoderGFFIdentification
import HarmonicBalls.Proofs.Sec11.ClosureScales.CircleShiftContinuity
import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGProfileApprox
import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGGoodProfiles
import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGProfileMeasure
import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGProfileMeasurable
import HarmonicBalls.Proofs.Sec11.ClosureScales.LQGProfileMeasureAE

/-! # Coded LQG measure of an actual continuous circle profile

The coded Palm identity (eq:r6-palm, r8 line 1815) is stated on the actual carrier `C(CircleDomain, ℝ)`: the continuous
functions on the positive-radius domain `CircleDomain = {p : ℝ × ℂ // 0 < p.1}` (r10 lines 927-950 and 1257-1392; the
marked identity at r10 lines 2575-2778). This file supplies its measure-theoretic input.

* `circleProfileMeasure γ α₀ F` is the coded LQG measure of `F`, built by the dyadic formula of `profileMeasure`
  (LQGProfileMeasure.lean) on the actual carrier: `circleProfileApprox` applies `profileDecoder γ (2^{-k})` to
  `circleRadiusField`, `circleGoodProfiles` is the good set, `circleProfileLimit` the limit functional, and
  `circleProfileMeasure` the Riesz–Markov–Kakutani measure of the limit functional.
* Factorization through positive radii: `profileMeasure_eq_of_eq_on_circleIndexSet` shows that the canonical
  `profileMeasure` depends only on the values on `circleIndexSet`. Hence `circleProfileMeasure_eq` identifies the coded
  measure with `profileMeasure` at the zero-off-`CircleDomain` extension `circleAdapter F`. The adapter is a proof device
  only: it is not a public carrier, and no public statement reads a value off `CircleDomain`.
* `circleCodedProfile` is the actual profile of a whole-plane GFF: the named decoder of r10, identified with the circle
  field and DMS-compatible by `circleCompatDecoder_gff_identification` (CircleDecoderGFFIdentification.lean).
  `ae_lqgMeasure_eq_circleProfileMeasure` identifies the LQG measure with the coded measure of that profile a.s.
* `measurable_circle_palm_lintegral`: measurability in the profile of the inner Palm integral over `B_1`.
* The generic kernel lemmas `measurable_lintegral_kernel_of_pointwise_finite` and its indicator auxiliary are moved here
  unchanged from PalmLambdaMeasurable.lean, so that both the canonical and the actual-carrier consumers use them.

Credit (Leonardo Bonanno): `LQGProfileMeasurable` and `LQGProfileMeasureAE` import the LQG field modules
`LatticeProb.Bonanno.LQGMetric.Field.*` of the Lattice-Probability port pinned for Lean v4.35. This file reaches them only
through those imports.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology
open scoped ENNReal

namespace HarmonicBalls

/-! ### Generic kernel lemmas (moved unchanged from PalmLambdaMeasurable.lean) -/

/-- Auxiliary: measurability of `a ↦ ∫⁻ b, 1_t(a, b) c ∂κ a` for a kernel with pointwise finite values. -/
theorem measurable_lintegral_indicator_const_of_pointwise_finite {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (κ : Kernel α β) (hκ : ∀ a, IsFiniteMeasure (κ a)) {t : Set (α × β)}
    (ht : MeasurableSet t) (c : ℝ≥0∞) :
    Measurable fun a => ∫⁻ b, t.indicator (Function.const (α × β) c) (a, b) ∂κ a := by
  unfold Function.const
  simp_rw [lintegral_indicator_const_comp measurable_prodMk_left ht _]
  exact Measurable.const_mul (Kernel.measurable_kernel_prodMk_left_of_finite ht hκ) c

/-- Measurability of a parametric lower integral against a kernel whose values are finite measures (pointwise
finiteness suffices). The proof is that of Mathlib's `Measurable.lintegral_kernel_prod_right`
(`Probability/Kernel/MeasurableLIntegral.lean`), with the indicator case replaced by the pointwise-finite version. -/
theorem measurable_lintegral_kernel_of_pointwise_finite {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (κ : Kernel α β) (hκ : ∀ a, IsFiniteMeasure (κ a)) {f : α → β → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) : Measurable fun a => ∫⁻ b, f a b ∂κ a := by
  let F : ℕ → SimpleFunc (α × β) ℝ≥0∞ := SimpleFunc.eapprox (Function.uncurry f)
  have h : ∀ a, ⨆ n, F n a = Function.uncurry f a := SimpleFunc.iSup_eapprox_apply hf
  simp only [Prod.forall, Function.uncurry_apply_pair] at h
  simp_rw [← h]
  have : ∀ a, (∫⁻ b, ⨆ n, F n (a, b) ∂κ a) = ⨆ n, ∫⁻ b, F n (a, b) ∂κ a := by
    intro a
    rw [lintegral_iSup]
    · exact fun n => (F n).measurable.comp measurable_prodMk_left
    · exact fun i j hij b => SimpleFunc.monotone_eapprox (Function.uncurry f) hij _
  simp_rw [this]
  refine .iSup fun n => ?_
  refine SimpleFunc.induction
    (motive := fun f => Measurable (fun (a : α) => ∫⁻ (b : β), f (a, b) ∂κ a)) ?_ ?_ (F n)
  · intro c t ht
    simp only [SimpleFunc.const_zero, SimpleFunc.coe_piecewise, SimpleFunc.coe_const,
      SimpleFunc.coe_zero, Set.piecewise_eq_indicator]
    exact measurable_lintegral_indicator_const_of_pointwise_finite κ hκ ht c
  · intro g₁ g₂ _ hm₁ hm₂
    simp only [SimpleFunc.coe_add, Pi.add_apply]
    have h_add :
      (fun a => ∫⁻ b, g₁ (a, b) + g₂ (a, b) ∂κ a) =
        (fun a => ∫⁻ b, g₁ (a, b) ∂κ a) + fun a => ∫⁻ b, g₂ (a, b) ∂κ a := by
      ext1 a
      rw [Pi.add_apply, lintegral_add_left (by fun_prop)]
    rw [h_add]
    exact Measurable.add hm₁ hm₂

/-! ### Internal adapter (a proof device, not a carrier) -/

/-- Points of `circleIndexSet` have positive radius. -/
theorem circleIndexSet_fst_pos {p : ℝ × ℂ} (hp : p ∈ circleIndexSet) : 0 < p.1 := hp.1

/-- The zero-off-`CircleDomain` extension of `F` is continuous on `circleIndexSet`. -/
theorem continuousOn_circleAdapter (F : C(CircleDomain, ℝ)) :
    ContinuousOn (fun p : ℝ × ℂ => if h : 0 < p.1 then F ⟨p, h⟩ else 0) circleIndexSet := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hc : Continuous fun p : circleIndexSet => F ⟨(p : ℝ × ℂ), circleIndexSet_fst_pos p.2⟩ :=
    F.continuous.comp (Continuous.subtype_mk continuous_subtype_val fun p => circleIndexSet_fst_pos p.2)
  refine hc.congr fun p => ?_
  simp only [Set.domRestrict_apply, circleIndexSet_fst_pos p.2, ↓reduceDIte]

/-- **Internal adapter, not a public carrier.** The zero-off-`CircleDomain` extension of `F` to a canonical profile. It
transports the canonical theory (`profileMeasure`, `profileMeasure_ae_eq`) to the actual carrier; no public statement of
this file reads it off `CircleDomain`. -/
def circleAdapter (F : C(CircleDomain, ℝ)) : CanonicalProfile :=
  ⟨fun p => if h : 0 < p.1 then F ⟨p, h⟩ else 0, continuousOn_circleAdapter F⟩

theorem measurable_circleAdapter : Measurable circleAdapter := by
  have hval : Measurable fun F : C(CircleDomain, ℝ) =>
      fun p : ℝ × ℂ => if h : 0 < p.1 then F ⟨p, h⟩ else 0 := by
    refine Measurable.of_eval fun p => ?_
    by_cases hp : 0 < p.1
    · simp only [hp, ↓reduceDIte]
      exact ContinuousMap.measurable_eval _
    · simp only [hp, ↓reduceDIte]
      exact measurable_const
  exact Measurable.subtype_mk hval

/-! ### The dyadic formula on the actual carrier -/

/-- The LQG exponent at the dyadic radius `2^{-k}` of an actual profile `F`, `z ↦ F(2^{-k}, z) - α₀ ⨍_{∂B_{2^{-k}}(z)} log|·|`:
the value of `fieldCircleAverage α₀` (Defs/GFF.lean:118) at radius `dyadicScale k`, read on `CircleDomain` only. -/
noncomputable def circleRadiusField (α₀ : ℝ) (F : C(CircleDomain, ℝ)) (k : ℕ) : ℂ → ℝ :=
  fun z => F ⟨(dyadicScale k, z), dyadicScale_pos k⟩ -
    α₀ * Real.circleAverage (fun x => Real.log ‖x‖) z (dyadicScale k)

/-- The dyadic LQG approximation of an actual profile at scale `2^{-k}`: the formula of `profileApprox`
(LQGProfileApprox.lean:45) with `circleRadiusField` in place of `profileRadiusField`. -/
noncomputable def circleProfileApprox (γ α₀ : ℝ) (k : ℕ) (F : C(CircleDomain, ℝ)) : Measure ℂ :=
  profileDecoder γ (dyadicScale k) (circleRadiusField α₀ F k)

/-- The good set of actual profiles: `goodProfiles` (LQGGoodProfiles.lean:38) with `circleProfileApprox`. -/
def circleGoodProfiles (γ α₀ : ℝ) : Set C(CircleDomain, ℝ) :=
  {F | (∀ R : ℕ, ⨆ n : ℕ, circleProfileApprox γ α₀ n F (closedBall (0 : ℂ) ((R : ℝ) + 1)) < ⊤) ∧
    ∀ g ∈ testFamily, CauchySeq (fun n : ℕ => ∫ z, g z ∂(circleProfileApprox γ α₀ n F))}

open scoped Classical in
/-- The limit functional of an actual profile: the formula of `profileLimit` (LQGProfileMeasure.lean:24). -/
noncomputable def circleProfileLimit (γ α₀ : ℝ) (F : C(CircleDomain, ℝ))
    (ψ : CompactlySupportedContinuousMap ℂ ℝ) : ℝ :=
  if F ∈ circleGoodProfiles γ α₀ then
    limUnder atTop (fun n : ℕ => ∫ z, ψ z ∂(circleProfileApprox γ α₀ n F)) else 0

theorem circleRadiusField_eq (α₀ : ℝ) (F : C(CircleDomain, ℝ)) (k : ℕ) :
    circleRadiusField α₀ F k = profileRadiusField α₀ (dyadicScale k) (circleAdapter F) := by
  funext z
  simp only [circleRadiusField, profileRadiusField, fieldCircleAverage, profileField, circleAdapter,
    dyadicScale_pos k, ↓reduceDIte]

theorem circleProfileApprox_eq (γ α₀ : ℝ) (k : ℕ) (F : C(CircleDomain, ℝ)) :
    circleProfileApprox γ α₀ k F = profileApprox γ α₀ k (circleAdapter F) := by
  unfold circleProfileApprox profileApprox
  rw [circleRadiusField_eq]

theorem circleGoodProfiles_iff (γ α₀ : ℝ) (F : C(CircleDomain, ℝ)) :
    F ∈ circleGoodProfiles γ α₀ ↔ circleAdapter F ∈ goodProfiles γ α₀ := by
  simp only [circleGoodProfiles, goodProfiles, Set.mem_ofPred_eq, circleProfileApprox_eq]

theorem circleProfileLimit_eq (γ α₀ : ℝ) (F : C(CircleDomain, ℝ))
    (ψ : CompactlySupportedContinuousMap ℂ ℝ) :
    circleProfileLimit γ α₀ F ψ = profileLimit γ α₀ (circleAdapter F) ψ := by
  unfold circleProfileLimit profileLimit
  by_cases h : F ∈ circleGoodProfiles γ α₀
  · have h' : circleAdapter F ∈ goodProfiles γ α₀ := (circleGoodProfiles_iff γ α₀ F).1 h
    simp only [h, h', ↓reduceIte, circleProfileApprox_eq]
  · have h' : circleAdapter F ∉ goodProfiles γ α₀ := fun h'' => h ((circleGoodProfiles_iff γ α₀ F).2 h'')
    simp only [h, h', ↓reduceIte]

/-- The limit functional of an actual profile, a positive linear map on `C_c(ℂ, ℝ)`: the carrier-`C(CircleDomain, ℝ)`
version of `profileFunctional` (LQGProfileMeasure.lean:47), with the same positivity proofs transported through the
characterization `circleProfileLimit_eq`. -/
noncomputable def circleProfileFunctional (γ α₀ : ℝ) (F : C(CircleDomain, ℝ)) :
    CompactlySupportedContinuousMap ℂ ℝ →ₚ[ℝ] ℝ where
  toFun := circleProfileLimit γ α₀ F
  map_add' ψ₁ ψ₂ := by
    show circleProfileLimit γ α₀ F (ψ₁ + ψ₂) = circleProfileLimit γ α₀ F ψ₁ + circleProfileLimit γ α₀ F ψ₂
    rw [circleProfileLimit_eq, circleProfileLimit_eq, circleProfileLimit_eq]
    exact (profileFunctional γ α₀ (circleAdapter F)).map_add' ψ₁ ψ₂
  map_smul' c ψ := by
    show circleProfileLimit γ α₀ F (c • ψ) = c • circleProfileLimit γ α₀ F ψ
    rw [circleProfileLimit_eq, circleProfileLimit_eq]
    exact (profileFunctional γ α₀ (circleAdapter F)).map_smul' c ψ
  monotone' ψ₁ ψ₂ h := by
    show circleProfileLimit γ α₀ F ψ₁ ≤ circleProfileLimit γ α₀ F ψ₂
    rw [circleProfileLimit_eq, circleProfileLimit_eq]
    exact (profileFunctional γ α₀ (circleAdapter F)).monotone' h

/-- **The coded LQG measure of an actual circle profile**: the Riesz–Markov–Kakutani measure of
`circleProfileFunctional` (the carrier-`C(CircleDomain, ℝ)` version of `profileMeasure`, LQGProfileMeasure.lean:97). -/
noncomputable def circleProfileMeasure (γ α₀ : ℝ) (F : C(CircleDomain, ℝ)) : Measure ℂ :=
  RealRMK.rieszMeasure (circleProfileFunctional γ α₀ F)

theorem circleProfileFunctional_eq (γ α₀ : ℝ) (F : C(CircleDomain, ℝ)) :
    circleProfileFunctional γ α₀ F = profileFunctional γ α₀ (circleAdapter F) :=
  DFunLike.ext _ _ fun ψ => circleProfileLimit_eq γ α₀ F ψ

/-- **Characterization of the coded measure.** The dyadic formula on the actual carrier gives the canonical
`profileMeasure` of the zero-off-`CircleDomain` extension: `circleProfileMeasure γ α₀ F = profileMeasure γ α₀ (circleAdapter F)`. -/
theorem circleProfileMeasure_eq (γ α₀ : ℝ) (F : C(CircleDomain, ℝ)) :
    circleProfileMeasure γ α₀ F = profileMeasure γ α₀ (circleAdapter F) := by
  unfold circleProfileMeasure profileMeasure
  rw [circleProfileFunctional_eq]

/-! ### Factorization of the canonical measure through positive radii -/

/-- The dyadic approximations of a canonical profile depend only on its values on `circleIndexSet`. -/
theorem profileApprox_eq_of_eq_on_circleIndexSet (γ α₀ : ℝ) (k : ℕ) {c c' : CanonicalProfile}
    (h : ∀ p ∈ circleIndexSet, c.1 p = c'.1 p) : profileApprox γ α₀ k c = profileApprox γ α₀ k c' := by
  unfold profileApprox
  congr 1
  funext z
  have hp : (dyadicScale k, z) ∈ circleIndexSet := Set.mk_mem_prod (dyadicScale_pos k) (Set.mem_univ z)
  simp only [profileRadiusField, fieldCircleAverage, profileField, h _ hp]

/-- **Factorization through positive radii.** The canonical `profileMeasure` depends only on the restriction of the
profile to `circleIndexSet`; this is the independence of the zero-off-`CircleDomain` extension used by `circleAdapter`. -/
theorem profileMeasure_eq_of_eq_on_circleIndexSet (γ α₀ : ℝ) {c c' : CanonicalProfile}
    (h : ∀ p ∈ circleIndexSet, c.1 p = c'.1 p) : profileMeasure γ α₀ c = profileMeasure γ α₀ c' := by
  have hk : ∀ k : ℕ, profileApprox γ α₀ k c = profileApprox γ α₀ k c' :=
    fun k => profileApprox_eq_of_eq_on_circleIndexSet γ α₀ k h
  have hgood : c ∈ goodProfiles γ α₀ ↔ c' ∈ goodProfiles γ α₀ := by
    simp only [goodProfiles, Set.mem_ofPred_eq, hk]
  have hlim : profileFunctional γ α₀ c = profileFunctional γ α₀ c' := by
    refine DFunLike.ext _ _ fun ψ => ?_
    show profileLimit γ α₀ c ψ = profileLimit γ α₀ c' ψ
    unfold profileLimit
    by_cases hc : c ∈ goodProfiles γ α₀
    · have hc' : c' ∈ goodProfiles γ α₀ := hgood.1 hc
      simp only [hc, hc', ↓reduceIte, hk]
    · have hc' : c' ∉ goodProfiles γ α₀ := fun h' => hc (hgood.2 h')
      simp only [hc, hc', ↓reduceIte]
  unfold profileMeasure
  rw [hlim]

/-! ### Measurability and local finiteness on the actual carrier -/

instance isLocallyFiniteMeasure_circleProfileMeasure (γ α₀ : ℝ) (F : C(CircleDomain, ℝ)) :
    IsLocallyFiniteMeasure (circleProfileMeasure γ α₀ F) := by
  rw [circleProfileMeasure_eq]
  infer_instance

theorem measurable_circleProfileMeasure (γ α₀ : ℝ) : Measurable (circleProfileMeasure γ α₀) := by
  have h : circleProfileMeasure γ α₀ = fun F => profileMeasure γ α₀ (circleAdapter F) :=
    funext fun F => circleProfileMeasure_eq γ α₀ F
  rw [h]
  exact (measurable_profileMeasure γ α₀).comp measurable_circleAdapter

/-- The coded LQG measure restricted to the unit disc `B_1`, as a kernel on the actual carrier. -/
def circleProfileMeasureBall (γ : ℝ) : Kernel C(CircleDomain, ℝ) ℂ where
  toFun F := (circleProfileMeasure γ 0 F).restrict (ball (0 : ℂ) 1)
  measurable' := by
    refine Measure.measurable_of_measurable_coe _ (fun t ht => ?_)
    simp only [Measure.restrict_apply ht]
    exact (Measure.measurable_measure.mp (measurable_circleProfileMeasure γ 0)) _
      (ht.inter measurableSet_ball)

instance isFiniteMeasure_circleProfileMeasureBall (γ : ℝ) (F : C(CircleDomain, ℝ)) :
    IsFiniteMeasure (circleProfileMeasureBall γ F) := by
  show IsFiniteMeasure ((circleProfileMeasure γ 0 F).restrict (ball (0 : ℂ) 1))
  exact isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne

/-- **Measurability of the inner Palm integral** on the actual carrier: for jointly measurable `Ψ`, the map
`F ↦ ∫_{B_1} Ψ(F, z) circleProfileMeasure γ 0 F (dz)` is measurable. -/
theorem measurable_circle_palm_lintegral (γ : ℝ) {Ψ : C(CircleDomain, ℝ) → ℂ → ℝ≥0∞}
    (hΨ : Measurable (fun p : C(CircleDomain, ℝ) × ℂ => Ψ p.1 p.2)) :
    Measurable fun F : C(CircleDomain, ℝ) => ∫⁻ z in ball (0 : ℂ) 1, Ψ F z ∂(circleProfileMeasure γ 0 F) :=
  measurable_lintegral_kernel_of_pointwise_finite (circleProfileMeasureBall γ)
    (fun _ => inferInstance) (f := fun F z => Ψ F z) hΨ

/-! ### The actual profile of a whole-plane GFF -/

/-- **The actual continuous positive-circle profile** of a whole-plane GFF with pairing functional `T`: the named circle
decoder `circleCompatDecoder` (r10 lines 1313-1323; CircleDecoderAdditionCompatibility.lean:54) at a literal mollifier
`rho` and a family `q : I → CircleDomain`, with the scales `countableCircleScale hρ q`
(CountableMollifiedCircleConvergence.lean:138). Its identification with the circle field and its DMS compatibility are
`circleCompatDecoder_gff_identification` (CircleDecoderGFFIdentification.lean:67). -/
noncomputable def circleCodedProfile {rho : ℂ → ℝ} (hρ : IsLiteralMollifier rho) {I : Type*}
    (q : I → CircleDomain) (T : (ℂ → ℝ) → ℝ) : C(CircleDomain, ℝ) :=
  circleCompatDecoder rho q (countableCircleScale hρ q) T

/-- **The LQG measure is the coded measure of the actual profile almost surely.** For a whole-plane GFF with LQG measure
`μ` (`IsLQGMeasureOfField`, Defs/LQG.lean:73) and a random profile `F` which is a.s. the circle field on `CircleDomain`,
`μ ω = circleProfileMeasure γ 0 (F ω)` for almost every `ω`. Derived from `profileMeasure_ae_eq`
(LQGProfileMeasureAE.lean:58) through the adapter and `circleProfileMeasure_eq`. -/
theorem ae_lqgMeasure_eq_circleProfileMeasure {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {F : Ω → C(CircleDomain, ℝ)} (hF : ∀ᵐ ω ∂P, ∀ p : CircleDomain, F ω p = hcirc ω p.1.1 p.1.2) :
    ∀ᵐ ω ∂P, μ ω = circleProfileMeasure γ 0 (F ω) := by
  have hcJ : ∀ᵐ ω ∂P, ∀ p ∈ circleIndexSet, (circleAdapter (F ω)).1 p = hcirc ω p.1 p.2 := by
    filter_upwards [hF] with ω hω
    intro p hp
    have hpos : 0 < p.1 := circleIndexSet_fst_pos hp
    show (if h : 0 < p.1 then F ω ⟨p, h⟩ else 0) = hcirc ω p.1 p.2
    simp only [hpos, ↓reduceDIte]
    exact hω ⟨p, hpos⟩
  filter_upwards [profileMeasure_ae_eq hμ hcJ] with ω hω
  rw [hω, circleProfileMeasure_eq]

end HarmonicBalls

end
