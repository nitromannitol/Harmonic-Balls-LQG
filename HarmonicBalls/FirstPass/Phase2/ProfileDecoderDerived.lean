import HarmonicBalls.FirstPass.Frozen.S8d
import HarmonicBalls.FirstPass.Phase2.MassFunctionalDerived
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-!
# Derivation of `LQGMeasureOfProfileMeasurableFrozen`

The decoder is the vague limit of the dyadic
approximations of `circleProfile y` on its convergence locus, and `0` elsewhere; `IsWholePlaneGFF.ae_circle_map_eq_raw`
identifies it with `μ ω` almost surely. The route's step (b), measurability of the convergence locus, is not supplied
by the source. It is proved here by countable determination: vague convergence of the approximations is tested on a
countable family `D` of compactly supported continuous functions with a uniform mass bound (`TestFamily`,
`tendsto_of_testFamily`). The limit measure is the Riesz measure (`RealRMK.rieszMeasure`) of the limit functional.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal CompactlySupported

namespace HarmonicBalls

universe u

namespace ProfileDecoderDerived

/-! ### 1. A countable test family -/

/-- A countable family `D` of compactly supported continuous test functions. (i) Each ball `closedBall 0 n` is
covered by a mass-bounding member `D m`: `0 ≤ D m` and `1 ≤ D m` on the ball. (ii) Every `f` supported in
`closedBall 0 n` is approximated uniformly, to any `δ > 0`, by some `D m` supported in `closedBall 0 n`. -/
structure TestFamily where
  D : ℕ → C_c(ℂ, ℝ)
  mass : ∀ n : ℕ, ∃ m : ℕ, (∀ z : ℂ, 0 ≤ D m z) ∧ ∀ z ∈ closedBall (0 : ℂ) n, 1 ≤ D m z
  approx : ∀ (n : ℕ) (f : C_c(ℂ, ℝ)), tsupport ⇑f ⊆ closedBall (0 : ℂ) n → ∀ δ : ℝ, 0 < δ →
    ∃ m : ℕ, tsupport ⇑(D m) ⊆ closedBall (0 : ℂ) n ∧ ∀ z : ℂ, |f z - D m z| ≤ δ

/-- The explicit cutoff: `1` on `closedBall 0 n`, `0` outside `closedBall 0 (n + 1)`. -/
def cutoffFun (n : ℕ) (z : ℂ) : ℝ := max 0 (min 1 ((n : ℝ) + 1 - ‖z‖))

theorem continuous_cutoffFun (n : ℕ) : Continuous (cutoffFun n) := by
  unfold cutoffFun
  fun_prop

/-- The cutoff as a compactly supported continuous function. -/
def cutoffC (n : ℕ) : C_c(ℂ, ℝ) where
  toContinuousMap := ⟨cutoffFun n, continuous_cutoffFun n⟩
  hasCompactSupport' := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1)) fun z hz => ?_
    have hz' : (n : ℝ) + 1 < ‖z‖ := by simpa [mem_closedBall, dist_zero_right] using hz
    have h1 : (n : ℝ) + 1 - ‖z‖ ≤ 0 := by linarith
    show cutoffFun n z = 0
    unfold cutoffFun
    rw [min_eq_right (show (n : ℝ) + 1 - ‖z‖ ≤ 1 by linarith), max_eq_left h1]

theorem cutoffC_nonneg (n : ℕ) (z : ℂ) : 0 ≤ cutoffC n z := by
  show 0 ≤ cutoffFun n z
  unfold cutoffFun
  exact le_max_left _ _

theorem cutoffC_mass (n : ℕ) (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) n) : 1 ≤ cutoffC n z := by
  have hz' : ‖z‖ ≤ (n : ℝ) := by simpa [mem_closedBall, dist_zero_right] using hz
  show 1 ≤ cutoffFun n z
  unfold cutoffFun
  rw [min_eq_left (show (1 : ℝ) ≤ (n : ℝ) + 1 - ‖z‖ by linarith)]
  exact le_max_of_le_right le_rfl

/-- Restriction of a compactly supported function to a closed ball, as a continuous function on the ball. -/
def restrictBall (n : ℕ) (g : C_c(ℂ, ℝ)) : C(closedBall (0 : ℂ) n, ℝ) :=
  ContinuousMap.restrict (closedBall (0 : ℂ) n) g.toContinuousMap

theorem exists_testFamily : Nonempty TestFamily := by
  classical
  let S : ℕ → Set C_c(ℂ, ℝ) := fun n => {g | tsupport ⇑g ⊆ closedBall (0 : ℂ) n}
  have hsep : ∀ n : ℕ, TopologicalSpace.IsSeparable (restrictBall n '' S n) := fun n =>
    TopologicalSpace.IsSeparable.of_separableSpace _
  have hex : ∀ n : ℕ, ∃ t ⊆ restrictBall n '' S n, t.Countable ∧ restrictBall n '' S n ⊆ closure t :=
    fun n => (hsep n).exists_countable_dense_subset
  choose t hts htc hdense using hex
  have hlift : ∀ n, ∀ τ ∈ t n, ∃ g ∈ S n, restrictBall n g = τ := fun n τ hτ => hts n hτ
  choose! lift hliftS hliftR using hlift
  let Dset : Set C_c(ℂ, ℝ) := Set.range cutoffC ∪ ⋃ n, lift n '' t n
  have hcount : Dset.Countable :=
    (countable_range _).union (countable_iUnion fun n => (htc n).image _)
  obtain ⟨D, hD⟩ := hcount.exists_eq_range ⟨cutoffC 0, Or.inl ⟨0, rfl⟩⟩
  have hmemD : ∀ g ∈ Dset, ∃ m, D m = g := fun g hg => by
    rw [hD] at hg
    exact hg
  refine ⟨⟨D, ?_, ?_⟩⟩
  · intro n
    obtain ⟨m, hm⟩ := hmemD (cutoffC n) (Or.inl ⟨n, rfl⟩)
    refine ⟨m, fun z => ?_, fun z hz => ?_⟩
    · rw [hm]
      exact cutoffC_nonneg n z
    · rw [hm]
      exact cutoffC_mass n z hz
  · intro n f hf δ hδ
    have hfS : f ∈ S n := hf
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 (hdense n ⟨f, hfS, rfl⟩) δ hδ
    have hdmem : lift n b ∈ Dset := Or.inr (mem_iUnion.2 ⟨n, mem_image_of_mem _ hb⟩)
    obtain ⟨m, hm⟩ := hmemD _ hdmem
    have hdS : tsupport ⇑(lift n b) ⊆ closedBall (0 : ℂ) n := hliftS n b hb
    refine ⟨m, ?_, fun z => ?_⟩
    · rw [hm]
      exact hdS
    · rw [hm]
      by_cases hz : z ∈ closedBall (0 : ℂ) n
      · have h3 : dist (f z) (lift n b z) ≤ dist (restrictBall n f) (restrictBall n (lift n b)) :=
          ContinuousMap.dist_apply_le_dist (f := restrictBall n f)
            (g := restrictBall n (lift n b)) (⟨z, hz⟩ : closedBall (0 : ℂ) n)
        rw [hliftR n b hb] at h3
        rw [Real.dist_eq] at h3
        exact h3.trans hdist.le
      · have hf0 : f z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hf h))
        have hd0 : lift n b z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hdS h))
        rw [hf0, hd0, sub_zero, abs_zero]
        exact hδ.le

/-! ### 2. Vague convergence is tested on the family -/

theorem integrable_of_cc (g : C_c(ℂ, ℝ)) (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] :
    Integrable g μ :=
  g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport

/-- Countable determination: if every `∫ D m dν_k` converges, then every `∫ f dν_k`, `f ∈ C_c`, converges. -/
theorem tendsto_of_testFamily (T : TestFamily) {ν : ℕ → Measure ℂ}
    (hν : ∀ k, IsLocallyFiniteMeasure (ν k))
    (hconv : ∀ m : ℕ, ∃ L, Tendsto (fun k => ∫ z, T.D m z ∂(ν k)) atTop (𝓝 L))
    (f : C_c(ℂ, ℝ)) : ∃ L, Tendsto (fun k => ∫ z, f z ∂(ν k)) atTop (𝓝 L) := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1
    f.hasCompactSupport.isCompact.isBounded
  have hsupp : tsupport ⇑f ⊆ closedBall (0 : ℂ) ⌈r⌉₊ :=
    hr.trans (closedBall_subset_closedBall (Nat.le_ceil r))
  obtain ⟨m₀, hm₀nonneg, hm₀one⟩ := T.mass ⌈r⌉₊
  obtain ⟨L₀, hL₀⟩ := hconv m₀
  have hK₀ : 0 < |L₀| + 1 := by positivity
  have hev : ∀ᶠ k in atTop, ∫ z, T.D m₀ z ∂(ν k) < |L₀| + 1 :=
    hL₀.eventually (gt_mem_nhds (by linarith [le_abs_self L₀]))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  have hcauchy : CauchySeq (fun k => ∫ z, f z ∂(ν k)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    set δ : ℝ := ε / (4 * (|L₀| + 1)) with hδdef
    have hδ : 0 < δ := div_pos hε (by positivity)
    obtain ⟨m₁, hm₁supp, hm₁close⟩ := T.approx ⌈r⌉₊ f hsupp δ hδ
    obtain ⟨L₁, hL₁⟩ := hconv m₁
    obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 hL₁.cauchySeq (ε / 2) (by positivity)
    have key : ∀ k, N₀ ≤ k → |∫ z, f z ∂(ν k) - ∫ z, T.D m₁ z ∂(ν k)| ≤ ε / 4 := by
      intro k hk
      have := hν k
      have hpt : ∀ z, ‖f z - T.D m₁ z‖ ≤ δ * T.D m₀ z := by
        intro z
        by_cases hz : z ∈ closedBall (0 : ℂ) ⌈r⌉₊
        · have h1 : ‖f z - T.D m₁ z‖ ≤ δ := by
            rw [Real.norm_eq_abs]
            exact hm₁close z
          have h2 : 1 ≤ T.D m₀ z := hm₀one z hz
          calc ‖f z - T.D m₁ z‖ ≤ δ := h1
            _ = δ * 1 := (mul_one δ).symm
            _ ≤ δ * T.D m₀ z := mul_le_mul_of_nonneg_left h2 hδ.le
        · have hf0 : f z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hsupp h))
          have hd0 : T.D m₁ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hm₁supp h))
          rw [hf0, hd0, sub_zero, norm_zero]
          exact mul_nonneg hδ.le (hm₀nonneg z)
      have hb : ‖∫ z, (f z - T.D m₁ z) ∂(ν k)‖ ≤ ∫ z, δ * T.D m₀ z ∂(ν k) :=
        norm_integral_le_of_norm_le ((integrable_of_cc (T.D m₀) (ν k)).const_mul δ)
          (Eventually.of_forall hpt)
      rw [integral_const_mul, integral_sub (integrable_of_cc f _) (integrable_of_cc (T.D m₁) _),
        Real.norm_eq_abs] at hb
      have hc : ∫ z, T.D m₀ z ∂(ν k) ≤ |L₀| + 1 := (hN₀ k hk).le
      calc |∫ z, f z ∂(ν k) - ∫ z, T.D m₁ z ∂(ν k)| ≤ δ * ∫ z, T.D m₀ z ∂(ν k) := hb
        _ ≤ δ * (|L₀| + 1) := mul_le_mul_of_nonneg_left hc hδ.le
        _ = ε / 4 := by rw [hδdef]; field_simp
    refine ⟨max N₀ N₁, fun p hp q hq => ?_⟩
    have hp' : N₀ ≤ p := (le_max_left _ _).trans hp
    have hq' : N₀ ≤ q := (le_max_left _ _).trans hq
    have hb : |(∫ z, T.D m₁ z ∂(ν p)) - ∫ z, T.D m₁ z ∂(ν q)| < ε / 2 := by
      have := hN₁ p ((le_max_right _ _).trans hp) q ((le_max_right _ _).trans hq)
      rwa [Real.dist_eq] at this
    have kp := key p hp'
    have kq := key q hq'
    have h2 : |(∫ z, T.D m₁ z ∂(ν q)) - ∫ z, f z ∂(ν q)| ≤ ε / 4 := by
      rw [abs_sub_comm]
      exact kq
    have h3 := abs_add_three ((∫ z, f z ∂(ν p)) - ∫ z, T.D m₁ z ∂(ν p))
      ((∫ z, T.D m₁ z ∂(ν p)) - ∫ z, T.D m₁ z ∂(ν q)) ((∫ z, T.D m₁ z ∂(ν q)) - ∫ z, f z ∂(ν q))
    have h4 : |(∫ z, f z ∂(ν p)) - ∫ z, f z ∂(ν q)| =
        |((∫ z, f z ∂(ν p)) - ∫ z, T.D m₁ z ∂(ν p)) + ((∫ z, T.D m₁ z ∂(ν p)) - ∫ z, T.D m₁ z ∂(ν q))
          + ((∫ z, T.D m₁ z ∂(ν q)) - ∫ z, f z ∂(ν q))| := by
      congr 1
      ring
    rw [Real.dist_eq]
    linarith [h3, h4, kp, hb, h2]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨L, hL⟩

/-- The positive linear functional `g ↦ lim_k ∫ g dν_k` on `C_c(ℂ, ℝ)`. -/
theorem tendsto_limUnder_test (ν : ℕ → Measure ℂ) (hconv : ∀ g : C_c(ℂ, ℝ), ∃ L,
    Tendsto (fun k => ∫ z, g z ∂(ν k)) atTop (𝓝 L)) (g : C_c(ℂ, ℝ)) :
    Tendsto (fun k => ∫ z, g z ∂(ν k)) atTop
      (𝓝 (limUnder atTop (fun k => ∫ z, g z ∂(ν k)))) :=
  tendsto_nhds_limUnder (hconv g)

/-- The limit functional of a sequence of locally finite measures along which all test integrals converge. -/
def limFunctional (ν : ℕ → Measure ℂ) (hν : ∀ k, IsLocallyFiniteMeasure (ν k))
    (hconv : ∀ g : C_c(ℂ, ℝ), ∃ L, Tendsto (fun k => ∫ z, g z ∂(ν k)) atTop (𝓝 L)) :
    C_c(ℂ, ℝ) →ₚ[ℝ] ℝ where
  toFun g := limUnder atTop (fun k => ∫ z, g z ∂(ν k))
  map_add' f g := by
    show limUnder atTop (fun k => ∫ z, (f + g) z ∂(ν k)) =
      limUnder atTop (fun k => ∫ z, f z ∂(ν k)) + limUnder atTop (fun k => ∫ z, g z ∂(ν k))
    refine tendsto_nhds_unique (tendsto_limUnder_test ν hconv (f + g)) ?_
    refine Tendsto.congr (fun k => ?_)
      ((tendsto_limUnder_test ν hconv f).add (tendsto_limUnder_test ν hconv g))
    have := hν k
    simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
    exact (integral_add (integrable_of_cc f _) (integrable_of_cc g _)).symm
  map_smul' c f := by
    show limUnder atTop (fun k => ∫ z, (c • f) z ∂(ν k)) =
      c • limUnder atTop (fun k => ∫ z, f z ∂(ν k))
    rw [smul_eq_mul]
    refine tendsto_nhds_unique (tendsto_limUnder_test ν hconv (c • f)) ?_
    refine Tendsto.congr (fun k => ?_) ((tendsto_limUnder_test ν hconv f).const_mul c)
    have := hν k
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
    exact (integral_const_mul c _).symm
  monotone' := by
    intro f g hfg
    show limUnder atTop (fun k => ∫ z, f z ∂(ν k)) ≤ limUnder atTop (fun k => ∫ z, g z ∂(ν k))
    refine le_of_tendsto_of_tendsto' (tendsto_limUnder_test ν hconv f)
      (tendsto_limUnder_test ν hconv g) (fun k => ?_)
    have := hν k
    exact integral_mono (integrable_of_cc f _) (integrable_of_cc g _) (fun z => hfg z)

/-! ### 3. The dyadic approximations depend measurably on the profile -/

theorem fca_circleProfile_eq (α : ℝ) (y : C(CircleParameter, ℝ)) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    fieldCircleAverage α (circleProfile y) ε z =
      y (⟨ε, hε⟩, z) - α * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ε := by
  simp only [fieldCircleAverage, circleProfile, hε, ↓reduceDIte]

theorem continuous_fca (α : ℝ) (y : C(CircleParameter, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun z : ℂ => fieldCircleAverage α (circleProfile y) ε z := by
  have h : (fun z : ℂ => fieldCircleAverage α (circleProfile y) ε z) =
      fun z => y (⟨ε, hε⟩, z) - α * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ε :=
    funext fun z => fca_circleProfile_eq α y hε z
  rw [h]
  exact (y.continuous.comp (continuous_const.prodMk continuous_id)).sub
    ((MassFunctionalDerived.continuous_circleAverage_log_norm hε).const_mul α)

/-- The dyadic approximation `ε^{γ²/2} e^{γ h_ε(z)} dz` of the profile `y`, at the scale `2^{-k}`. -/
def approxMeas (γ α : ℝ) (y : C(CircleParameter, ℝ)) (k : ℕ) : Measure ℂ :=
  lqgApprox γ (fieldCircleAverage α (circleProfile y)) (dyadicScale k)

theorem isLocallyFiniteMeasure_approxMeas (γ α : ℝ) (y : C(CircleParameter, ℝ)) (k : ℕ) :
    IsLocallyFiniteMeasure (approxMeas γ α y k) :=
  MassFunctionalDerived.isLocallyFiniteMeasure_lqgApprox γ (continuous_fca α y (dyadicScale_pos k))

/-- The integrand `ε^{γ²/2} e^{γ h_ε(z)} f(z)` of the approximation at scale `ε`. -/
def approxIntegrand (γ α : ℝ) {ε : ℝ} (hε : 0 < ε) (f : ℂ → ℝ) (y : C(CircleParameter, ℝ)) (z : ℂ) : ℝ :=
  ε ^ (γ ^ 2 / 2) * Real.exp (γ * (y (⟨ε, hε⟩, z) - α * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ε)) *
    f z

theorem continuous_approxIntegrand (γ α : ℝ) {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℝ} (hf : Continuous f) :
    Continuous fun q : C(CircleParameter, ℝ) × ℂ => approxIntegrand γ α hε f q.1 q.2 := by
  have hE : Continuous fun q : C(CircleParameter, ℝ) × ℂ => q.1 (⟨ε, hε⟩, q.2) :=
    continuous_eval.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  have hA : Continuous fun q : C(CircleParameter, ℝ) × ℂ =>
      Real.circleAverage (fun x : ℂ => Real.log ‖x‖) q.2 ε :=
    (MassFunctionalDerived.continuous_circleAverage_log_norm hε).comp continuous_snd
  have hρ : Continuous fun q : C(CircleParameter, ℝ) × ℂ =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * (q.1 (⟨ε, hε⟩, q.2) -
        α * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) q.2 ε)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hE.sub (continuous_const.mul hA))))
  exact hρ.mul (hf.comp continuous_snd)

theorem measurable_integral_approxMeas (γ α : ℝ) {f : ℂ → ℝ} (hf : Continuous f) (k : ℕ) :
    Measurable fun y : C(CircleParameter, ℝ) => ∫ z, f z ∂(approxMeas γ α y k) := by
  have hε : 0 < dyadicScale k := dyadicScale_pos k
  have key : ∀ y : C(CircleParameter, ℝ), ∫ z, f z ∂(approxMeas γ α y k) =
      ∫ z, approxIntegrand γ α hε f y z := by
    intro y
    have hρ : Continuous fun z : ℂ => dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldCircleAverage α (circleProfile y) (dyadicScale k) z) :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_fca α y hε)))
    unfold approxMeas lqgApprox
    rw [integral_withDensity_eq_integral_toReal_smul (f := fun z : ℂ => ENNReal.ofReal
      (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage α (circleProfile y) (dyadicScale k) z)))
      hρ.measurable.ennreal_ofReal (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
    congr 1
    funext z
    have hnn : 0 ≤ dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldCircleAverage α (circleProfile y) (dyadicScale k) z) :=
      mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
    rw [smul_eq_mul, ENNReal.toReal_ofReal hnn, approxIntegrand, fca_circleProfile_eq α y hε z]
  have hSM : StronglyMeasurable fun q : C(CircleParameter, ℝ) × ℂ => approxIntegrand γ α hε f q.1 q.2 :=
    (continuous_approxIntegrand γ α hε hf).stronglyMeasurable
  have hmeas : Measurable fun y : C(CircleParameter, ℝ) => ∫ z, approxIntegrand γ α hε f y z :=
    (hSM.integral_prod_right (ν := volume)).measurable
  simp only [key]
  exact hmeas

/-! ### 4. The convergence locus and the decoder -/

/-- The convergence locus: profiles whose dyadic approximations integrate every test function of the family to a
convergent sequence. -/
def convSet (T : TestFamily) (γ α : ℝ) : Set (C(CircleParameter, ℝ)) :=
  {y | ∀ m : ℕ, ∃ L, Tendsto (fun k => ∫ z, T.D m z ∂(approxMeas γ α y k)) atTop (𝓝 L)}

theorem measurableSet_convSet (T : TestFamily) (γ α : ℝ) : MeasurableSet (convSet T γ α) := by
  have h : convSet T γ α = ⋂ m : ℕ,
      {y | ∃ L, Tendsto (fun k => ∫ z, T.D m z ∂(approxMeas γ α y k)) atTop (𝓝 L)} := by
    ext y
    simp [convSet]
  rw [h]
  exact MeasurableSet.iInter fun m => measurableSet_exists_tendsto fun k =>
    measurable_integral_approxMeas γ α (T.D m).continuous k

theorem conv_of_mem (T : TestFamily) (γ α : ℝ) {y : C(CircleParameter, ℝ)} (hy : y ∈ convSet T γ α)
    (g : C_c(ℂ, ℝ)) : ∃ L, Tendsto (fun k => ∫ z, g z ∂(approxMeas γ α y k)) atTop (𝓝 L) :=
  tendsto_of_testFamily T (fun k => isLocallyFiniteMeasure_approxMeas γ α y k) hy g

open Classical in
/-- The limit functional of the profile `y`: the vague limit of the dyadic approximations on the convergence locus,
and `0` off it. -/
def decoderFunctional (T : TestFamily) (γ α : ℝ) (y : C(CircleParameter, ℝ)) : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  if hy : y ∈ convSet T γ α then
    limFunctional (fun k => approxMeas γ α y k) (fun k => isLocallyFiniteMeasure_approxMeas γ α y k)
      (fun g => conv_of_mem T γ α hy g)
  else 0

theorem decoderFunctional_of_mem {T : TestFamily} {γ α : ℝ} {y : C(CircleParameter, ℝ)}
    (hy : y ∈ convSet T γ α) (g : C_c(ℂ, ℝ)) :
    decoderFunctional T γ α y g = limUnder atTop (fun k => ∫ z, g z ∂(approxMeas γ α y k)) := by
  simp only [decoderFunctional, hy, ↓reduceDIte]
  rfl

theorem decoderFunctional_of_not_mem {T : TestFamily} {γ α : ℝ} {y : C(CircleParameter, ℝ)}
    (hy : y ∉ convSet T γ α) (g : C_c(ℂ, ℝ)) : decoderFunctional T γ α y g = 0 := by
  simp only [decoderFunctional, hy, ↓reduceDIte]
  rfl

/-- The decoder: the Riesz measure of the limit functional. -/
def decoder (T : TestFamily) (γ α : ℝ) (y : C(CircleParameter, ℝ)) : Measure ℂ :=
  RealRMK.rieszMeasure (decoderFunctional T γ α y)

instance isLocallyFiniteMeasure_decoder (T : TestFamily) (γ α : ℝ) (y : C(CircleParameter, ℝ)) :
    IsLocallyFiniteMeasure (decoder T γ α y) := by
  unfold decoder
  infer_instance

theorem integral_decoder (T : TestFamily) (γ α : ℝ) (y : C(CircleParameter, ℝ)) (g : C_c(ℂ, ℝ)) :
    ∫ z, g z ∂(decoder T γ α y) = decoderFunctional T γ α y g :=
  RealRMK.integral_rieszMeasure _ g

theorem measurable_decoderFunctional_apply (T : TestFamily) (γ α : ℝ) (g : C_c(ℂ, ℝ)) :
    Measurable fun y => decoderFunctional T γ α y g := by
  have hind : ∀ k, Measurable fun y : C(CircleParameter, ℝ) =>
      (convSet T γ α).indicator (fun y => ∫ z, g z ∂(approxMeas γ α y k)) y := fun k =>
    (measurable_integral_approxMeas γ α g.continuous k).indicator (measurableSet_convSet T γ α)
  refine measurable_of_tendsto_metrizable hind ?_
  refine tendsto_pi_nhds.2 fun y => ?_
  by_cases hy : y ∈ convSet T γ α
  · simp only [Set.indicator_of_mem hy]
    rw [decoderFunctional_of_mem hy g]
    obtain ⟨L, hL⟩ := conv_of_mem T γ α hy g
    exact tendsto_nhds_limUnder ⟨L, hL⟩
  · simp only [Set.indicator_of_notMem hy]
    rw [decoderFunctional_of_not_mem hy g]
    exact tendsto_const_nhds

theorem measurable_decoder (T : TestFamily) (γ α : ℝ) : Measurable (decoder T γ α) := by
  refine measurable_measure_of_isOpen (fun y => inferInstance) (fun U hU => ?_)
  obtain ⟨f, hfc, hfcc, hmass⟩ := exists_open_mass_test_functions hU
  have heq : (fun y => decoder T γ α y U) =
      fun y => ⨆ n, ENNReal.ofReal (decoderFunctional T γ α y ⟨⟨f n, hfc n⟩, hfcc n⟩) := by
    funext y
    rw [hmass (decoder T γ α y) inferInstance]
    congr 1
    funext n
    congr 1
    exact integral_decoder T γ α y ⟨⟨f n, hfc n⟩, hfcc n⟩
  rw [heq]
  exact Measurable.iSup fun n =>
    ENNReal.measurable_ofReal.comp (measurable_decoderFunctional_apply T γ α _)

theorem isLQGLimit_decoder (T : TestFamily) (γ α : ℝ) {y : C(CircleParameter, ℝ)}
    (hy : y ∈ convSet T γ α) :
    IsLQGLimit γ (fieldCircleAverage α (circleProfile y)) (decoder T γ α y) := by
  refine ⟨inferInstance, fun f hf hfc => ?_⟩
  have h := integral_decoder T γ α y ⟨⟨f, hf⟩, hfc⟩
  rw [show (∫ z, f z ∂(decoder T γ α y)) = decoderFunctional T γ α y ⟨⟨f, hf⟩, hfc⟩ from h,
    decoderFunctional_of_mem hy]
  exact tendsto_nhds_limUnder (conv_of_mem T γ α hy ⟨⟨f, hf⟩, hfc⟩)


end ProfileDecoderDerived

/-- Derivation of `LQGMeasureOfProfileMeasurableFrozen`. The decoder
is the Riesz measure of the vague limit of the dyadic approximations on the convergence locus, and `0` elsewhere. -/
theorem lqgMeasureOfProfileMeasurable_derived : LQGMeasureOfProfileMeasurableFrozen.{u} := by
  intro Ω _ P _ γ α hC hcirc μ F hh hμ hFm hF
  obtain ⟨T⟩ := ProfileDecoderDerived.exists_testFamily
  have hagree : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2 :=
    IsWholePlaneGFF.ae_circle_map_eq_raw hh hF
  have h2 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (circleProfile (F ω))) (μ ω) :=
    (isLQGMeasureOfField_circleProfile_iff hagree γ α μ).1 hμ
  have hmem : ∀ᵐ ω ∂P, F ω ∈ ProfileDecoderDerived.convSet T γ α := by
    filter_upwards [h2] with ω hω
    intro m
    exact ⟨_, hω.tendsto_integral (T.D m) (T.D m).continuous (T.D m).hasCompactSupport⟩
  refine ⟨ProfileDecoderDerived.decoder T γ α, ProfileDecoderDerived.measurable_decoder T γ α, ?_, ?_⟩
  · filter_upwards [h2, hmem] with ω hω hωm
    exact IsLQGLimit.unique hω (ProfileDecoderDerived.isLQGLimit_decoder T γ α hωm)
  · have hae : ∀ᵐ y ∂(P.map F), y ∈ ProfileDecoderDerived.convSet T γ α :=
      (ae_map_iff hFm.aemeasurable (ProfileDecoderDerived.measurableSet_convSet T γ α)).2 hmem
    filter_upwards [hae] with y hy
    exact ProfileDecoderDerived.isLQGLimit_decoder T γ α hy

end HarmonicBalls
