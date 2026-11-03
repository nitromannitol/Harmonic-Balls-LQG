import HarmonicBalls.Proofs.Sec3.Basic

/-!
# Lemma A.6 with a general pole, and Lemma 3.5

Proofs of `ObstacleCompatibilityPoleStep1` and `ObstacleCompatibilityPoleStep2` (Steps/Sec3/ClusterCompatibility.lean).

* Harmonic functions have `Δ = 0` distributionally (`hasLaplacian_zero_of_harmonicOnNhd`, via the mean value property
  and the converse of Weyl's lemma), and `Δ ≤ μ` is local (`LaplacianLE.union`, a smooth cut-off).
* The removable singularity of `G_{B_{r₁}}(z,·) - G_{B_{r₂}}(z,·)` at the pole `z` (E32): off the pole it equals
  `h_z = h^{r₂}_z - h^{r₁}_z`, the difference of the explicit greatest harmonic minorants
  (`greatestHarmonicMinorantBall`), which is harmonic on a neighbourhood of `closedBall 0 r₁`.
* Step 1: `ŵ = v_{B_{r₂};z}(t) - t h_z ∈ S_{B_{r₁};z}(t)`, so `u_{B_{r₁};z}(t) ≤ u_{B_{r₂};z}(t)` (eq:monotonicity-domains).
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set Laplacian ComplexConjugate

universe u

/-! ## Harmonic functions and the distributional Laplacian -/

/-- A harmonic function on an open set has the mean value property on circles in it, so it is superharmonic. -/
theorem isSuperharmonicOn_of_harmonicOnNhd {f : ℂ → ℝ} {U : Set ℂ}
    (hf : InnerProductSpace.HarmonicOnNhd f U) : IsSuperharmonicOn U f := by
  have hfc : ContinuousOn f U := fun x hx => (hf x hx).1.continuousAt.continuousWithinAt
  refine ⟨hfc.lowerSemicontinuousOn, fun x hx r hr hsub => ?_⟩
  refine ⟨(hfc.mono (sphere_subset_closedBall.trans hsub)).circleIntegrable hr.le, ?_⟩
  rw [InnerProductSpace.HarmonicOnNhd.circleAverage_eq (hf.mono (by rw [abs_of_pos hr]; exact hsub))]

/-- A harmonic function on an open set has `Δ f = 0` there in the distributional sense. -/
theorem hasLaplacian_zero_of_harmonicOnNhd {f : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hf : InnerProductSpace.HarmonicOnNhd f U) : HasLaplacian f 0 0 U := by
  have hfc : ContinuousOn f U := fun x hx => (hf x hx).1.continuousAt.continuousWithinAt
  have hsup := isSuperharmonicOn_of_harmonicOnNhd hf
  have hsup' : IsSuperharmonicOn U (-f) := by
    refine ⟨hfc.neg.lowerSemicontinuousOn, fun x hx r hr hsub => ?_⟩
    obtain ⟨hi, -⟩ := hsup.2 x hx r hr hsub
    refine ⟨hi.neg, ?_⟩
    rw [circleAverage_neg_fun, Pi.neg_apply,
      InnerProductSpace.HarmonicOnNhd.circleAverage_eq (hf.mono (by rw [abs_of_pos hr]; exact hsub))]
  exact hasLaplacianOfLaplacianLEGEStep_holds U f hU
    (laplacianLEOfSuperharmonicStep_holds U f hU hfc hsup)
    (LaplacianGE.of_laplacianLE_neg (laplacianLEOfSuperharmonicStep_holds U (-f) hU hfc.neg hsup'))

/-- Adding a multiple of a function with `Δ h = 0` preserves `Δ w ≤ μ`. -/
theorem LaplacianLE.add_const_mul_of_hasLaplacian_zero {w h : ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ}
    (hw : LaplacianLE w μ U) (hh : HasLaplacian h 0 0 U) (c : ℝ) :
    LaplacianLE (fun x => w x + c * h x) μ U := by
  refine ⟨hw.1.add (MeasureTheory.LocallyIntegrableOn.smul hh.1 c), fun φ hφ hφ0 hφμ => ?_⟩
  have h0 := (hh.2 φ hφ).2.2
  rw [integral_zero_measure, sub_zero] at h0
  have e : (fun x => (w x + c * h x) * Δ φ x) = fun x => w x * Δ φ x + c * (h x * Δ φ x) := by
    funext x; ring
  rw [e, integral_add (integrable_mul_laplacian_of_test hw.1 hφ)
    ((integrable_mul_laplacian_of_test hh.1 hφ).const_mul c), integral_const_mul, h0, mul_zero, add_zero]
  exact hw.2 φ hφ hφ0 hφμ

/-- **`Δ w ≤ μ` is local**: on the union of two open sets it follows from the inequality on each (cut-off
`χ ∈ C_c^∞(U₁)`, `χ = 1` near `tsupport φ \ U₂`, and `φ = φχ + φ(1-χ)`). -/
theorem LaplacianLE.union {w : ℂ → ℝ} {μ : Measure ℂ} {U₁ U₂ : Set ℂ} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂)
    (h₁ : LaplacianLE w μ U₁) (h₂ : LaplacianLE w μ U₂) : LaplacianLE w μ (U₁ ∪ U₂) := by
  refine ⟨fun x hx => ?_, fun φ hφ hφ0 hφμ => ?_⟩
  · have hU := hU₁.union hU₂
    rcases hx with hx | hx
    · have := h₁.1 x hx
      rwa [nhdsWithin_eq_nhds.2 (hU₁.mem_nhds hx), ← nhdsWithin_eq_nhds.2 (hU.mem_nhds (Or.inl hx))] at this
    · have := h₂.1 x hx
      rwa [nhdsWithin_eq_nhds.2 (hU₂.mem_nhds hx), ← nhdsWithin_eq_nhds.2 (hU.mem_nhds (Or.inr hx))] at this
  obtain ⟨hφd, hφc, hφU⟩ := hφ
  set K := tsupport φ with hKdef
  have hK' : IsCompact (K \ U₂) := hφc.of_isClosed_subset (isClosed_tsupport φ |>.sdiff hU₂) sdiff_subset
  have hK'U : K \ U₂ ⊆ U₁ := fun x hx => (hφU hx.1).resolve_right hx.2
  obtain ⟨V, hVo, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK' hU₁ hK'U
  obtain ⟨χ, hχd, hχc, hχU, hχ01, hχ1⟩ := exists_cutoff_of_isCompact_subset_isOpen hVc hU₁ hVU
  set φ₁ : ℂ → ℝ := fun x => χ x * φ x with hφ₁
  set φ₂ : ℂ → ℝ := fun x => φ x - χ x * φ x with hφ₂
  have hφ₁t : IsTestFunction U₁ φ₁ :=
    ⟨hχd.mul hφd, hφc.mul_left, (tsupport_mul_subset_left).trans hχU⟩
  have hsupp₂ : Function.support φ₂ ⊆ K \ V := by
    intro x hx
    have hx' : φ x - χ x * φ x ≠ 0 := hx
    have hφx : φ x ≠ 0 := fun h => hx' (by rw [h]; ring)
    refine ⟨subset_tsupport _ hφx, fun hxV => hx' ?_⟩
    rw [hχ1 x (subset_closure hxV)]
    ring
  have hφ₂t : IsTestFunction U₂ φ₂ := by
    refine ⟨hφd.sub (hχd.mul hφd), ?_, ?_⟩
    · exact HasCompactSupport.intro (hφc.diff hVo) fun x hx => by
        by_contra h
        exact hx (hsupp₂ (Function.mem_support.2 h))
    · refine (closure_minimal hsupp₂ ((isClosed_tsupport φ).sdiff hVo)).trans fun x hx => ?_
      by_contra hxU
      exact hx.2 (hKV ⟨hx.1, hxU⟩)
  have hφ₁0 : 0 ≤ φ₁ := fun x => mul_nonneg (hχ01 x).1 (hφ0 x)
  have hφ₂0 : 0 ≤ φ₂ := fun x => by
    show 0 ≤ φ x - χ x * φ x
    calc (0 : ℝ) ≤ (1 - χ x) * φ x := mul_nonneg (sub_nonneg.2 (hχ01 x).2) (hφ0 x)
      _ = φ x - χ x * φ x := by ring
  have hφ₁μ : Integrable φ₁ μ := by
    refine (hφμ.bdd_mul (c := 1) hχd.continuous.aestronglyMeasurable ?_)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hχ01 x).1]
    exact (hχ01 x).2
  have hφ₂μ : Integrable φ₂ μ := hφμ.sub hφ₁μ
  have hsum : ∀ x, Δ φ x = Δ φ₁ x + Δ φ₂ x := by
    intro x
    have e : φ = fun y => φ₁ y + φ₂ y := by
      funext y
      simp only [hφ₁, hφ₂]
      ring
    rw [e]
    exact ContDiffAt.laplacian_add (hφ₁t.1.contDiffAt.of_le (by norm_cast))
      (hφ₂t.1.contDiffAt.of_le (by norm_cast))
  have i1 := integrable_mul_laplacian_of_test h₁.1 hφ₁t
  have i2 := integrable_mul_laplacian_of_test h₂.1 hφ₂t
  have e : (fun x => w x * Δ φ x) = fun x => w x * Δ φ₁ x + w x * Δ φ₂ x := by
    funext x; rw [hsum x]; ring
  have eφ : ∫ x, φ x ∂μ = ∫ x, φ₁ x ∂μ + ∫ x, φ₂ x ∂μ := by
    rw [← integral_add hφ₁μ hφ₂μ]
    congr 1
    funext x
    simp only [hφ₁, hφ₂]
    ring
  rw [e, integral_add i1 i2, eφ]
  exact add_le_add (h₁.2 φ₁ hφ₁t hφ₁0 hφ₁μ) (h₂.2 φ₂ hφ₂t hφ₂0 hφ₂μ)

/-! ## The removable singularity of `G_{B_{r₁}}(z,·) - G_{B_{r₂}}(z,·)` -/

/-- `G_{B_r}(z,·) = N(z,·) - h^r_z` on the closed ball off the pole (on `∂B_r` both sides vanish). -/
theorem greenFunction_ball_eq_sub_of_mem_closedBall {r : ℝ} {z y : ℂ} (hz : z ∈ ball (0 : ℂ) r)
    (hy : y ∈ closedBall (0 : ℂ) r) (hyz : y ≠ z) :
    greenFunction (ball 0 r) z y = newtonKernel z y - greatestHarmonicMinorantBall r z y := by
  by_cases hyb : y ∈ ball (0 : ℂ) r
  · exact greenFunction_ball_eq_sub hz hyb (Ne.symm hyz)
  · have hr : 0 < r := pos_of_mem_ball hz
    have hz' : ‖z‖ < r := mem_ball_zero_iff.1 hz
    have hy' : ‖y‖ = r := le_antisymm (mem_closedBall_zero_iff.1 hy) (not_lt.1 fun h => hyb (mem_ball_zero_iff.2 h))
    rw [greenFunction_ball_of_le_norm hy'.ge, ← newtonKernel_sub_greenBall hr (Ne.symm hyz)
      (norm_sub_conj_mul_pos hr hz' hy'.le).ne']
    have h1 := greenBall_nonneg hr hz'.le hy'.le
    have h2 := greenBall_nonpos hr hz'.le hy'.ge
    linarith

/-- The harmonic function `h_z = h^{r₂}_z - h^{r₁}_z` (`r₁ ≤ r₂`, `z ∈ B_{r₁}`). -/
noncomputable def greenBallDifference (r₁ r₂ : ℝ) (z y : ℂ) : ℝ :=
  greatestHarmonicMinorantBall r₂ z y - greatestHarmonicMinorantBall r₁ z y

theorem harmonicOnNhd_greenBallDifference {r₁ r₂ : ℝ} (hr₁₂ : r₁ ≤ r₂) {z : ℂ} (hz : z ∈ ball (0 : ℂ) r₁) :
    InnerProductSpace.HarmonicOnNhd (greenBallDifference r₁ r₂ z) (closedBall 0 r₁) := by
  intro y hy
  have hr₁ : 0 < r₁ := pos_of_mem_ball hz
  have hz' : ‖z‖ < r₁ := mem_ball_zero_iff.1 hz
  have hy' : ‖y‖ ≤ r₁ := mem_closedBall_zero_iff.1 hy
  exact (harmonicAt_greatestHarmonicMinorantBall (norm_pos_iff.1 (norm_sub_conj_mul_pos (hr₁.trans_le hr₁₂)
      (hz'.trans_le hr₁₂) (hy'.trans hr₁₂)))).sub
    (harmonicAt_greatestHarmonicMinorantBall (norm_pos_iff.1 (norm_sub_conj_mul_pos hr₁ hz' hy')))

/-- Off the pole, `G_{B_{r₁}}(z,·) - G_{B_{r₂}}(z,·) = h_z` on `closedBall 0 r₁` (`r₁ < r₂`). -/
theorem greenFunction_sub_eq_greenBallDifference {r₁ r₂ : ℝ} (hr₁₂ : r₁ < r₂) {z y : ℂ}
    (hz : z ∈ ball (0 : ℂ) r₁) (hy : y ∈ closedBall (0 : ℂ) r₁) (hyz : y ≠ z) :
    greenFunction (ball 0 r₁) z y - greenFunction (ball 0 r₂) z y = greenBallDifference r₁ r₂ z y := by
  rw [greenFunction_ball_eq_sub_of_mem_closedBall hz hy hyz,
    greenFunction_ball_eq_sub_of_mem_closedBall (ball_subset_ball hr₁₂.le hz)
      (closedBall_subset_closedBall hr₁₂.le hy) hyz, greenBallDifference]
  ring

/-! ## Step 1: monotonicity in the domain -/

/-- **Lemma A.6, Step 1 with a general pole** (`ObstacleCompatibilityPoleStep1`). -/
theorem obstacleCompatibilityPoleStep1_holds : ObstacleCompatibilityPoleStep1 := by
  intro μ hμ R βm βp hR hV t ht r₁ r₂ hr₁₂ hr₂R z hz x hx hxz
  rcases hr₁₂.lt_or_eq with hlt | heq
  swap
  · subst heq
    exact le_rfl
  have hr₂ : 0 < r₂ := (pos_of_mem_ball hz).trans hlt
  have hz₂ : z ∈ ball (0 : ℂ) r₂ := ball_subset_ball hlt.le hz
  obtain ⟨-, hvc, hvS⟩ := leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hr₂ (hV.mono hr₂R) hz₂ ht
  set v₂ := leastSupersolution μ r₂ z t with hv₂def
  set h := greenBallDifference r₁ r₂ z with hhdef
  have hharm := harmonicOnNhd_greenBallDifference hlt.le hz
  have hhc : ContinuousOn h (closedBall 0 r₁) := fun y hy => (hharm y hy).1.continuousAt.continuousWithinAt
  have hhL : HasLaplacian h 0 0 (ball 0 r₁) :=
    hasLaplacian_zero_of_harmonicOnNhd isOpen_ball (hharm.mono ball_subset_closedBall)
  set ŵ : ℂ → ℝ := fun y => v₂ y + (-t) * h y with hŵdef
  have hŵS : ŵ ∈ supersolutions μ r₁ z t := by
    refine ⟨(hvc.mono (closedBall_subset_closedBall hlt.le)).add (continuousOn_const.mul hhc),
      (hvS.2.1.mono_set (ball_subset_ball hlt.le)).add_const_mul_of_hasLaplacian_zero hhL (-t),
      fun y hy hyz => ?_⟩
    have h1 := hvS.2.2 y (closedBall_subset_closedBall hlt.le hy) hyz
    have h2 : greenFunction (ball 0 r₁) z y - greenFunction (ball 0 r₂) z y = h y :=
      greenFunction_sub_eq_greenBallDifference hlt hz hy hyz
    have e : t * h y = t * greenFunction (ball 0 r₁) z y - t * greenFunction (ball 0 r₂) z y := by
      rw [← h2]; ring
    show -t * greenFunction (ball 0 r₁) z y ≤ v₂ y + (-t) * h y
    linarith
  have hle := leastSupersolution_le hŵS (ball_subset_closedBall hx) hxz
  have h2 : greenFunction (ball 0 r₁) z x - greenFunction (ball 0 r₂) z x = h x :=
    greenFunction_sub_eq_greenBallDifference hlt hz (ball_subset_closedBall hx) hxz
  have e : t * h x = t * greenFunction (ball 0 r₁) z x - t * greenFunction (ball 0 r₂) z x := by
    rw [← h2]; ring
  simp only [odometer]
  show leastSupersolution μ r₁ z t x + t * greenFunction (ball 0 r₁) z x ≤
    v₂ x + t * greenFunction (ball 0 r₂) z x
  have : leastSupersolution μ r₁ z t x ≤ v₂ x + (-t) * h x := hle
  linarith

/-! ## Step 2: comparison with the glued odometer -/

/-- `-t G_{B_R}(z,·)` has `Δ = 0` (so `≤ μ`) on open subsets of `B_R` avoiding the pole. -/
theorem laplacianLE_neg_mul_greenFunction_of_notMem {μ : Measure ℂ} {R t : ℝ} {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) {U : Set ℂ} (hUR : U ⊆ ball 0 R) (hzU : z ∉ U) :
    LaplacianLE (fun y => -t * greenFunction (ball 0 R) z y) μ U := by
  have hR : 0 < R := pos_of_mem_ball hz
  have hG := ((greenFunctionBall R hR z hz).1)
  refine ⟨(MeasureTheory.LocallyIntegrableOn.smul (hG.1.mono_set hUR) (-t)), fun φ hφ hφ0 _ => ?_⟩
  have hφR : IsTestFunction (ball 0 R) φ := ⟨hφ.1, hφ.2.1, hφ.2.2.trans hUR⟩
  have h0 := (hG.2 φ hφR).2.2
  have hφz : φ z = 0 := image_eq_zero_of_notMem_tsupport fun h => hzU (hφ.2.2 h)
  rw [integral_zero_measure, integral_dirac, hφz, sub_zero] at h0
  have e : (fun y => -t * greenFunction (ball 0 R) z y * Δ φ y) =
      fun y => -t * (greenFunction (ball 0 R) z y * Δ φ y) := by
    funext y; ring
  rw [e, integral_const_mul, h0, mul_zero]
  exact integral_nonneg hφ0

/-- **Lemma A.6, Step 2 with a general pole** (`ObstacleCompatibilityPoleStep2`): the glued function
`ŵ = v_{B_{s₁};z}(t) + t h_z` on `B_{s₁}`, `-t G_{B_R}(z,·)` outside, is a supersolution on `B_R`, so
`u_{B_R;z}(t) ≤ ū` (`ū = u_{B_{s₁};z}(t)` on `B_{s₁}`, `0` outside). The printed proof's subharmonicity of
`u_{B_R;z}(t) - ū` on `Λ_{B_R;z}(t)` and the maximum principle are replaced by the minimality of
`v_{B_R;z}(t)`; the locality of `Δ ≤ μ` (`LaplacianLE.union`) covers the gluing along `B_{s₁} \ closure Λ_{B_{s₁};z}(t)`,
where both formulas agree. -/
theorem obstacleCompatibilityPoleStep2_holds : ObstacleCompatibilityPoleStep2 := by
  classical
  intro μ hμ R βm βp hR hV t ht s₁ s₂ hs₁₂ hs₂R z hz hcl
  have hs₁R : s₁ ≤ R := hs₁₂.trans hs₂R
  rcases hs₁R.lt_or_eq with hlt | heq
  swap
  · subst heq
    exact ⟨fun x _ _ => le_rfl, fun x hx hx' => absurd hx hx'⟩
  have hs₁ : 0 < s₁ := pos_of_mem_ball hz
  have hzR : z ∈ ball (0 : ℂ) R := ball_subset_ball hlt.le hz
  -- `Λ_{B_{s₁}} ⊆ Λ_{B_{s₂}}` (Step 1), so `closure Λ_{B_{s₁}} ⊂ B_{s₁}`
  have hsub₁₂ : cluster μ s₁ z t ⊆ cluster μ s₂ z t := by
    intro x hx
    rw [mem_cluster_iff] at hx ⊢
    by_cases hxz : x = z
    · exact ⟨ball_subset_ball hs₁₂ hx.1, Or.inl hxz⟩
    · exact ⟨ball_subset_ball hs₁₂ hx.1, Or.inr ((hx.2.resolve_left hxz).trans_le
        (obstacleCompatibilityPoleStep1_holds μ hμ R βm βp hR hV t ht s₁ s₂ hs₁₂ hs₂R z hz x hx.1 hxz))⟩
  have hcl₁ : closure (cluster μ s₁ z t) ⊆ ball 0 s₁ := (closure_mono hsub₁₂).trans hcl
  obtain ⟨-, hvc, hvS⟩ := leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ hs₁ (hV.mono hs₁R) hz ht
  set v₁ := leastSupersolution μ s₁ z t with hv₁def
  set h := greenBallDifference s₁ R z with hhdef
  have hharm := harmonicOnNhd_greenBallDifference hlt.le hz
  have hhc : ContinuousOn h (closedBall 0 s₁) := fun y hy => (hharm y hy).1.continuousAt.continuousWithinAt
  have hhL : HasLaplacian h 0 0 (ball 0 s₁) :=
    hasLaplacian_zero_of_harmonicOnNhd isOpen_ball (hharm.mono ball_subset_closedBall)
  set GR := greenFunction (ball (0 : ℂ) R) z with hGRdef
  set G₁ := greenFunction (ball (0 : ℂ) s₁) z with hG₁def
  have hdiff : ∀ y ∈ closedBall (0 : ℂ) s₁, y ≠ z → G₁ y - GR y = h y := fun y hy hyz =>
    greenFunction_sub_eq_greenBallDifference hlt hz hy hyz
  set O := (closure (cluster μ s₁ z t))ᶜ with hOdef
  have hOo : IsOpen O := isClosed_closure.isOpen_compl
  have hzO : z ∉ O := fun h => h (subset_closure ⟨hz, Or.inl rfl⟩)
  have hv₁O : ∀ y ∈ ball (0 : ℂ) s₁, y ∈ O → v₁ y = -t * G₁ y := by
    intro y hy hyO
    have hyz : y ≠ z := fun h => hzO (h ▸ hyO)
    have hyΛ : y ∉ cluster μ s₁ z t := fun h => hyO (subset_closure h)
    have h0 : 0 ≤ odometer μ s₁ z t y := odometer_nonneg ht.le (ball_subset_closedBall hy) hyz
    have hnot : ¬ (0 < odometer μ s₁ z t y) := fun hp => hyΛ (mem_cluster_iff.2 ⟨hy, Or.inr hp⟩)
    have h1 : odometer μ s₁ z t y = 0 := le_antisymm (not_lt.1 hnot) h0
    rw [odometer, ← hv₁def, ← hG₁def] at h1
    linarith
  set ŵ : ℂ → ℝ := fun y => if y ∈ ball (0 : ℂ) s₁ then v₁ y + t * h y else -t * GR y with hŵdef
  have hŵin : ∀ y ∈ ball (0 : ℂ) s₁, ŵ y = v₁ y + t * h y := fun y hy => by
    show (if y ∈ ball (0 : ℂ) s₁ then v₁ y + t * h y else -t * GR y) = _
    exact ite_eq_left_iff.2 fun hn => absurd hy hn
  have hŵout : ∀ y, y ∉ ball (0 : ℂ) s₁ → ŵ y = -t * GR y := fun y hy => by
    show (if y ∈ ball (0 : ℂ) s₁ then v₁ y + t * h y else -t * GR y) = _
    exact ite_eq_right_iff.2 fun hp => absurd hp hy
  have hŵO : ∀ y ∈ O, ŵ y = -t * GR y := by
    intro y hyO
    by_cases hy : y ∈ ball (0 : ℂ) s₁
    · have hyz : y ≠ z := fun h => hzO (h ▸ hyO)
      rw [hŵin y hy, hv₁O y hy hyO, ← hdiff y (ball_subset_closedBall hy) hyz]
      ring
    · exact hŵout y hy
  have hballO : ∀ y, y ∉ ball (0 : ℂ) s₁ → y ∈ O := fun y hy h => hy (hcl₁ h)
  have hGRc : ContinuousOn GR {z}ᶜ := continuousOn_greenFunction_ball hzR
  have hŵc : ContinuousOn ŵ (closedBall 0 R) := by
    intro x _
    by_cases hxs : x ∈ ball (0 : ℂ) s₁
    · have hev : ŵ =ᶠ[𝓝 x] fun y => v₁ y + t * h y := by
        filter_upwards [isOpen_ball.mem_nhds hxs] with y hy using hŵin y hy
      have hn : closedBall (0 : ℂ) s₁ ∈ 𝓝 x := mem_of_superset (isOpen_ball.mem_nhds hxs) ball_subset_closedBall
      have hc : ContinuousAt (fun y => v₁ y + t * h y) x :=
        (hvc.continuousAt hn).add (continuousAt_const.mul (hhc.continuousAt hn))
      exact (hc.congr hev.symm).continuousWithinAt
    · have hxO := hballO x hxs
      have hxz : x ≠ z := fun h => hxs (h ▸ hz)
      have hev : ŵ =ᶠ[𝓝 x] fun y => -t * GR y := by
        filter_upwards [hOo.mem_nhds hxO] with y hy using hŵO y hy
      have hc : ContinuousAt (fun y => -t * GR y) x :=
        continuousAt_const.mul (hGRc.continuousAt (isOpen_compl_singleton.mem_nhds hxz))
      exact (hc.congr hev.symm).continuousWithinAt
  have hL₁ : LaplacianLE ŵ μ (ball 0 s₁) :=
    (hvS.2.1.add_const_mul_of_hasLaplacian_zero hhL t).congr_eqOn measurableSet_ball
      fun y hy => (hŵin y hy).symm
  have hL₂ : LaplacianLE ŵ μ (ball 0 R ∩ O) :=
    (laplacianLE_neg_mul_greenFunction_of_notMem (t := t) hzR inter_subset_left
      fun h => hzO h.2).congr_eqOn (measurableSet_ball.inter hOo.measurableSet) fun y hy => (hŵO y hy.2).symm
  have hunion : ball (0 : ℂ) s₁ ∪ (ball 0 R ∩ O) = ball 0 R := by
    ext y
    constructor
    · rintro (hy | hy)
      · exact ball_subset_ball hlt.le hy
      · exact hy.1
    · intro hy
      by_cases hys : y ∈ ball (0 : ℂ) s₁
      · exact Or.inl hys
      · exact Or.inr ⟨hy, hballO y hys⟩
  have hL : LaplacianLE ŵ μ (ball 0 R) :=
    hunion ▸ LaplacianLE.union isOpen_ball (isOpen_ball.inter hOo) hL₁ hL₂
  have hŵS : ŵ ∈ supersolutions μ R z t := by
    refine ⟨hŵc, hL, fun y _ hyz => ?_⟩
    show -t * GR y ≤ ŵ y
    by_cases hys : y ∈ ball (0 : ℂ) s₁
    · rw [hŵin y hys]
      have h0 : 0 ≤ odometer μ s₁ z t y := odometer_nonneg ht.le (ball_subset_closedBall hys) hyz
      rw [odometer, ← hv₁def, ← hG₁def] at h0
      have e : t * h y = t * G₁ y - t * GR y := by rw [← hdiff y (ball_subset_closedBall hys) hyz]; ring
      linarith
    · rw [hŵout y hys]
  refine ⟨fun x hx hxz => ?_, fun x hx hxs => ?_⟩
  · have hle := leastSupersolution_le hŵS (ball_subset_closedBall (ball_subset_ball hlt.le hx)) hxz
    rw [hŵin x hx] at hle
    have e : t * h x = t * G₁ x - t * GR x := by rw [← hdiff x (ball_subset_closedBall hx) hxz]; ring
    rw [odometer, odometer, ← hv₁def, ← hG₁def, ← hGRdef]
    linarith
  · have hxz : x ≠ z := fun h => hxs (h ▸ hz)
    have hle := leastSupersolution_le hŵS (ball_subset_closedBall hx) hxz
    rw [hŵout x hxs] at hle
    rw [odometer, ← hGRdef]
    linarith

/-- **Lemma A.6 with a general pole.** -/
theorem obstacleCompatibilityGeneral_holds : ObstacleCompatibilityGeneral :=
  obstacleCompatibilityGeneral_of_steps obstacleCompatibilityPoleStep1_holds obstacleCompatibilityPoleStep2_holds

/-- **Lemma A.6** (lemma:appendix-cluster-compatibility, line 3851) as printed (pole `0`, [C14]). -/
theorem obstacleCompatibility_holds : ObstacleCompatibilityStmt :=
  obstacleCompatibility_of_general obstacleCompatibilityGeneral_holds

/-- **Lemma 3.5** (lemma:cluster-compatibility, line 657, [C14]), given Input I2. -/
theorem clusterCompatibility_proved (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) : ClusterCompatibilityStmt.{u} :=
  clusterCompatibility_of_steps hI2 obstacleCompatibilityPoleStep1_holds obstacleCompatibilityPoleStep2_holds

end HarmonicBalls
