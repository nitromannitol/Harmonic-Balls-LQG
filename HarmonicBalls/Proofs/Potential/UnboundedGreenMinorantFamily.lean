import HarmonicBalls.Proofs.Potential.FiniteDiscGreenReciprocity
import HarmonicBalls.Proofs.Potential.UnboundedGreenMinorantHarmonic

/-! # Joint regularity of Green minorants

The pole-shift argument from `FiniteDiscGreenReciprocity` yields joint
continuity on an open domain when each pole has a real harmonic minorant.
-/

namespace HarmonicBalls

open Set Metric Filter InnerProductSpace
open scoped Topology

/-- The harmonic correction has the same pole-shift bound as the
regularized Newtonian kernel, when the regularization discs lie in the domain. -/
theorem greenHarmonicCorrection_pole_shift_le_of_exists
    {U : Set ℂ} (hU : IsOpen U)
    (hex : ∀ z ∈ U, ∃ h : ℂ → ℝ, IsHarmonicMinorant U (newtonKernelEReal z) h)
    {ε : ℝ} (hε : 0 < ε) {z z' y : ℂ} (hy : y ∈ U)
    (hz : closedBall z (2 * ε) ⊆ U) (hz' : closedBall z' (2 * ε) ⊆ U) :
    (greatestHarmonicMinorant U (newtonKernelEReal z') y).toReal -
      (greatestHarmonicMinorant U (newtonKernelEReal z) y).toReal ≤
      (2 * Real.pi)⁻¹ * Real.log (1 + ‖z - z'‖ / ε) := by
  have hzU : z ∈ U := hz (mem_closedBall_self (by positivity))
  have hz'U : z' ∈ U := hz' (mem_closedBall_self (by positivity))
  let H : ℂ → ℂ → ℝ := fun x w =>
    (greatestHarmonicMinorant U (newtonKernelEReal x) w).toReal
  have hreg (x : ℂ) (hx : closedBall x (2 * ε) ⊆ U) (w : ℂ) (hw : w ∈ U) :
      H x w ≤ regularizedNewtonKernel ε x w := by
    have hub : greatestHarmonicMinorant U (newtonKernelEReal x) w ≤
        (regularizedNewtonKernel ε x w : EReal) := by
      rw [greatestHarmonicMinorant_regularized hε hx]
      exact greatestHarmonicMinorant_le hw
    obtain ⟨h, hh⟩ := hex x (hx (mem_closedBall_self (by positivity)))
    have hlb := hh.le_greatestHarmonicMinorant w
    have hb : greatestHarmonicMinorant U (newtonKernelEReal x) w ≠ ⊥ :=
      ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlb
    exact EReal.toReal_le_toReal hub hb (EReal.coe_ne_top _)
  let C : ℝ := (2 * Real.pi)⁻¹ * Real.log (1 + ‖z - z'‖ / ε)
  let q : ℂ → ℝ := fun w => H z' w - C
  have hq : IsHarmonicMinorant U (newtonKernelEReal z) q := by
    apply (isHarmonicMinorant_regularized_iff hε hz).2
    constructor
    · exact (harmonicOnNhd_greatestHarmonicMinorant_newtonKernel_of_exists hU hz'U (hex z' hz'U)).sub
        (InnerProductSpace.harmonicOnNhd_const C)
    · intro w hw
      change ((H z' w - C : ℝ) : EReal) ≤ (regularizedNewtonKernel ε z w : EReal)
      rw [EReal.coe_le_coe_iff]
      have hshift := regularizedNewtonKernel_sub_le hε z z' w
      have hbound := hreg z' hz' w hw
      dsimp [C] at *
      linarith
  have hlower := hq.le_greatestHarmonicMinorant y
  have hupper : greatestHarmonicMinorant U (newtonKernelEReal z) y ≤
      (regularizedNewtonKernel ε z y : EReal) := by
    rw [greatestHarmonicMinorant_regularized hε hz]
    exact greatestHarmonicMinorant_le hy
  have hreal := EReal.toReal_le_toReal hlower (EReal.coe_ne_bot _)
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) hupper)
  simp only [EReal.toReal_coe] at hreal
  change H z' y - H z y ≤ C
  dsimp [q] at hreal
  linarith

/-- For a fixed observation point in an open set, the harmonic
correction is continuous in the pole. This does not use reciprocity. -/
theorem continuousAt_greenHarmonicCorrection_pole_of_exists
    {U : Set ℂ} (hU : IsOpen U)
    (hex : ∀ z ∈ U, ∃ h : ℂ → ℝ, IsHarmonicMinorant U (newtonKernelEReal z) h)
    {z y : ℂ} (hz : z ∈ U) (hy : y ∈ U) :
    ContinuousAt (fun x => (greatestHarmonicMinorant U (newtonKernelEReal x) y).toReal) z := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hz
  let ε : ℝ := δ / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hzball : closedBall z (2 * ε) ⊆ U :=
    (closedBall_subset_ball (by dsimp [ε]; linarith)).trans hδU
  have hnear : ∀ x ∈ ball z (δ / 4), closedBall x (2 * ε) ⊆ U := by
    intro x hx w hw
    apply hδU
    rw [mem_ball] at hx ⊢
    rw [mem_closedBall] at hw
    have ht := dist_triangle w x z
    dsimp [ε] at hw
    linarith
  let C : ℂ → ℝ := fun x => (2 * Real.pi)⁻¹ * Real.log (1 + ‖z - x‖ / ε)
  have hC : ContinuousAt C z := by
    dsimp [C]
    fun_prop (disch := simp)
  have hCz : C z = 0 := by simp [C]
  rw [Metric.continuousAt_iff]
  intro η hη
  obtain ⟨κ, hκ, hκC⟩ := Metric.continuousAt_iff.mp hC η hη
  refine ⟨min κ (δ / 4), lt_min hκ (by positivity), ?_⟩
  intro x hx
  have hxball : x ∈ ball z (δ / 4) := mem_ball.mpr (lt_of_lt_of_le hx (min_le_right _ _))
  have hsmall := hκC (lt_of_lt_of_le hx (min_le_left _ _))
  rw [hCz, dist_zero_right] at hsmall
  have h1 := greenHarmonicCorrection_pole_shift_le_of_exists hU hex hε hy hzball (hnear x hxball)
  have h2 := greenHarmonicCorrection_pole_shift_le_of_exists hU hex hε hy (hnear x hxball) hzball
  rw [norm_sub_rev] at h2
  change _ ≤ C x at h1 h2
  rw [Real.dist_eq]
  have hsmall' : C x < η := lt_of_le_of_lt (le_abs_self (C x)) (by simpa only [Real.norm_eq_abs] using hsmall)
  exact lt_of_le_of_lt (abs_le.mpr ⟨by linarith, h1⟩) hsmall'

/-- The harmonic correction is jointly continuous in the pole and the
observation point throughout an open domain. -/
theorem continuousAt_greenHarmonicCorrection_uncurry_of_exists
    {U : Set ℂ} (hU : IsOpen U)
    (hex : ∀ z ∈ U, ∃ h : ℂ → ℝ, IsHarmonicMinorant U (newtonKernelEReal z) h)
    {z y : ℂ} (hz : z ∈ U) (hy : y ∈ U) :
    ContinuousAt (fun p : ℂ × ℂ =>
      (greatestHarmonicMinorant U (newtonKernelEReal p.1) p.2).toReal) (z, y) := by
  obtain ⟨δ, hδ, hδU⟩ := Metric.isOpen_iff.mp hU z hz
  let ε : ℝ := δ / 8
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hzball : closedBall z (2 * ε) ⊆ U :=
    (closedBall_subset_ball (by dsimp [ε]; linarith)).trans hδU
  have hnear : ∀ x ∈ ball z (δ / 4), closedBall x (2 * ε) ⊆ U := by
    intro x hx w hw
    apply hδU
    rw [mem_ball] at hx ⊢
    rw [mem_closedBall] at hw
    have ht := dist_triangle w x z
    dsimp [ε] at hw
    linarith
  let H : ℂ → ℂ → ℝ := fun x w =>
    (greatestHarmonicMinorant U (newtonKernelEReal x) w).toReal
  let C : ℂ → ℝ := fun x => (2 * Real.pi)⁻¹ * Real.log (1 + ‖z - x‖ / ε)
  have hC : ContinuousAt C z := by
    dsimp [C]
    fun_prop (disch := simp)
  have hCz : C z = 0 := by simp [C]
  have hCt : Tendsto (fun p : ℂ × ℂ => C p.1) (𝓝 (z, y)) (𝓝 0) := by
    simpa only [hCz, Function.comp_def] using hC.tendsto.comp (continuous_fst : Continuous (fun p : ℂ × ℂ => p.1)).continuousAt.tendsto
  have hbound : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, y), ‖H p.1 p.2 - H z p.2‖ ≤ C p.1 := by
    have hfirst : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, y), p.1 ∈ ball z (δ / 4) :=
      continuous_fst.continuousAt (isOpen_ball.mem_nhds (mem_ball_self (by positivity)))
    have hsecond : ∀ᶠ p : ℂ × ℂ in 𝓝 (z, y), p.2 ∈ U :=
      continuous_snd.continuousAt (hU.mem_nhds hy)
    filter_upwards [hfirst, hsecond] with p hp hpU
    have h1 := greenHarmonicCorrection_pole_shift_le_of_exists hU hex hε hpU hzball (hnear p.1 hp)
    have h2 := greenHarmonicCorrection_pole_shift_le_of_exists hU hex hε hpU (hnear p.1 hp) hzball
    rw [norm_sub_rev] at h2
    change H p.1 p.2 - H z p.2 ≤ C p.1 at h1
    change H z p.2 - H p.1 p.2 ≤ C p.1 at h2
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith, h1⟩
  have hdiff : Tendsto (fun p : ℂ × ℂ => H p.1 p.2 - H z p.2)
      (𝓝 (z, y)) (𝓝 0) := squeeze_zero_norm' hbound hCt
  have hobs : Tendsto (fun p : ℂ × ℂ => H z p.2)
      (𝓝 (z, y)) (𝓝 (H z y)) :=
    ((harmonicOnNhd_greatestHarmonicMinorant_newtonKernel_of_exists hU hz (hex z hz) y hy).1.continuousAt).tendsto.comp
      continuous_snd.continuousAt
  have hsum := hdiff.add hobs
  change Tendsto (fun p : ℂ × ℂ => H p.1 p.2) (𝓝 (z, y)) (𝓝 (H z y))
  simpa only [zero_add, sub_add_cancel] using hsum


/-- The greatest minorant is continuous jointly on the product of the domain
with itself. -/
theorem continuousOn_greenHarmonicCorrection_uncurry_of_exists
    {U : Set ℂ} (hU : IsOpen U)
    (hex : ∀ z ∈ U, ∃ h : ℂ → ℝ, IsHarmonicMinorant U (newtonKernelEReal z) h) :
    ContinuousOn (fun p : ℂ × ℂ =>
      (greatestHarmonicMinorant U (newtonKernelEReal p.1) p.2).toReal) (U ×ˢ U) := by
  intro p hp
  exact (continuousAt_greenHarmonicCorrection_uncurry_of_exists hU hex hp.1 hp.2).continuousWithinAt

/-- A compact set of poles admits a jointly measurable harmonic family with
uniform bounds on compact sets of observations. -/
theorem exists_measurable_harmonic_minorant_family_of_exists
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hex : ∀ z ∈ U, ∃ h : ℂ → ℝ, IsHarmonicMinorant U (newtonKernelEReal z) h) :
    ∃ F : ℂ → ℂ → ℝ, Measurable (Function.uncurry F) ∧
      (∀ z, HarmonicOnNhd (F z) U) ∧
      (∀ L : Set ℂ, IsCompact L → L ⊆ U →
        ∃ C : ℝ, ∀ z, ∀ x ∈ L, |F z x| ≤ C) ∧
      ∀ z ∈ K, ∀ x ∈ U,
        (greatestHarmonicMinorant U (newtonKernelEReal z) x).toReal = F z x := by
  classical
  let H : ℂ × ℂ → ℝ := fun p =>
    (greatestHarmonicMinorant U (newtonKernelEReal p.1) p.2).toReal
  let F : ℂ → ℂ → ℝ := fun z x => if z ∈ K ∧ x ∈ U then H (z, x) else 0
  have hcont : ContinuousOn H (U ×ˢ U) :=
    continuousOn_greenHarmonicCorrection_uncurry_of_exists hU hex
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · have hmeas : Measurable ((K ×ˢ U).piecewise H (fun _ => 0)) :=
      (hcont.mono (Set.prod_mono hKU (Subset.rfl))).measurable_piecewise
        continuousOn_const (hK.measurableSet.prod hU.measurableSet)
    convert hmeas using 1
    funext p
    simp [F, Set.piecewise, Function.uncurry, Set.mem_prod]
  · intro z
    by_cases hz : z ∈ K
    · have hzU := hKU hz
      have hh := harmonicOnNhd_greatestHarmonicMinorant_newtonKernel_of_exists hU hzU (hex z hzU)
      intro x hx
      apply (harmonicAt_congr_nhds ?_).2 (hh x hx)
      filter_upwards [hU.mem_nhds hx] with w hw
      simp [F, H, hz, hw]
    · simp [F, hz]
  · intro L hL hLU
    obtain ⟨C, hC⟩ := (hK.prod hL).exists_bound_of_continuousOn
      (hcont.mono (Set.prod_mono hKU hLU))
    refine ⟨max C 0, ?_⟩
    intro z x hx
    by_cases hz : z ∈ K
    · simpa [F, H, hz, hLU hx, Real.norm_eq_abs] using
        (hC (z, x) ⟨hz, hx⟩).trans (le_max_left C 0)
    · simp [F, hz]
  · intro z hz x hx
    simp [F, H, hz, hx]

/-- Existence of a Newtonian harmonic minorant at one interior pole implies
existence at every interior pole of an open set. -/
theorem exists_harmonicMinorant_newtonKernel_of_exists_at_pole
    {U : Set ℂ} (hU : IsOpen U) {z z' : ℂ} (hz : z ∈ U) (hz' : z' ∈ U)
    (hex : ∃ h : ℂ → ℝ, IsHarmonicMinorant U (newtonKernelEReal z) h) :
    ∃ h : ℂ → ℝ, IsHarmonicMinorant U (newtonKernelEReal z') h := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU z hz
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.mp hU z' hz'
  let ε : ℝ := min r s / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hball : closedBall z (2 * ε) ⊆ U := by
    apply (closedBall_subset_ball ?_).trans hrU
    dsimp [ε]
    have := min_le_left r s
    linarith
  have hball' : closedBall z' (2 * ε) ⊆ U := by
    apply (closedBall_subset_ball ?_).trans hsU
    dsimp [ε]
    have := min_le_right r s
    linarith
  obtain ⟨h, hh⟩ := hex
  have hreg := (isHarmonicMinorant_regularized_iff hε hball).1 hh
  refine ⟨fun w => h w - (2 * Real.pi)⁻¹ * Real.log (1 + ‖z' - z‖ / ε),
    (isHarmonicMinorant_regularized_iff hε hball').2 ⟨fun w hw =>
      (hreg.1 w hw).sub (harmonicAt_const _), fun w hw => ?_⟩⟩
  have h1 := EReal.coe_le_coe_iff.1 (hreg.2 w hw)
  have h2 := regularizedNewtonKernel_sub_le hε z' z w
  exact EReal.coe_le_coe_iff.2 (by linarith)

/-- The literal real-valued greatest-minorant correction is jointly
continuous on every open domain. -/
theorem continuousOn_greenHarmonicCorrection_uncurry
    {U : Set ℂ} (hU : IsOpen U) :
    ContinuousOn (fun p : ℂ × ℂ =>
      (greatestHarmonicMinorant U (newtonKernelEReal p.1) p.2).toReal) (U ×ˢ U) := by
  classical
  by_cases hex : ∃ z ∈ U, ∃ h : ℂ → ℝ, IsHarmonicMinorant U (newtonKernelEReal z) h
  · obtain ⟨z, hz, h⟩ := hex
    exact continuousOn_greenHarmonicCorrection_uncurry_of_exists hU
      (fun z' hz' => exists_harmonicMinorant_newtonKernel_of_exists_at_pole hU hz hz' h)
  · have hzero : ∀ p ∈ U ×ˢ U,
        (greatestHarmonicMinorant U (newtonKernelEReal p.1) p.2).toReal = 0 := by
      intro p hp
      have hnone : ¬∃ h : ℂ → ℝ, IsHarmonicMinorant U (newtonKernelEReal p.1) h :=
        fun h => hex ⟨p.1, hp.1, h⟩
      have hnone' : ∀ h, ¬IsHarmonicMinorant U (newtonKernelEReal p.1) h :=
        fun h hh => hnone ⟨h, hh⟩
      simp [greatestHarmonicMinorant, hnone']
    exact continuousOn_const.congr (fun p hp => hzero p hp)

/-- A jointly measurable, locally bounded harmonic family represents the
literal correction on a compact set of poles in any open domain. -/
theorem exists_measurable_harmonic_minorant_family
    {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ F : ℂ → ℂ → ℝ,
      Measurable (Function.uncurry F) ∧
      (∀ z, HarmonicOnNhd (F z) U) ∧
      (∀ L, IsCompact L → L ⊆ U → ∃ C : ℝ, ∀ z x, x ∈ L → |F z x| ≤ C) ∧
      ∀ z ∈ K, ∀ x ∈ U,
        (greatestHarmonicMinorant U (newtonKernelEReal z) x).toReal = F z x := by
  classical
  by_cases hex : ∃ z ∈ U, ∃ h : ℂ → ℝ, IsHarmonicMinorant U (newtonKernelEReal z) h
  · obtain ⟨z, hz, h⟩ := hex
    exact exists_measurable_harmonic_minorant_family_of_exists hU hK hKU
      (fun z' hz' => exists_harmonicMinorant_newtonKernel_of_exists_at_pole hU hz hz' h)
  · refine ⟨fun _ _ => 0, measurable_const, fun _ => harmonicOnNhd_const 0,
      fun _ _ _ => ⟨0, by simp⟩, ?_⟩
    intro z hz x hx
    have hnone : ¬∃ h : ℂ → ℝ, IsHarmonicMinorant U (newtonKernelEReal z) h :=
      fun h => hex ⟨z, hKU hz, h⟩
    have hnone' : ∀ h, ¬IsHarmonicMinorant U (newtonKernelEReal z) h :=
      fun h hh => hnone ⟨h, hh⟩
    simp [greatestHarmonicMinorant, hnone']

end HarmonicBalls
