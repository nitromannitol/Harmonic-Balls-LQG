import HarmonicBalls.Proofs.Sec5.PoleInfimumCharacterization
import Mathlib.Analysis.Convex.Continuous

/-! # Time dependence of general-domain least supersolutions

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
Assumptions at the pole use the enclosing-disc potential bound. -/

namespace HarmonicBalls

open MeasureTheory Metric Set Laplacian

/-- Convex combinations preserve the distributional Laplacian upper bound. -/
theorem LaplacianLE.convex_combination {w v : ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ}
    (hw : LaplacianLE w μ U) (hv : LaplacianLE v μ U)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    LaplacianLE (fun x => a * w x + b * v x) μ U := by
  refine ⟨(hw.1.smul a).add (hv.1.smul b), fun φ hφ hφ0 hφμ => ?_⟩
  have heq : (fun x => (a * w x + b * v x) * Δ φ x) =
      (fun x => a * (w x * Δ φ x) + b * (v x * Δ φ x)) := by
    funext x; ring
  rw [heq, integral_add ((integrable_mul_laplacian_of_test hw.1 hφ).const_mul a)
    ((integrable_mul_laplacian_of_test hv.1 hφ).const_mul b), integral_const_mul, integral_const_mul]
  have h1 := mul_le_mul_of_nonneg_left (hw.2 φ hφ hφ0 hφμ) ha
  have h2 := mul_le_mul_of_nonneg_left (hv.2 φ hφ hφ0 hφμ) hb
  calc
    _ ≤ a * (∫ x, φ x ∂μ) + b * (∫ x, φ x ∂μ) := add_le_add h1 h2
    _ = _ := by rw [← add_mul, hab, one_mul]

/-- Convex combinations of competitors match the interpolated time. -/
theorem convex_combination_mem_supersolutionsOn {μ : Measure ℂ} {U : Set ℂ} {z : ℂ}
    {s t a b : ℝ} {w v : ℂ → ℝ} (hw : w ∈ supersolutionsOn μ U z s)
    (hv : v ∈ supersolutionsOn μ U z t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    (fun x => a * w x + b * v x) ∈ supersolutionsOn μ U z (a * s + b * t) := by
  refine ⟨(continuousOn_const.mul hw.1).add (continuousOn_const.mul hv.1),
    hw.2.1.convex_combination hv.2.1 ha hb hab, ?_⟩
  intro x hx hxz
  have h1 := mul_le_mul_of_nonneg_left (hw.2.2 x hx hxz) ha
  have h2 := mul_le_mul_of_nonneg_left (hv.2.2 x hx hxz) hb
  nlinarith

/-- Infimum semantics on the closed domain, including the pole. -/
theorem isGLB_supersolutionsOn_values
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z x : ℂ} (hz : z ∈ U) (hx : x ∈ closure U) {t : ℝ} (ht : 0 ≤ t) :
    IsGLB ((fun w : ℂ → ℝ => w x) '' supersolutionsOn μ U z t)
      (leastSupersolutionOn μ U z t x) := by
  by_cases hxz : x = z
  · subst x; exact isGLB_supersolutionsOn_values_pole hμ hR hV hU hsub hz ht
  · exact isGLB_supersolutionsOn_values_of_ne_pole (isBounded_ball.subset hsub) ht hx hxz

/-- Increasing time enlarges the competitor class. -/
theorem supersolutionsOn_mono_time {μ : Measure ℂ} {U : Set ℂ}
    (hUb : Bornology.IsBounded U) {z : ℂ} {s t : ℝ} (hst : s ≤ t) :
    supersolutionsOn μ U z s ⊆ supersolutionsOn μ U z t := by
  intro w hw
  refine ⟨hw.1, hw.2.1, ?_⟩
  intro x hx hxz
  have hg := greenFunction_nonneg hUb z x
  have h := hw.2.2 x hx hxz
  nlinarith

/-- The least supersolution is antitone in nonnegative time, including at the pole. -/
theorem leastSupersolutionOn_antitone_time
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z x : ℂ} (hz : z ∈ U) (hx : x ∈ closure U) :
    AntitoneOn (fun t => leastSupersolutionOn μ U z t x) (Ici 0) := by
  intro s hs t ht hst
  apply (isGLB_supersolutionsOn_values hμ hR hV hU hsub hz hx hs).2
  rintro _ ⟨w, hw, rfl⟩
  exact (isGLB_supersolutionsOn_values hμ hR hV hU hsub hz hx ht).1
    ⟨w, supersolutionsOn_mono_time (isBounded_ball.subset hsub) hst hw, rfl⟩

/-- The least supersolution is convex in nonnegative time. -/
theorem leastSupersolutionOn_convex_time
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z x : ℂ} (hz : z ∈ U) (hx : x ∈ closure U) :
    ConvexOn ℝ (Ici 0) (fun t => leastSupersolutionOn μ U z t x) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro s hs t ht a b ha hb hab
  have habt : 0 ≤ a * s + b * t := add_nonneg (mul_nonneg ha hs) (mul_nonneg hb ht)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨w, hw, hwlt⟩ := exists_supersolutionOn_lt_of_leastSupersolutionOn_lt
    (isBounded_ball.subset hsub) hs (lt_add_of_pos_right _ hε)
  obtain ⟨v, hv, hvlt⟩ := exists_supersolutionOn_lt_of_leastSupersolutionOn_lt
    (isBounded_ball.subset hsub) ht (lt_add_of_pos_right _ hε)
  have h := (isGLB_supersolutionsOn_values hμ hR hV hU hsub hz hx habt).1
    ⟨_, convex_combination_mem_supersolutionsOn hw hv ha hb hab, rfl⟩
  change leastSupersolutionOn μ U z (a * s + b * t) x ≤
    a * leastSupersolutionOn μ U z s x + b * leastSupersolutionOn μ U z t x + ε
  have h1 := mul_le_mul_of_nonneg_left hwlt.le ha
  have h2 := mul_le_mul_of_nonneg_left hvlt.le hb
  have he : a * ε + b * ε = ε := by rw [← add_mul, hab, one_mul]
  linarith

/-- Local Lipschitz continuity holds at every positive time. -/
theorem leastSupersolutionOn_locallyLipschitz_time
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z x : ℂ} (hz : z ∈ U) (hx : x ∈ closure U) :
    LocallyLipschitzOn (Ioi 0) (fun t => leastSupersolutionOn μ U z t x) := by
  simpa only [interior_Ici] using
    (leastSupersolutionOn_convex_time hμ hR hV hU hsub hz hx).locallyLipschitzOn_interior

/-- On a positive compact time interval the time Lipschitz constant can be
chosen uniformly over the whole closed domain. -/
theorem leastSupersolutionOn_uniform_lipschitz_time
    {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {R βm βp : ℝ}
    (hR : 0 < R) (hV : VolumeGrowth μ R βm βp)
    {U : Set ℂ} (hU : IsOpen U) (hsub : U ⊆ ball (0 : ℂ) R)
    {z : ℂ} (hz : z ∈ U) {s T : ℝ} (hs : 0 < s) (_hsT : s ≤ T) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ closure U, ∀ u ∈ Icc s T, ∀ v ∈ Icc s T,
      |leastSupersolutionOn μ U z u x - leastSupersolutionOn μ U z v x| ≤ C * |u - v| := by
  have hUb : Bornology.IsBounded U := isBounded_ball.subset hsub
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).bddAbove_image
    (greenPotentialBall_continuousOn μ hμ R βm βp hR hV)
  let B := max M 0
  have hB : 0 ≤ B := le_max_right _ _
  have hcl : closure U ⊆ closedBall (0 : ℂ) R :=
    closure_minimal (hsub.trans ball_subset_closedBall) isClosed_closedBall
  have hbound : ∀ x ∈ closure U, ∀ t : ℝ, 0 ≤ t →
      |leastSupersolutionOn μ U z t x| ≤ B := by
    intro x hx t ht
    have hglb := isGLB_supersolutionsOn_values hμ hR hV hU hsub hz hx ht
    have hup : leastSupersolutionOn μ U z t x ≤ 0 :=
      hglb.1 ⟨0, zero_mem_supersolutionsOn hUb ht, rfl⟩
    rw [abs_of_nonpos hup]
    by_cases hxU : x ∈ U
    · have hlo : -greenPotentialBall μ R x ≤ leastSupersolutionOn μ U z t x := by
        apply hglb.2
        rintro _ ⟨w, hw, rfl⟩
        exact neg_greenPotentialBall_le_supersolutionOn hμ hR hV hU hsub hz hw hxU
      have hQ : greenPotentialBall μ R x ≤ B := (hM ⟨x, hcl hx, rfl⟩).trans (le_max_left _ _)
      linarith
    · have hxz : x ≠ z := fun h => hxU (h ▸ hz)
      rw [leastSupersolutionOn_eq_zero_of_boundary hUb ht hx hxU hxz]
      simpa using hB
  let C : NNReal := (2 * B / (s / 4)).toNNReal
  refine ⟨C, NNReal.coe_nonneg C, ?_⟩
  intro x hx u hu v hv
  have hball : ball ((s + T) / 2) (T / 2) ⊆ Ici (0 : ℝ) := by
    intro t ht
    rw [mem_ball, Real.dist_eq] at ht
    have := (abs_lt.mp ht).1
    change 0 ≤ t
    linarith
  have hconv := (leastSupersolutionOn_convex_time hμ hR hV hU hsub hz hx).subset
    hball (convex_ball _ _)
  have hlip : LipschitzOnWith C (fun t => leastSupersolutionOn μ U z t x)
      (ball ((s + T) / 2) (T / 2 - s / 4)) := by
    apply hconv.lipschitzOnWith_of_abs_le (by linarith : 0 < s / 4)
    intro t ht
    exact hbound x hx t (hball ht)
  have hu' : u ∈ ball ((s + T) / 2) (T / 2 - s / 4) := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    rcases hu with ⟨hu₁, hu₂⟩
    constructor <;> linarith
  have hv' : v ∈ ball ((s + T) / 2) (T / 2 - s / 4) := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    rcases hv with ⟨hv₁, hv₂⟩
    constructor <;> linarith
  simpa only [Real.dist_eq] using hlip.dist_le_mul u hu' v hv'

#print axioms leastSupersolutionOn_antitone_time
#print axioms leastSupersolutionOn_convex_time
#print axioms leastSupersolutionOn_locallyLipschitz_time
#print axioms leastSupersolutionOn_uniform_lipschitz_time

end HarmonicBalls
