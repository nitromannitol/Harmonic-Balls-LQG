import HarmonicBalls.Defs.HarmonicBall
import HarmonicBalls.Proofs.Potential.GreenPositivity

/-!
# The test class of Theorem 1.1 as printed admits no bounded harmonic ball (correction C7)

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795), lines 136-146 and
Theorem 1.1 (theorem:harmonic-balls, line 152). The preserved arXiv source (`paper/lqg_harmonic_ball.tex`,
line 146) defines a harmonic ball `Λ(z)` by the mean value property eq:harmonic-ball for all `f = f₁ + f₂` with
`f₁` harmonic in a neighbourhood of `closure Λ(z)` and `f₂ ∈ H̃_O(Λ(z))` "for some `O` with `Λ(z) ⊂ Ō`", where
`O` is a bounded open set (line 142). This file formalizes that *published* class
(`publishedHarmonicBallTestClass`, `IsPublishedHarmonicBall`) and proves that, for every measure `μ` charging
nonempty open sets (Lebesgue measure; `μ_h` almost surely), no bounded open set is a harmonic ball for it
(`not_isPublishedHarmonicBall`). Since Theorem 1.1(b) (line 157) asserts that the harmonic balls `Λ_t(z)` are bounded,
Theorem 1.1 as printed is false. The corrected class (`harmonicBallTestClass`, `Defs/HarmonicBall.lean`) requires
`closure Λ ⊆ O` (correction C7).

## The construction ([C7])

Let `Λ` be bounded open and `z ∈ Λ`. Choose `ε > 0` with `closedBall z ε ⊆ Λ` and let
`S = closedBall z ε ∩ {w | w.im = z.im}` be the horizontal slit of length `2ε` centered at `z`. Choose `R` with
`closure Λ ⊆ B_R(0)` and set `O = B_R(0) \ S`, a bounded open set. The slit has empty interior, so `Λ ⊆ B_R ⊆ Ō`.
Pick `y ∈ ∂Λ` (nonempty: `Λ` is a nonempty bounded open subset of the connected plane). Then `y ∈ O \ Λ`, so
`f₂ = G_O(·, y) ∈ H̃_O(Λ)` (`greenFunction_mem_greenPotentialClass`, `ν = δ_y`). Now `f₂(z) = 0` since
`z ∈ S ⊆ ∂O`, whereas `f₂ > 0` on `B_r(y) \ {y}` for small `r` (`greenFunction_pos`) and `B_r(y) ∩ Λ` is a nonempty
open set, so `∫_Λ f₂ dμ > 0 = f₂(z) μ(Λ)`.

## The value `f₂(z) = 0` is not a junk value

In Lean `greenFunction O z y = 0` holds because `z ∉ O` (a junk-value convention of `Defs/Green.lean`). The slit is
chosen so that this is also the true value: a segment is non-polar, so every point of `S` is a regular boundary point
of `O` and `G_O(·, y)` extends continuously by `0` to `S`. (A single point `S = {z}` would *not* do: it is polar,
`G_{B_R \ {z}} = G_{B_R}` off `z`, and the Lean value `0` at `z` would be a junk value.)
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace

/-- The class of test functions of lines 143-146 *as printed* (`paper/lqg_harmonic_ball.tex`, line 146):
`f = f₁ + f₂` with `f₁` harmonic in a neighbourhood of `closure Λ` and `f₂ ∈ H̃_O(Λ)` for some bounded open `O`
(line 142) with `Λ ⊆ closure O`. It contains the corrected class `harmonicBallTestClass Λ`
(`harmonicBallTestClass_subset_published`); it is too large (`not_isPublishedHarmonicBall`). -/
def publishedHarmonicBallTestClass (Λ : Set ℂ) : Set (ℂ → ℝ) :=
  {f | ∃ (f₁ f₂ : ℂ → ℝ) (O : Set ℂ), HarmonicOnNhd f₁ (closure Λ) ∧ IsOpen O ∧ Bornology.IsBounded O ∧
    Λ ⊆ closure O ∧ f₂ ∈ greenPotentialClass O Λ ∧ f = f₁ + f₂}

/-- `Λ` is a *harmonic ball for `μ` centered at `z` in the sense printed at lines 143-146*: `Λ` is a harmonic ball
(eq:harmonic-ball) and every `f ∈ publishedHarmonicBallTestClass Λ` has the mean value property on `Λ` at `z`. This
is `IsHarmonicBallGen` with the published test class in place of the corrected one. -/
def IsPublishedHarmonicBall (μ : Measure ℂ) (Λ : Set ℂ) (z : ℂ) : Prop :=
  IsHarmonicBall μ Λ z ∧ ∀ f ∈ publishedHarmonicBallTestClass Λ, HasMeanValueProperty μ Λ z f

/-- The corrected class is contained in the published one (`closure Λ ⊆ O` implies `Λ ⊆ closure O`). -/
theorem harmonicBallTestClass_subset_published (Λ : Set ℂ) :
    harmonicBallTestClass Λ ⊆ publishedHarmonicBallTestClass Λ := by
  rintro f ⟨f₁, f₂, O, hf₁, hO, hOb, hΛO, hf₂, rfl⟩
  exact ⟨f₁, f₂, O, hf₁, hO, hOb, (subset_closure.trans hΛO).trans subset_closure, hf₂, rfl⟩

/-- A published harmonic ball is a harmonic ball in the corrected sense of Theorem 1.1. -/
theorem IsPublishedHarmonicBall.isHarmonicBallGen {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ}
    (h : IsPublishedHarmonicBall μ Λ z) : IsHarmonicBallGen μ Λ z :=
  ⟨h.1, fun f hf => h.2 f (harmonicBallTestClass_subset_published Λ hf)⟩

/-- *The published test class is too large.* Let `μ` charge every nonempty open set, let `Λ` be a bounded open set
and `z ∈ Λ`. Then some `f ∈ publishedHarmonicBallTestClass Λ` (namely `f = G_O(·, y)` with `O = B_R(0) \ S` for a
slit `S ∋ z` and `y ∈ ∂Λ`, see the module docstring) fails the mean value property on `Λ` at `z`. -/
theorem exists_not_hasMeanValueProperty_published {μ : Measure ℂ} [μ.IsOpenPosMeasure] {Λ : Set ℂ}
    (hΛo : IsOpen Λ) (hΛb : Bornology.IsBounded Λ) {z : ℂ} (hz : z ∈ Λ) :
    ∃ f ∈ publishedHarmonicBallTestClass Λ, ¬ HasMeanValueProperty μ Λ z f := by
  -- the slit `S` through `z`
  obtain ⟨δ, hδ, hδΛ⟩ := Metric.isOpen_iff.1 hΛo z hz
  set ε := δ / 2 with hε_def
  have hε : 0 < ε := by positivity
  have hεΛ : closedBall z ε ⊆ Λ := (closedBall_subset_ball (by linarith)).trans hδΛ
  set S : Set ℂ := closedBall z ε ∩ {w | w.im = z.im} with hS_def
  have hzS : z ∈ S := ⟨mem_closedBall_self hε.le, rfl⟩
  have hSclosed : IsClosed S := isClosed_closedBall.inter (isClosed_eq Complex.continuous_im continuous_const)
  have hSdense : Dense Sᶜ := by
    refine Dense.mono ?_ ((dense_compl_singleton z.im).preimage Complex.isOpenMap_im)
    intro w hw hwS
    exact hw hwS.2
  -- a boundary point `y` of `Λ`
  have hne : Λ ≠ univ := fun h => NormedSpace.unbounded_univ ℝ ℂ (h ▸ hΛb)
  obtain ⟨y, hy⟩ := nonempty_frontier_iff.2 ⟨⟨z, hz⟩, hne⟩
  have hyΛ : y ∉ Λ := by
    rw [hΛo.frontier_eq] at hy
    exact hy.2
  have hycl : y ∈ closure Λ := frontier_subset_closure hy
  -- the bounded open set `O = B_R(0) \ S`
  obtain ⟨R₀, hR₀⟩ := hΛb.subset_closedBall 0
  have hclR₀ : closure Λ ⊆ closedBall 0 R₀ := closure_minimal hR₀ isClosed_closedBall
  set O : Set ℂ := ball 0 (R₀ + 1) \ S with hO_def
  have hOopen : IsOpen O := isOpen_ball.sdiff hSclosed
  have hObdd : Bornology.IsBounded O := isBounded_ball.subset sdiff_subset
  have hΛO : Λ ⊆ closure O := by
    intro w hw
    exact hSdense.open_subset_closure_inter isOpen_ball
      (closedBall_subset_ball (lt_add_one R₀) (hR₀ hw))
  -- a disc `closedBall y r ⊆ O`
  have hyz : ε < ‖y - z‖ := by
    by_contra h
    exact hyΛ (hεΛ (by rw [mem_closedBall, dist_eq_norm]; exact not_lt.1 h))
  set r := min (1 / 2) ((‖y - z‖ - ε) / 2) with hr_def
  have hr : 0 < r := lt_min (by norm_num) (by linarith)
  have hr₁ : r ≤ 1 / 2 := min_le_left _ _
  have hr₂ : r ≤ (‖y - z‖ - ε) / 2 := min_le_right _ _
  have hball : closedBall y r ⊆ O := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    refine ⟨?_, fun hwS => ?_⟩
    · have hy0 : ‖y‖ ≤ R₀ := by simpa using hclR₀ hycl
      rw [mem_ball, dist_zero_right]
      calc ‖w‖ = ‖(w - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ ‖w - y‖ + ‖y‖ := norm_add_le _ _
        _ < R₀ + 1 := by linarith
    · have hwz : ‖w - z‖ ≤ ε := by
        have := hwS.1
        rwa [mem_closedBall, dist_eq_norm] at this
      have : ‖y - z‖ ≤ ‖y - w‖ + ‖w - z‖ := norm_sub_le_norm_sub_add_norm_sub y w z
      rw [norm_sub_rev y w] at this
      linarith
  have hyO : y ∈ O := hball (mem_closedBall_self hr.le)
  -- the test function `f₂ = G_O(·, y)`
  refine ⟨fun x => greenFunction O x y, ⟨0, _, O, harmonicOnNhd_const 0, hOopen, hObdd, hΛO,
    greenFunction_mem_greenPotentialClass ⟨hyO, hyΛ⟩, (zero_add _).symm⟩, ?_⟩
  rintro ⟨hint, heq⟩
  change greenFunction O z y * μ.real Λ = ∫ x in Λ, greenFunction O x y ∂μ at heq
  have hz0 : greenFunction O z y = 0 := greenFunction_of_notMem_left (fun h => h.2 hzS) y
  rw [hz0, zero_mul] at heq
  have hpos : 0 < ∫ x in Λ, greenFunction O x y ∂μ := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ fun x => greenFunction_nonneg hObdd x y) hint]
    have hU : (ball y r ∩ Λ).Nonempty := mem_closure_iff.1 hycl _ isOpen_ball (mem_ball_self hr)
    refine lt_of_lt_of_le ((isOpen_ball.inter hΛo).measure_pos μ hU) (measure_mono ?_)
    rintro w ⟨hwb, hwΛ⟩
    refine ⟨?_, hwΛ⟩
    have hwy : 0 < ‖w - y‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hyΛ (h ▸ hwΛ))
    rw [mem_ball, dist_eq_norm] at hwb
    exact (greenFunction_pos hObdd hr hball hwy hwb).ne'
  linarith

/-- *No bounded open set is a harmonic ball in the sense printed at line 146*, for any measure `μ` charging every
nonempty open set (e.g. Lebesgue measure, or `μ_h` on its almost sure event of positive mass of open sets). Since
Theorem 1.1(b) asserts that the harmonic balls `Λ_t(z)` are bounded, Theorem 1.1 with the published test class is
false; correction C7 replaces `Λ ⊆ Ō` by `closure Λ ⊆ O`. -/
theorem not_isPublishedHarmonicBall {μ : Measure ℂ} [μ.IsOpenPosMeasure] {Λ : Set ℂ}
    (hΛb : Bornology.IsBounded Λ) (z : ℂ) : ¬ IsPublishedHarmonicBall μ Λ z := by
  rintro ⟨⟨hΛo, hz, -⟩, h⟩
  obtain ⟨f, hf, hnot⟩ := exists_not_hasMeanValueProperty_published (μ := μ) hΛo hΛb hz
  exact hnot (h f hf)

/-- The Lebesgue case: no bounded open set is a harmonic ball for Lebesgue measure in the sense printed at
line 146 (the example `Λ = B_1(0)`). -/
theorem not_isPublishedHarmonicBall_volume {Λ : Set ℂ} (hΛb : Bornology.IsBounded Λ) (z : ℂ) :
    ¬ IsPublishedHarmonicBall volume Λ z :=
  not_isPublishedHarmonicBall hΛb z

end HarmonicBalls
