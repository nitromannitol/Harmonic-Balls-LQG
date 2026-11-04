import HarmonicBalls.Proofs.Sec5.PunctureCapacityBarrier
import HarmonicBalls.Proofs.Sec5.PuncturedDiscContact

/-! # Competitors on a punctured disc

Capped Green barriers enforce the boundary constraint at an isolated point
while their effect away from that point tends to zero.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian

/-- Adding a function with nonpositive weak Laplacian preserves the upper bound. -/
theorem LaplacianLE.add_of_nonpos {w b : ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ}
    (hw : LaplacianLE w μ U) (hb : LaplacianLE b 0 U) :
    LaplacianLE (fun x => w x + b x) μ U := by
  refine ⟨hw.1.add hb.1, fun φ hφ hφ0 hφμ => ?_⟩
  have hzero := hb.2 φ hφ hφ0 integrable_zero_measure
  rw [integral_zero_measure] at hzero
  have heq : (fun x => (w x + b x) * Δ φ x) =
      fun x => w x * Δ φ x + b x * Δ φ x := by
    funext x
    ring
  rw [heq, integral_add (integrable_mul_laplacian_of_test hw.1 hφ)
    (integrable_mul_laplacian_of_test hb.1 hφ)]
  linarith [hw.2 φ hφ hφ0 hφμ]

/-- A capped Green barrier turns a disc supersolution into a punctured-disc
supersolution when its cap compensates for the value at the puncture. -/
theorem add_cappedGreenBarrier_mem_supersolutionsOn
    {μ : Measure ℂ} {R t c M : ℝ} {z a : ℂ} {w : ℂ → ℝ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (hw : w ∈ supersolutions μ R z t) (hc : 0 < c) (hM : 0 ≤ M)
    (hcap : 0 ≤ w a + M) :
    (fun x => w x + cappedGreenBarrier R a c M x) ∈
      supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t := by
  have hcl : closure (ball (0 : ℂ) R \ {a}) ⊆ closedBall (0 : ℂ) R :=
    closure_minimal (sdiff_subset.trans ball_subset_closedBall) isClosed_closedBall
  refine ⟨(hw.1.mono hcl).add ((continuousOn_cappedGreenBarrier ha hc).mono hcl), ?_, ?_⟩
  · exact (hw.2.1.mono_set sdiff_subset).add_of_nonpos
      ((laplacianLE_cappedGreenBarrier ha hc).mono_set sdiff_subset)
  · intro x hx hxz
    have hb := cappedGreenBarrier_nonneg (R := R) (a := a) (le_of_lt hc) hM (x := x)
    by_cases hxa : x = a
    · subst x
      have haU : a ∉ ball (0 : ℂ) R \ {a} := by simp
      rw [greenFunction_of_notMem_right haU]
      simp only [mul_zero, cappedGreenBarrier, ↓reduceIte]
      exact hcap
    · by_cases hxU : x ∈ ball (0 : ℂ) R \ {a}
      · rw [greenFunction_punctured_ball ha hz hxU hxz]
        linarith [hw.2.2 x (hcl hx) hxz]
      · have hxb : x ∉ ball (0 : ℂ) R := by
          intro hxb
          exact hxU ⟨hxb, hxa⟩
        have h1 := hw.2.2 x (hcl hx) hxz
        rw [greenFunction_of_notMem_right hxb, mul_zero] at h1
        rw [greenFunction_of_notMem_right hxU, mul_zero]
        linarith

/-- Away from the puncture, the punctured-domain infimum is bounded above
by every disc supersolution. -/
theorem leastSupersolutionOn_punctured_disc_le_supersolution
    {μ : Measure ℂ} {R t : ℝ} {z a x : ℂ} {w : ℂ → ℝ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (hw : w ∈ supersolutions μ R z t) (hx : x ∈ ball (0 : ℂ) R \ {a})
    (hxz : x ≠ z) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t x ≤ w x := by
  let M : ℝ := |w a| + 1
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hcap : 0 ≤ w a + M := by dsimp [M]; linarith [neg_abs_le (w a)]
  have hlim : Tendsto (fun c : ℝ => w x + cappedGreenBarrier R a c M x)
      (𝓝[>] 0) (𝓝 (w x)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_cappedGreenBarrier_coefficient_zero (show x ≠ a by simpa using hx.2) hM)
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with c hc
  exact leastSupersolutionOn_le_of_mem
    (add_cappedGreenBarrier_mem_supersolutionsOn ha hz hw hc hM hcap) (subset_closure hx) hxz

/-- A disc supersolution which is negative at the puncture forces the
punctured-domain least supersolution to be discontinuous there. -/
theorem not_continuousWithinAt_leastSupersolutionOn_punctured_disc
    {μ : Measure ℂ} {R t : ℝ} {z a : ℂ} {w : ℂ → ℝ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (ht : 0 ≤ t) (hw : w ∈ supersolutions μ R z t) (hneg : w a < 0) :
    ¬ ContinuousWithinAt (leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t)
      (ball (0 : ℂ) R \ {a}) a := by
  have haz : a ≠ z := Ne.symm (show z ≠ a by simpa using hz.2)
  have hac : a ∈ closure (ball (0 : ℂ) R \ {a}) := by
    have h := (dense_compl_singleton a).open_subset_closure_inter isOpen_ball ha
    simpa [sdiff_eq, inter_comm] using h
  have haU : a ∉ ball (0 : ℂ) R \ {a} := by simp
  have hUb : Bornology.IsBounded (ball (0 : ℂ) R \ {a}) := isBounded_ball.subset sdiff_subset
  have hv := leastSupersolutionOn_eq_zero_of_boundary (μ := μ) hUb ht hac haU haz
  have : (𝓝[ball (0 : ℂ) R \ {a}] a).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hac
  intro hcont
  have hnearv : ∀ᶠ x in 𝓝[ball (0 : ℂ) R \ {a}] a,
      w a / 2 < leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t x :=
    hcont.eventually (Ioi_mem_nhds (by rw [hv]; linarith))
  have hnearw : ∀ᶠ x in 𝓝[ball (0 : ℂ) R \ {a}] a, w x < w a / 2 := by
    have hwcont : ContinuousWithinAt w (ball (0 : ℂ) R \ {a}) a :=
      (hw.1 a (ball_subset_closedBall ha)).mono (sdiff_subset.trans ball_subset_closedBall)
    exact hwcont.eventually (Iio_mem_nhds (by linarith))
  have hnearz : ∀ᶠ x in 𝓝[ball (0 : ℂ) R \ {a}] a, x ≠ z :=
    (show ∀ᶠ x in 𝓝 a, x ≠ z from isOpen_compl_singleton.mem_nhds haz).filter_mono
      (nhdsWithin_le_nhds : 𝓝[ball (0 : ℂ) R \ {a}] a ≤ 𝓝 a)
  obtain ⟨x, hxv, hxw, hxz, hxU⟩ :=
    (hnearv.and (hnearw.and (hnearz.and self_mem_nhdsWithin))).exists
  have hle := leastSupersolutionOn_punctured_disc_le_supersolution ha hz hw hxU hxz
  linarith

/-- Under the same hypothesis the pointwise infimum is not an admissible
punctured-disc supersolution. -/
theorem leastSupersolutionOn_punctured_disc_not_mem_of_negative
    {μ : Measure ℂ} {R t : ℝ} {z a : ℂ} {w : ℂ → ℝ}
    (ha : a ∈ ball (0 : ℂ) R) (hz : z ∈ ball (0 : ℂ) R \ {a})
    (ht : 0 ≤ t) (hw : w ∈ supersolutions μ R z t) (hneg : w a < 0) :
    leastSupersolutionOn μ (ball (0 : ℂ) R \ {a}) z t ∉
      supersolutionsOn μ (ball (0 : ℂ) R \ {a}) z t := by
  intro hv
  have hac : a ∈ closure (ball (0 : ℂ) R \ {a}) := by
    have h := (dense_compl_singleton a).open_subset_closure_inter isOpen_ball ha
    simpa [sdiff_eq, inter_comm] using h
  exact not_continuousWithinAt_leastSupersolutionOn_punctured_disc ha hz ht hw hneg
    ((hv.1 a hac).mono subset_closure)

#print axioms not_continuousWithinAt_leastSupersolutionOn_punctured_disc
#print axioms leastSupersolutionOn_punctured_disc_not_mem_of_negative

#print axioms LaplacianLE.add_of_nonpos
#print axioms add_cappedGreenBarrier_mem_supersolutionsOn
#print axioms leastSupersolutionOn_punctured_disc_le_supersolution

end HarmonicBalls
