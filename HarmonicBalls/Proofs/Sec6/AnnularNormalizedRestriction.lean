import HarmonicBalls.Proofs.Sec6.AnnularCenteredExhaustion

/-! # Annular normalized restrictions in the local field

The imported annular exhaustion uses Leonardo Bonanno's LatticeProb
formalization of the ergodic theorem.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- The normalized LQG restriction to an annulus has a version measurable in
the field on that annulus modulo additive constants, provided the annulus is
a positive finite-mass continuity set. -/
theorem IsWholePlaneGFF.exists_modConst_annular_normalizedRestriction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (z : ℂ) {r R : ℝ} (hr : 0 ≤ r) (hrR : r < R)
    (hfront : ∀ᵐ ω ∂P, μ ω (frontier (annulus z r R)) = 0)
    (hfinite : ∀ᵐ ω ∂P, μ ω (annulus z r R) ≠ ∞)
    (hpositive : ∀ᵐ ω ∂P, 0 < μ ω (annulus z r R)) :
    ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (fieldSigmaAlgebraModConst 0 hC (annulus z r R)) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (annulus z r R) := by
  let : IsProbabilityMeasure P := hgff.isProbabilityMeasure
  have hanchor : z + (((r + R) / 2 : ℝ) : ℂ) ∈ annulus z r R := by
    have hm : 0 ≤ (r + R) / 2 := by linarith
    have hd : dist (z + (((r + R) / 2 : ℝ) : ℂ)) z = (r + R) / 2 := by
      simp only [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hm]
    change dist (z + (((r + R) / 2 : ℝ) : ℂ)) z < R ∧
      ¬ dist (z + (((r + R) / 2 : ℝ) : ℂ)) z ≤ r
    rw [hd]
    constructor <;> linarith
  obtain ⟨E, d, hEm, hmono, hE, hbounded, hEf, hdm, hdeq⟩ :=
    IsWholePlaneGFF.exists_centered_lqg_annular_exhaustion hgff hμ z hr hrR hfront _ hanchor
  obtain ⟨S, hcount, hpi, _, hopen, hgen, hSfront⟩ :=
    hgff.exists_ae_lqg_continuity_piSystem P hμ
  have hfronts := ae_frontiers_intersections_of_common_continuity P μ E S hEf hSfront
  have hmass : ∀ᵐ ω ∂P, μ ω (annulus z r R) ≠ 0 ∧ μ ω (annulus z r R) ≠ ∞ := by
    filter_upwards [hpositive, hfinite] with ω hp hf
    exact ⟨hp.ne', hf⟩
  apply exists_normalizedRestriction_version_of_ae_piSystem_ratios P
    (fieldSigmaAlgebraModConst 0 hC (annulus z r R))
    ((fieldSigmaAlgebraModConst_le 0 hC _).trans (hgff.fieldSigmaAlgebra_le 0 _))
    μ (hgff.aemeasurable_lqgMeasure hμ) (annulus z r R)
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet hmass S hcount hgen hpi
    (fun V hV => (hopen V hV).measurableSet)
  intro V hV
  have hp : ∀ᵐ ω ∂P, μ ω (⋃ n, E n) ≠ 0 ∧ μ ω (⋃ n, E n) ≠ ∞ := by
    filter_upwards [hmass] with ω hω
    simpa only [hE] using hω
  have hfV : ∀ᵐ ω ∂P,
      (∀ n, μ ω (frontier (E n)) = 0 ∧ μ ω (frontier (V ∩ E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0 ∧ μ ω (frontier (V ∩ ⋃ n, E n)) = 0 := by
    filter_upwards [hfronts] with ω hω
    exact hω V hV
  have hv := exists_local_lqg_ratio_version_of_centered_exhaustion P
    (fieldSigmaAlgebraModConst 0 hC (annulus z r R)) hgff hμ E hEm hmono hbounded V
    (hopen V hV).measurableSet hfV hp _ d hdm hdeq
  simpa only [hE] using hv

/-- Full support and the staged affine laws provide an annular normalized
restriction measurable in the field modulo constants. -/
theorem IsWholePlaneGFF.exists_modConst_annular_normalizedRestriction_of_affine
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hgff : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hQ : 0 < lqgQ γ)
    (z : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (fieldSigmaAlgebraModConst 0 hC (annulus z r R)) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (annulus z r R) := by
  have hnonempty : (annulus z r R).Nonempty := by
    refine ⟨z + (((r + R) / 2 : ℝ) : ℂ), ?_⟩
    have hm : 0 ≤ (r + R) / 2 := by linarith
    have hd : dist (z + (((r + R) / 2 : ℝ) : ℂ)) z = (r + R) / 2 := by
      simp only [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hm]
    change dist (z + (((r + R) / 2 : ℝ) : ℂ)) z < R ∧
      ¬ dist (z + (((r + R) / 2 : ℝ) : ℂ)) z ≤ r
    rw [hd]
    constructor <;> linarith
  apply IsWholePlaneGFF.exists_modConst_annular_normalizedRestriction hgff hμ z hr.le hrR
    (ae_lqg_annulus_frontier_eq_zero_of_affine hgff hμ hAff hCC hγ hγ2 z hr
      (by linarith))
  · filter_upwards [hμ] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω.isLocallyFiniteMeasure
    exact ne_top_of_le_ne_top measure_ball_ne_top (measure_mono Set.sdiff_subset)
  · filter_upwards [hfull γ 0 hγ hγ2 hQ Ω P hC hcirc μ hgff hμ] with ω hω
    exact hω _ (isOpen_ball.sdiff isClosed_closedBall) hnonempty

end HarmonicBalls.Section6
