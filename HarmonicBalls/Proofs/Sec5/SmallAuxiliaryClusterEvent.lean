import HarmonicBalls.Proofs.Sec5.PunctureInadmissibilityAllTimes
import HarmonicBalls.Proofs.Sec5.OpenHorizonPositivity

/-! # Small auxiliary clusters of radius four, for every pole of the closed unit disc

For a whole-plane Gaussian free field and its gamma-LQG measure `mu` with parameter `alpha0`, the
scaled small-time proposition `ClusterUpperBoundPolyHighProbStmt` (Proposition 7.1 of the source,
pp. 37-38) is applied to the normalized pullback of `mu` by the factor `4`, at poles `q / 4` in `B_{1/2}`.
The whole-plane affine invariance `WholePlaneGFFAffineInvariance` and the LQG coordinate change
`LQGMeasureCoordChange` transport the field inputs. Borel-Cantelli at dyadic times, together with a
countable intersection over the radii, gives one event on which the cluster at radius `4` is small around
every pole of the closed unit disc. The cluster at radius `4` is the dilation by `4` of the cluster of the
normalized pullback at radius `1`, so no radius-four small-cluster event, boundary mass assertion or
compact containment of an old cluster is assumed; the only inputs are the explicit field hypotheses.

Credit: Leonardo Bonanno. His Lattice-Probability formalization, on the pinned lean-v4.35 line
(`lakefile.lean`, commit 3912597a70dcc6c9b73042abd884a26989341c8d), is consumed here through the imports:
`LatticeProb.Prob.Birkhoff` lies in the import closure of this module, and those modules carry his credit.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Pointwise

universe u

/-- **Small auxiliary clusters of radius four.** Let `0 < gamma < 2` and `alpha0 < lqgQ gamma`. For a
whole-plane GFF `(P, hC, hcirc)` and its gamma-LQG measure `mu` with parameter `alpha0`, almost surely the
following holds: for every pole `q` in the closed unit disc and every radius `a > 0` there is a mass
`sigma > 0` with `closure (cluster (mu omega) 4 q sigma) ⊆ ball q a`. The event is fixed before the pole
and the radius. -/
theorem ae_radiusFour_cluster_small_all_centres
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ q ∈ closedBall (0 : ℂ) 1, ∀ a : ℝ, 0 < a →
      ∃ σ : ℝ, 0 < σ ∧ closure (cluster (μ ω) 4 q σ) ⊆ ball q a := by
  let hC' := affinePairing hC hcirc (4 : ℂ) 0
  let hcirc' : Ω → ℝ → ℂ → ℝ := fun ω r z =>
    hcirc ω (4 * r) ((4 : ℝ) • z) - hcirc ω 4 0
  have hGFF' : IsWholePlaneGFF P hC' hcirc' := by
    have hcirc_eq : hcirc' = affineCircle hcirc (4 : ℂ) 0 := by
      funext ω r z
      simp [hcirc', affineCircle, Complex.real_smul]
    rw [hcirc_eq]
    exact hAff hGFF (4 : ℂ) (by norm_num) 0
  have hμ' : IsLQGMeasureOfField P γ α₀ hcirc'
      (fun ω => normalizedPullbackMeasure γ α₀ 4 (hcirc ω) (μ ω)) :=
    isLQGMeasureOfField_normalizedPullback hCC hGFF hγ hγ2 hα hμ (by norm_num)
  have hevent : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 / 2),
        closure (cluster (normalizedPullbackMeasure γ α₀ 4 (hcirc ω) (μ ω)) 1 z t) ⊆
          ball z (((2 : ℝ)⁻¹ ^ n / 2) / 2) := by
    intro n
    have hr : ((2 : ℝ)⁻¹ ^ n / 2) ∈ Ioo (0 : ℝ) 1 := by
      constructor
      · positivity
      · have hp : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
        linarith
    have h := h71 γ α₀ hγ hγ2 hα Ω P hC' hcirc' _ hGFF' hμ' _ hr
    filter_upwards [h.ae_eventually_dyadic] with ω hω
    obtain ⟨m, hm⟩ := hω.exists
    exact ⟨(2 : ℝ)⁻¹ ^ m, by positivity, hm⟩
  filter_upwards [ae_all_iff.mpr hevent] with ω hsmall
  intro q hq a ha
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ha (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨T, hT, hbound⟩ := hsmall n
  have hq' : ((4 : ℝ)⁻¹ • q) ∈ ball (0 : ℂ) (1 / 2) := by
    rw [mem_closedBall_zero_iff] at hq
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4⁻¹)]
    linarith
  let c : ℝ := Real.exp (γ * (lqgQ γ * Real.log 4 + fieldCircleAverage α₀ (hcirc ω) 4 0))
  have hc : 0 < c := Real.exp_pos _
  let σ : ℝ := c * (T / 2)
  have hσ : 0 < σ := mul_pos hc (half_pos hT)
  have hσdiv : σ / c = T / 2 := by
    dsimp [σ]
    field_simp
  have hcl := hbound (T / 2) ⟨half_pos hT, (half_lt_self hT).le⟩ ((4 : ℝ)⁻¹ • q) hq'
  have hsmul : (4 : ℝ) • ((4 : ℝ)⁻¹ • q) = q := by
    rw [smul_smul, mul_inv_cancel₀ (by norm_num : (4 : ℝ) ≠ 0), one_smul]
  have hscale := cluster_normalizedPullback_smul (γ := γ) (α₀ := α₀) (k := 4) (R := 1) (t := σ)
    (hcirc := hcirc ω) (μ := μ ω) (z := (4 : ℝ)⁻¹ • q) (by norm_num) hσ.le
  change (4 : ℝ) • cluster (normalizedPullbackMeasure γ α₀ 4 (hcirc ω) (μ ω)) 1
    ((4 : ℝ)⁻¹ • q) (σ / c) = cluster (μ ω) (4 * 1) ((4 : ℝ) • ((4 : ℝ)⁻¹ • q)) σ at hscale
  rw [hσdiv, mul_one, hsmul] at hscale
  have hball : (4 : ℝ) • ball ((4 : ℝ)⁻¹ • q) (((2 : ℝ)⁻¹ ^ n / 2) / 2) =
      ball q (4 * (((2 : ℝ)⁻¹ ^ n / 2) / 2)) := by
    change (fun x : ℂ => (4 : ℝ) • x) '' _ = _
    simpa only [hsmul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 4)] using
      (Metric.smul_image_ball (by norm_num : (4 : ℝ) ≠ 0) ((4 : ℝ)⁻¹ • q)
        (((2 : ℝ)⁻¹ ^ n / 2) / 2))
  have hcl' : closure (cluster (μ ω) 4 q σ) ⊆ ball q (4 * (((2 : ℝ)⁻¹ ^ n / 2) / 2)) := by
    rw [← hscale, closure_smul₀' (by norm_num : (4 : ℝ) ≠ 0), ← hball]
    exact smul_set_mono hcl
  refine ⟨σ, hσ, hcl'.trans (ball_subset_ball ?_)⟩
  linarith

end HarmonicBalls
