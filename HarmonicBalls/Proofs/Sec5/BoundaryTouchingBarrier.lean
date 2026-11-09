import HarmonicBalls.Proofs.Sec6.AnnulusOdometerPotential
import HarmonicBalls.Steps.Sec3.LeastSupersolutionMem
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.Sec8.GreenKernelContinuity
import HarmonicBalls.Proofs.Potential.GreenBall

/-!
# Finite auxiliary barrier for the boundary-touching right-continuity step

Section 4 of the released draft (`steps4-t4.tex` lines 927-955, Comparison at a point separated from the old cluster):
for `p` in the closed unit disc and `0 < r < 1/8`, with `E = B_r(p) ∩ B_1` and `S = ∂B_r(p) ∩ closed B_1`, the finite
sum `H` of actual radius-4 odometers at auxiliary poles `q ∈ S` is nonnegative and continuous on `E`, vanishes on
`E ∩ B_{r/2}(p)`, is bounded below by `1` on `S` away from the poles, tends to `+∞` at each pole, and satisfies
`Δ H ≤ N μ` on `E` with `N` the number of poles.

The auxiliary poles and masses come from the small-auxiliary-cluster premise `hsmall`, a hypothesis of the theorem (the
separate small-time proposition of the source), not a proved statement here. The regularity used is the already proved
obstacle regularity (Lemma 3.1 in deterministic form, the distributional odometer bound away from the pole, and the
Green singularity of the ball). The poles keep the odometer's own value at the pole; no extended function is used.

Credit: the Green function and potential-theoretic infrastructure reached through the import closure use work of
Leonardo Bonanno, through the pinned Lattice-Probability (lean-v4.35) port.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian

/-- Divergence of the actual radius-4 odometer at its pole: the least supersolution is continuous on the closed ball,
hence bounded below near the pole, and the Green function tends to `+∞` at the pole. -/
theorem tendsto_odometer_pole_atTop {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βm βp : ℝ} (hV : VolumeGrowth μ 4 βm βp) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 4) {t : ℝ} (ht : 0 < t) :
    Tendsto (odometer μ 4 z t) (𝓝[≠] z) atTop := by
  have hv : ContinuousOn (leastSupersolution μ 4 z t) (closedBall (0 : ℂ) 4) :=
    (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
      obstacleCompatibilityShiftStep_holds hμ (by norm_num) hV hz ht).2.1
  have hcl : closedBall (0 : ℂ) 4 ∈ 𝓝 z :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hz) ball_subset_closedBall
  have hvz : Tendsto (leastSupersolution μ 4 z t) (𝓝[≠] z) (𝓝 (leastSupersolution μ 4 z t z)) :=
    ((hv.continuousAt hcl).tendsto).mono_left nhdsWithin_le_nhds
  have hg : Tendsto (fun x : ℂ => t * greenFunction (ball (0 : ℂ) 4) z x) (𝓝[≠] z) atTop :=
    Tendsto.const_mul_atTop ht (tendsto_greenFunction_ball_pole hz)
  exact hvz.add_atTop hg

/-- Off the pole the actual radius-4 odometer is continuous on the closed ball. -/
theorem continuousOn_odometer_off_pole {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βm βp : ℝ} (hV : VolumeGrowth μ 4 βm βp) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 4) {t : ℝ} (ht : 0 < t) :
    ContinuousOn (odometer μ 4 z t) (closedBall (0 : ℂ) 4 \ {z}) := by
  have hv : ContinuousOn (leastSupersolution μ 4 z t) (closedBall (0 : ℂ) 4) :=
    (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
      obstacleCompatibilityShiftStep_holds hμ (by norm_num) hV hz ht).2.1
  have hG : ContinuousOn (fun x : ℂ => greenFunction (ball (0 : ℂ) 4) z x)
      (closedBall (0 : ℂ) 4 \ {z}) :=
    (continuousOn_greenFunction_ball hz).mono fun _ hx => hx.2
  exact (hv.mono sdiff_subset).add (continuousOn_const.mul hG)

/-- An odometer vanishes at a point of its ball that lies outside its cluster. -/
theorem odometer_eq_zero_of_not_mem_cluster_ball {μ : Measure ℂ} {z x : ℂ} {t : ℝ} (ht : 0 ≤ t)
    (hx : x ∈ ball (0 : ℂ) 4) (hxΛ : x ∉ cluster μ 4 z t) : odometer μ 4 z t x = 0 := by
  rw [mem_cluster_iff, not_and, not_or] at hxΛ
  obtain ⟨hxz, hpos⟩ := hxΛ hx
  exact le_antisymm (not_lt.1 hpos) (odometer_nonneg (μ := μ) ht (ball_subset_closedBall hx) hxz)

/-- Away from its pole the distributional Laplacian of the actual radius-4 odometer is dominated by `μ`
(the existing odometer inequality, `Section6.odometer_hasLaplacian_dominated_away_from_pole`). -/
theorem laplacianLE_odometer_of_open {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βm βp : ℝ} (hV : VolumeGrowth μ 4 βm βp) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 4) {t : ℝ} (ht : 0 < t)
    {U : Set ℂ} (hU : IsOpen U) (hUsub : U ⊆ ball (0 : ℂ) 4 \ {z}) :
    LaplacianLE (odometer μ 4 z t) μ U := by
  obtain ⟨η, hη, -, hΔ⟩ :=
    Section6.odometer_hasLaplacian_dominated_away_from_pole hμ (by norm_num) hV hz ht hU.measurableSet hUsub
  refine ⟨hΔ.1, fun φ hφ hφ0 hφμ => ?_⟩
  exact (hΔ.laplacianLE.2 φ hφ hφ0 (hφμ.mono_measure hη)).trans
    (integral_mono_measure hη (Filter.Eventually.of_forall hφ0) hφμ)

/-- Sum of two distributional bounds, with the measures added. -/
theorem laplacianLE_add_measure {w₁ w₂ : ℂ → ℝ} {μ₁ μ₂ : Measure ℂ} {U : Set ℂ}
    (h₁ : LaplacianLE w₁ μ₁ U) (h₂ : LaplacianLE w₂ μ₂ U) :
    LaplacianLE (fun x => w₁ x + w₂ x) (μ₁ + μ₂) U := by
  refine ⟨h₁.1.add h₂.1, fun φ hφ hφ0 hφμ => ?_⟩
  obtain ⟨hφ1, hφ2⟩ := integrable_add_measure.1 hφμ
  have heq : (fun x => (w₁ x + w₂ x) * Δ φ x) = fun x => w₁ x * Δ φ x + w₂ x * Δ φ x := by
    funext x
    ring
  show ∫ x, (w₁ x + w₂ x) * Δ φ x ≤ ∫ x, φ x ∂(μ₁ + μ₂)
  rw [heq, integral_add (integrable_mul_laplacian_of_test h₁.1 hφ) (integrable_mul_laplacian_of_test h₂.1 hφ),
    integral_add_measure hφ1 hφ2]
  linarith [h₁.2 φ hφ hφ0 hφ1, h₂.2 φ hφ hφ0 hφ2]

/-- Finite sums of distributional bounds, with `T.card • μ` as the measure bound. -/
theorem laplacianLE_finset_sum {ι : Type*} [DecidableEq ι] (T : Finset ι) {w : ι → ℂ → ℝ} {μ : Measure ℂ}
    {U : Set ℂ} : (∀ i ∈ T, LaplacianLE (w i) μ U) → LaplacianLE (fun x => ∑ i ∈ T, w i x) (T.card • μ) U := by
  induction T using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.sum_empty, Finset.card_empty, zero_smul]
    exact laplacianLE_zero 0 U
  | @insert a T ha ih =>
    intro h
    have hT : ∀ i ∈ T, LaplacianLE (w i) μ U := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have hsum := laplacianLE_add_measure (h a (Finset.mem_insert_self a T)) (ih hT)
    rw [Finset.card_insert_of_notMem ha, succ_nsmul, add_comm]
    simp only [Finset.sum_insert ha]
    exact hsum

/-- The sphere `∂B_r(p)` meets the closed unit disc when `p` is in the closed unit disc and `0 < r < 1/8`. -/
theorem sphere_inter_closedBall_nonempty {p : ℂ} (hp : p ∈ closedBall (0 : ℂ) 1) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1 / 8) : (sphere p r ∩ closedBall (0 : ℂ) 1).Nonempty := by
  by_cases hp0 : p = 0
  · refine ⟨(r : ℂ), ?_, ?_⟩
    · rw [mem_sphere, hp0, dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hr0.le]
    · rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_of_nonneg hr0.le]
      linarith
  · have hn0 : 0 < ‖p‖ := norm_pos_iff.2 hp0
    have hne : ‖p‖ ≠ 0 := hn0.ne'
    have hn1 : ‖p‖ ≤ 1 := mem_closedBall_zero_iff.1 hp
    refine ⟨((1 - r / ‖p‖ : ℝ) : ℂ) * p, ?_, ?_⟩
    · rw [mem_sphere, dist_eq_norm]
      have h : ((1 - r / ‖p‖ : ℝ) : ℂ) * p - p = ((-(r / ‖p‖) : ℝ) : ℂ) * p := by
        push_cast
        ring
      rw [h, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos (div_pos hr0 hn0),
        div_mul_cancel₀ r hne]
    · rw [mem_closedBall_zero_iff, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have e : (1 - r / ‖p‖) * ‖p‖ = ‖p‖ - r := by
        rw [sub_mul, one_mul, div_mul_cancel₀ r hne]
      calc |1 - r / ‖p‖| * ‖p‖ = |(1 - r / ‖p‖) * ‖p‖| := by rw [abs_mul, abs_of_pos hn0]
        _ = |‖p‖ - r| := by rw [e]
        _ ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩

/-- **Finite auxiliary barrier** (Section 4, lines 927-955, deterministic part). Under the small-auxiliary-cluster
premise `hsmall` (for each pole `q ∈ S` some mass `σ > 0` has `closure (cluster μ 4 q σ) ⊆ B_{r/4}(q)`), there are a
finite set `T ⊆ S` of poles with masses `σ q > 0` such that the literal sum `H` of the actual odometers
`odometer μ 4 q (σ q)` satisfies the listed properties on `E = B_r(p) ∩ B_1` and `S`. The pole convention of the actual
odometer is unchanged; `H` is a finite sum of actual odometers, not an assumed barrier. -/
theorem finite_auxiliary_barrier_boundary_touching
    (μ : Measure ℂ) (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ} (hV : VolumeGrowth μ 4 βm βp)
    {p : ℂ} (hp : p ∈ closedBall (0 : ℂ) 1) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1 / 8)
    (hsmall : ∀ q ∈ sphere p r ∩ closedBall (0 : ℂ) 1,
      ∃ σ : ℝ, 0 < σ ∧ closure (cluster μ 4 q σ) ⊆ ball q (r / 4)) :
    ∃ (T : Finset ℂ) (σ : ℂ → ℝ) (H : ℂ → ℝ),
      1 ≤ T.card ∧
      (∀ q ∈ T, q ∈ sphere p r ∩ closedBall (0 : ℂ) 1) ∧
      (∀ q ∈ T, 0 < σ q) ∧
      H = (fun x => ∑ q ∈ T, odometer μ 4 q (σ q) x) ∧
      (∀ x ∈ ball p r ∩ ball (0 : ℂ) 1, 0 ≤ H x) ∧
      ContinuousOn H (ball p r ∩ ball (0 : ℂ) 1) ∧
      (∀ x ∈ ball p r ∩ ball (0 : ℂ) 1 ∩ ball p (r / 2), H x = 0) ∧
      (∃ c : ℝ, 0 < c ∧ ∀ x ∈ sphere p r ∩ closedBall (0 : ℂ) 1, (∀ q ∈ T, x ≠ q) → c ≤ H x) ∧
      (∀ q ∈ T, Tendsto H (𝓝[≠] q) atTop) ∧
      LaplacianLE H (T.card • μ) (ball p r ∩ ball (0 : ℂ) 1) := by
  classical
  have hEb4 : ∀ x ∈ ball p r ∩ ball (0 : ℂ) 1, x ∈ ball (0 : ℂ) 4 := fun x hx => by
    have h1 : ‖x‖ < 1 := mem_ball_zero_iff.1 hx.2
    exact mem_ball_zero_iff.2 (by linarith)
  have hSb4 : ∀ q ∈ sphere p r ∩ closedBall (0 : ℂ) 1, q ∈ ball (0 : ℂ) 4 := fun q hq => by
    have h1 : ‖q‖ ≤ 1 := mem_closedBall_zero_iff.1 hq.2
    exact mem_ball_zero_iff.2 (by linarith)
  have hEne : ∀ x ∈ ball p r ∩ ball (0 : ℂ) 1, ∀ q ∈ sphere p r ∩ closedBall (0 : ℂ) 1, x ≠ q := by
    intro x hx q hq hxq
    have h1 : dist x p < r := mem_ball.1 hx.1
    have h2 : dist q p = r := mem_sphere.1 hq.1
    rw [hxq] at h1
    linarith
  -- auxiliary masses from the small-cluster premise
  have hσex : ∀ x : ℂ, ∃ σ : ℝ, x ∈ sphere p r ∩ closedBall (0 : ℂ) 1 →
      0 < σ ∧ closure (cluster μ 4 x σ) ⊆ ball x (r / 4) := by
    intro x
    by_cases hx : x ∈ sphere p r ∩ closedBall (0 : ℂ) 1
    · obtain ⟨σ, hσ0, hcl⟩ := hsmall x hx
      exact ⟨σ, fun _ => ⟨hσ0, hcl⟩⟩
    · exact ⟨1, fun h => absurd h hx⟩
  choose σ hσ using hσex
  -- positivity radii from the divergence at each pole
  have hρex : ∀ x : ℂ, ∃ ρ : ℝ, 0 < ρ ∧
      (x ∈ sphere p r ∩ closedBall (0 : ℂ) 1 →
        ∀ y ∈ ball x ρ, y ≠ x → 1 ≤ odometer μ 4 x (σ x) y) := by
    intro x
    by_cases hx : x ∈ sphere p r ∩ closedBall (0 : ℂ) 1
    · have hdiv := tendsto_odometer_pole_atTop hμ hV (hSb4 x hx) (hσ x hx).1
      have hev : ∀ᶠ y in 𝓝[≠] x, 1 ≤ odometer μ 4 x (σ x) y := hdiv.eventually_ge_atTop 1
      obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hev)
      exact ⟨ρ, hρ, fun _ y hy hyx => hball hy hyx⟩
    · exact ⟨1, one_pos, fun h => absurd h hx⟩
  choose ρ hρpos hρ using hρex
  -- finite positivity cover of the compact set S
  have hS_compact : IsCompact (sphere p r ∩ closedBall (0 : ℂ) 1) :=
    (isCompact_sphere p r).inter_right isClosed_closedBall
  obtain ⟨T, hTS, hScov⟩ := hS_compact.elim_nhds_subcover (fun x => ball x (ρ x))
    (fun x _ => Metric.ball_mem_nhds x (hρpos x))
  have hT : 1 ≤ T.card := by
    obtain ⟨s, hs⟩ := sphere_inter_closedBall_nonempty hp hr0 hr1
    obtain ⟨q, hqT, -⟩ := mem_iUnion₂.1 (hScov hs)
    exact Finset.card_pos.2 ⟨q, hqT⟩
  refine ⟨T, σ, fun x => ∑ q ∈ T, odometer μ 4 q (σ q) x, hT, fun q hq => hTS q hq,
    fun q hq => (hσ q (hTS q hq)).1, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- nonnegativity on E
    intro x hx
    show 0 ≤ ∑ q ∈ T, odometer μ 4 q (σ q) x
    exact Finset.sum_nonneg fun q hq =>
      odometer_nonneg (μ := μ) (hσ q (hTS q hq)).1.le (ball_subset_closedBall (hEb4 x hx))
        (hEne x hx q (hTS q hq))
  · -- continuity on E
    apply continuousOn_finsetSum T
    intro q hq
    exact (continuousOn_odometer_off_pole hμ hV (hSb4 q (hTS q hq)) (hσ q (hTS q hq)).1).mono
      (fun x hx => ⟨ball_subset_closedBall (hEb4 x hx), hEne x hx q (hTS q hq)⟩)
  · -- vanishing on E ∩ B_{r/2}(p)
    intro x hx
    show ∑ q ∈ T, odometer μ 4 q (σ q) x = 0
    apply Finset.sum_eq_zero
    intro q hq
    have hqS := hTS q hq
    apply odometer_eq_zero_of_not_mem_cluster_ball (hσ q hqS).1.le (hEb4 x hx.1)
    intro hcl
    have hxcl : x ∈ ball q (r / 4) := (hσ q hqS).2 (subset_closure hcl)
    have hd1 : dist q p = r := mem_sphere.1 hqS.1
    have hd2 : dist x p < r / 2 := mem_ball.1 hx.2
    have hd3 : dist x q < r / 4 := mem_ball.1 hxcl
    have htri : dist q p ≤ dist q x + dist x p := dist_triangle q x p
    rw [dist_comm q x] at htri
    linarith
  · -- uniform lower bound on S away from the poles
    refine ⟨1, one_pos, fun x hx hxT => ?_⟩
    obtain ⟨q, hqT, hxq⟩ := mem_iUnion₂.1 (hScov hx)
    have h1 : 1 ≤ odometer μ 4 q (σ q) x := hρ q (hTS q hqT) x hxq (hxT q hqT)
    have hle : odometer μ 4 q (σ q) x ≤ ∑ q' ∈ T, odometer μ 4 q' (σ q') x :=
      Finset.single_le_sum (f := fun q' => odometer μ 4 q' (σ q') x)
        (fun q' hq' => odometer_nonneg (μ := μ) (hσ q' (hTS q' hq')).1.le
          (ball_subset_closedBall (hSb4 x hx)) (hxT q' hq')) hqT
    show 1 ≤ ∑ q' ∈ T, odometer μ 4 q' (σ q') x
    linarith
  · -- infinite lower limit at each pole
    intro q hq
    have hqS := hTS q hq
    have hdiv := tendsto_odometer_pole_atTop hμ hV (hSb4 q hqS) (hσ q hqS).1
    have hne : ∀ q' ∈ T.erase q, ∀ᶠ x in 𝓝[≠] q, x ≠ q' := fun q' hq' =>
      nhdsWithin_le_nhds (eventually_ne_nhds (Finset.ne_of_mem_erase hq').symm)
    have hall := (Filter.eventually_all_finset (T.erase q)).2 hne
    have hball : ∀ᶠ x in 𝓝[≠] q, x ∈ ball (0 : ℂ) 4 :=
      nhdsWithin_le_nhds (isOpen_ball.mem_nhds (hSb4 q hqS))
    have hle : ∀ᶠ x in 𝓝[≠] q,
        odometer μ 4 q (σ q) x ≤ ∑ q' ∈ T, odometer μ 4 q' (σ q') x := by
      filter_upwards [hall, hball] with x hxall hxb
      have hnn : 0 ≤ ∑ q' ∈ T.erase q, odometer μ 4 q' (σ q') x :=
        Finset.sum_nonneg fun q' hq' =>
          odometer_nonneg (μ := μ) (hσ q' (hTS q' (Finset.mem_of_mem_erase hq'))).1.le
            (ball_subset_closedBall hxb) (hxall q' hq')
      rw [← Finset.add_sum_erase T _ hq]
      linarith
    exact Filter.tendsto_atTop_mono' _ hle hdiv
  · -- distributional bound on E
    have hU : IsOpen (ball p r ∩ ball (0 : ℂ) 1) := isOpen_ball.inter isOpen_ball
    exact laplacianLE_finset_sum (w := fun q => odometer μ 4 q (σ q)) T fun q hq =>
      laplacianLE_odometer_of_open hμ hV (hSb4 q (hTS q hq)) (hσ q (hTS q hq)).1 hU
        (fun x hx => ⟨hEb4 x hx, hEne x hx q (hTS q hq)⟩)

end HarmonicBalls
