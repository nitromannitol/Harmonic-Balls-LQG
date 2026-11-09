import HarmonicBalls.Proofs.Sec5.SmallAuxiliaryClusterEvent
import HarmonicBalls.Proofs.Sec5.BoundaryTouchingBarrier
import HarmonicBalls.Steps.Sec2.GreenFunctionBall
import HarmonicBalls.Steps.Sec3.LeastSupersolutionMem
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.SecA.ObstacleNonCoincidenceHarmonic
import HarmonicBalls.Steps.Sec4.Basic
import HarmonicBalls.Proofs.Sec6.TruncatedOdometerLaplacian
import HarmonicBalls.Proofs.Sec6.TruncatedSubharmonic
import HarmonicBalls.Proofs.Sec6.DiscPotentialComparison
import HarmonicBalls.Proofs.Sec5.AccumulationSubharmonicMaximum
import HarmonicBalls.Steps.Sec5.ContinuityAssembly
import HarmonicBalls.Proofs.SecA.ObstacleLeastSuperharmonicMajorant
import HarmonicBalls.Proposed.LQG
import HarmonicBalls.Proofs.Sec2.SingularWeight
import HarmonicBalls.Proofs.Sec2.BallMassReduction
import HarmonicBalls.Proofs.Sec2.Assembly
import HarmonicBalls.Steps.Sec2.VolumeGrowth

/-!
# Local persistence and the boundary-touching right-continuity step (Proposition 5.2)

Stage 1 (`eq:local-persistence-zero`, steps4-final.tex lines 1161-1228): for a fixed event, a point `p`
of the closed unit disc at positive distance from the closure of an old cluster is avoided by the cluster
at all times `t + s`, `0 ≤ s ≤ δ`. The comparison is the least-supersolution monotonicity in the mass, the
finite auxiliary barrier of `BoundaryTouchingBarrier.lean`, the active-set Laplacian identity of the
odometer, and the maximum principle for subharmonic functions.

Stage 2 (lines 1230-1253): compactness of the complement of an `ε`-neighbourhood of the old cluster.

Credit: Leonardo Bonanno. The small-cluster event `SmallAuxiliaryClusterEvent.lean` consumes his
Lattice-Probability formalization on the pinned lean-v4.35 line (`lakefile.lean`, commit 3912597a70dcc6c9b73042abd884a26989341c8d),
through the import closure of `LatticeProb.Prob.Birkhoff`; those modules carry his credit.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Laplacian
open scoped Pointwise ENNReal

universe u

/-! ## Least supersolutions: the zero function and monotonicity in the mass -/

/-- The Green function of a disc is nonnegative (`greenFunction_nonneg` on the bounded ball). -/
theorem greenFunction_ball_nonneg (r : ℝ) (z x : ℂ) : 0 ≤ greenFunction (ball (0 : ℂ) r) z x :=
  greenFunction_nonneg isBounded_ball z x

/-- The zero function is a supersolution for every nonnegative mass (the obstacle `-t G` is nonpositive). -/
theorem zero_mem_supersolutions_ball {μ : Measure ℂ} {r : ℝ} {z : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    (0 : ℂ → ℝ) ∈ supersolutions μ r z t := by
  refine ⟨continuousOn_const, ⟨continuous_zero.locallyIntegrable.locallyIntegrableOn _, ?_⟩, ?_⟩
  · intro φ _ hφ0 _
    simp only [Pi.zero_apply, zero_mul, integral_zero]
    exact integral_nonneg fun x => hφ0 x
  · intro x _ hxz
    have hG := greenFunction_ball_nonneg r z x
    have hd := mul_nonneg ht hG
    simp only [Pi.zero_apply]
    linarith

/-- Monotonicity of the least supersolution in the mass: `S_t ⊆ S_{t'}` for `t ≤ t'` since `G ≥ 0`,
so the infimum over the larger family is smaller (Defs/Obstacle.lean, eq:super-solutions). -/
theorem leastSupersolution_anti_time {μ : Measure ℂ} {r : ℝ} {z : ℂ} {t t' : ℝ} (ht : 0 ≤ t)
    (htt' : t ≤ t') {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) r) (hxz : x ≠ z) :
    leastSupersolution μ r z t' x ≤ leastSupersolution μ r z t x := by
  have hsub : supersolutions μ r z t ⊆ supersolutions μ r z t' := by
    rintro w ⟨hc, hl, hb⟩
    refine ⟨hc, hl, fun y hy hyz => ?_⟩
    have hG := greenFunction_ball_nonneg r z y
    have hd := mul_nonneg (sub_nonneg.2 htt') hG
    have e : -t' * greenFunction (ball 0 r) z y
        = -t * greenFunction (ball 0 r) z y - (t' - t) * greenFunction (ball 0 r) z y := by ring
    rw [e]
    linarith [hb y hy hyz]
  unfold leastSupersolution
  refine csInf_le_csInf (bddBelow_supersolutions hx hxz) ?_ (Set.image_mono hsub)
  exact ⟨(fun w : ℂ → ℝ => w x) 0, ⟨0, zero_mem_supersolutions_ball ht, rfl⟩⟩

/-- Odometer comparison in the mass: `u_{t'} ≤ u_t + (t' - t) G` off the pole. -/
theorem odometer_le_add_green {μ : Measure ℂ} {r : ℝ} {z : ℂ} {t t' : ℝ} (ht : 0 ≤ t)
    (htt' : t ≤ t') {x : ℂ} (hx : x ∈ closedBall (0 : ℂ) r) (hxz : x ≠ z) :
    odometer μ r z t' x ≤ odometer μ r z t x + (t' - t) * greenFunction (ball 0 r) z x := by
  have h := leastSupersolution_anti_time (μ := μ) ht htt' hx hxz
  unfold odometer
  have e : t' * greenFunction (ball 0 r) z x
      = t * greenFunction (ball 0 r) z x + (t' - t) * greenFunction (ball 0 r) z x := by ring
  linarith

/-- The odometer vanishes at every point of the disc outside the cluster. -/
theorem odometer_eq_zero_of_not_mem_cluster_ball' {μ : Measure ℂ} {r : ℝ} {z : ℂ} {t : ℝ} (ht : 0 ≤ t)
    {x : ℂ} (hx : x ∈ ball (0 : ℂ) r) (hxΛ : x ∉ cluster μ r z t) : odometer μ r z t x = 0 := by
  have h1 : ¬ (x = z ∨ 0 < odometer μ r z t x) := fun h => hxΛ (mem_cluster_iff.2 ⟨hx, h⟩)
  simp only [not_or, not_lt] at h1
  exact le_antisymm h1.2 (odometer_nonneg ht (ball_subset_closedBall hx) h1.1)

/-! ## Maximum-principle glue -/

/-- The sum rule: if `Δu = μ` on `Λ` (active identity, the restriction of `μ` to `Λ`) and `Δ H ≤ N μ`
on `U ⊇ Λ` with `a N ≤ 1`, then `Δ (u - a H) ≥ 0` on `Λ`. -/
theorem laplacianGE_sub_of_hasLaplacian {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {Λ U : Set ℂ}
    (hΛU : Λ ⊆ U) {u H : ℂ → ℝ} {N : ℕ} {a : ℝ} (ha : 0 ≤ a) (haN : a * N ≤ 1)
    (hu : HasLaplacian u (μ.restrict Λ) 0 Λ) (hH : LaplacianLE H ((N : ℝ≥0∞) • μ) U) :
    LaplacianGE (fun x => u x - a * H x) 0 Λ := by
  have hHΛ : LaplacianLE H ((N : ℝ≥0∞) • μ) Λ := hH.mono_set hΛU
  refine ⟨hu.1.sub (hHΛ.1.smul a), fun φ hφ hφ0 => ?_⟩
  refine ⟨integrable_zero_measure, ?_⟩
  rw [integral_zero_measure]
  have hφμ : Integrable φ μ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hM0 : 0 ≤ ∫ x, φ x ∂μ := integral_nonneg fun x => hφ0 x
  have hres : ∫ x, φ x ∂(μ.restrict Λ) = ∫ x, φ x ∂μ := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hφ.2.2 h))
  obtain ⟨-, -, heq⟩ := hu.2 φ hφ
  rw [integral_zero_measure, sub_zero, hres] at heq
  have hHle := hHΛ.2 φ hφ hφ0 (hφμ.smul_measure (ENNReal.natCast_ne_top N))
  rw [integral_smul_measure, ENNReal.toReal_natCast, smul_eq_mul] at hHle
  have hsplit : ∫ x, (u x - a * H x) * Δ φ x
      = (∫ x, u x * Δ φ x) - a * ∫ x, H x * Δ φ x := by
    have e : (fun x => (u x - a * H x) * Δ φ x) = fun x => u x * Δ φ x - a * (H x * Δ φ x) := by
      funext x; ring
    rw [e, integral_sub (integrable_mul_laplacian_of_test hu.1 hφ)
      ((integrable_mul_laplacian_of_test hHΛ.1 hφ).const_mul a), integral_const_mul]
  rw [hsplit, heq]
  nlinarith [mul_le_mul_of_nonneg_left hHle ha, mul_le_mul_of_nonneg_right haN hM0]

/-- A distributional lower bound `Δw ≥ 0` with continuity gives classical subharmonicity. -/
theorem isSubharmonicOn_of_laplacianGE_zero {U : Set ℂ} (hU : IsOpen U) {w : ℂ → ℝ}
    (hc : ContinuousOn w U) (hw : LaplacianGE w 0 U) : IsSubharmonicOn U w := by
  have hq : HasLaplacian (0 : ℂ → ℝ) 0 0 U := by
    refine ⟨continuous_zero.locallyIntegrable.locallyIntegrableOn _, fun φ _ => ?_⟩
    exact ⟨integrable_zero_measure, integrable_zero_measure, by simp⟩
  have h := Section6.isSubharmonicOn_add_of_laplacianGE (μ := 0) (ν := 0) hU le_rfl hc
    continuous_zero.continuousOn hw hq
  simpa using h

/-- Subharmonicity is invariant under equality on the set (negate and use `IsSuperharmonicOn.congr`). -/
theorem isSubharmonicOn_congr_of_eqOn {U : Set ℂ} {f g : ℂ → ℝ} (hf : IsSubharmonicOn U f)
    (hfg : EqOn f g U) : IsSubharmonicOn U g :=
  IsSuperharmonicOn.congr (g := -f) (g' := -g) hf (fun x hx => by simp [hfg hx])

/-- A point of the closure of a set on which `F` is positive has `F ≥ 0` (continuity at the point). -/
theorem nonneg_of_mem_closure_of_pos {Λ : Set ℂ} {F : ℂ → ℝ} {x : ℂ} (hFx : ContinuousAt F x)
    (hpos : ∀ y ∈ Λ, 0 < F y) (hx : x ∈ closure Λ) : 0 ≤ F x := by
  have := mem_closure_iff_nhdsWithin_neBot.1 hx
  exact ge_of_tendsto (hFx.tendsto.mono_left nhdsWithin_le_nhds)
    (eventually_nhdsWithin_of_forall fun y hy => (hpos y hy).le)

/-! ## Regularity of the least supersolution and the odometer on the unit disc -/

/-- The least supersolution of radius one is continuous on the closed unit disc. -/
theorem leastSupersolution_continuousOn_closedBall_one {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βm βp : ℝ} (hV1 : VolumeGrowth μ 1 βm βp) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {τ : ℝ} (hτ : 0 < τ) :
    ContinuousOn (leastSupersolution μ 1 z τ) (closedBall 0 1) :=
  (leastSupersolution_mem_of_general obstacleLeastSuperharmonicMajorantGeneral_holds
    obstacleCompatibilityShiftStep_holds hμ one_pos hV1 hz hτ).2.1

/-- The odometer of radius one is continuous on the closed unit disc off its pole. -/
theorem odometer_continuousOn_one {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βm βp : ℝ} (hV1 : VolumeGrowth μ 1 βm βp) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {τ : ℝ} (hτ : 0 < τ) :
    ContinuousOn (odometer μ 1 z τ) (closedBall 0 1 \ {z}) :=
  continuousOn_odometer greenFunctionBall one_pos hz
    (leastSupersolution_continuousOn_closedBall_one hμ hV1 hz hτ)

/-- The Green function of the unit disc is continuous on the closed disc off its pole (it is the
odometer minus the least supersolution, divided by the mass). -/
theorem greenFunction_continuousOn_closedBall_one {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {βm βp : ℝ} (hV1 : VolumeGrowth μ 1 βm βp) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {τ : ℝ} (hτ : 0 < τ) :
    ContinuousOn (greenFunction (ball (0 : ℂ) 1) z) (closedBall 0 1 \ {z}) := by
  have hO := odometer_continuousOn_one hμ hV1 hz hτ
  have hL := (leastSupersolution_continuousOn_closedBall_one hμ hV1 hz hτ).mono
    (fun x (hx : x ∈ closedBall (0 : ℂ) 1 \ {z}) => hx.1)
  have hD : ContinuousOn (fun x => (odometer μ 1 z τ x - leastSupersolution μ 1 z τ x) / τ)
      (closedBall 0 1 \ {z}) := (hO.sub hL).div_const τ
  refine hD.congr fun x _ => ?_
  show greenFunction (ball (0 : ℂ) 1) z x = (odometer μ 1 z τ x - leastSupersolution μ 1 z τ x) / τ
  unfold odometer
  rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hτ.ne']

/-! ## The comparison at one time: the odometer lies below the finite barrier -/

/-- **Comparison at one time.** Let `u = odometer μ 1 z τ` and `F = u - κ H`, where `H` is the finite barrier
(nonnegative on `U = B_r(p) ∩ B_1`, continuous off its poles, at least `c` on the sphere away from the poles,
`→ +∞` at the poles, and `ΔH ≤ N μ`). If `u ≤ s G` on the closed comparison set with `s M ≤ κ c` and `κ N ≤ 1`,
then `u ≤ κ H` on `U`: the positive part of `F` is subharmonic on its positivity set (active identity plus the
sum rule), vanishes on the frontier, and the maximum principle `isSubharmonicOn_ball_sdiff_le_of_eventually_lt`
with the removed set `K = {1 ≤ |x|} ∪ T` gives `(F)^+ ≤ η` for every `η > 0`. -/
theorem odometer_le_mul_on_ball {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hV1 : VolumeGrowth μ 1 βm βp) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {τ : ℝ} (hτ : 0 < τ)
    {p : ℂ} {r : ℝ} (hzC : z ∉ closedBall p r)
    {T : Finset ℂ} {H : ℂ → ℝ} {c : ℝ}
    (hTS : ∀ q ∈ T, q ∈ sphere p r ∩ closedBall (0 : ℂ) 1)
    (hpos : ∀ x ∈ ball p r ∩ ball (0 : ℂ) 1, 0 ≤ H x)
    (hHc : ContinuousOn H (ball (0 : ℂ) 1 \ (T : Set ℂ)))
    (hcS : ∀ x ∈ sphere p r ∩ closedBall (0 : ℂ) 1, (∀ q ∈ T, x ≠ q) → c ≤ H x)
    (hTend : ∀ q ∈ T, Tendsto H (𝓝[≠] q) atTop)
    (hLap : LaplacianLE H ((T.card : ℝ≥0∞) • μ) (ball p r ∩ ball (0 : ℂ) 1))
    {κ s M : ℝ} (hκ : 0 < κ) (hκN : κ * (T.card : ℝ) ≤ 1) (hs : 0 ≤ s)
    (hκc : s * M ≤ κ * c)
    (hGM : ∀ x ∈ closedBall p r ∩ ball (0 : ℂ) 1, greenFunction (ball (0 : ℂ) 1) z x ≤ M)
    (hbound : ∀ x ∈ closedBall p r ∩ ball (0 : ℂ) 1,
      odometer μ 1 z τ x ≤ s * greenFunction (ball (0 : ℂ) 1) z x) :
    ∀ x ∈ ball p r ∩ ball (0 : ℂ) 1, odometer μ 1 z τ x ≤ κ * H x := by
  classical
  set U : Set ℂ := ball p r ∩ ball (0 : ℂ) 1 with hUdef
  set F : ℂ → ℝ := fun x => odometer μ 1 z τ x - κ * H x with hFdef
  set Λ : Set ℂ := U ∩ F ⁻¹' Ioi 0 with hΛdef
  set W : Set ℂ := ball (0 : ℂ) 1 \ ((T : Set ℂ) ∪ {z}) with hWdef
  set K : Set ℂ := {x : ℂ | 1 ≤ ‖x‖} ∪ (T : Set ℂ) with hKdef
  have hUopen : IsOpen U := isOpen_ball.inter isOpen_ball
  have hWopen : IsOpen W :=
    isOpen_ball.sdiff ((T.finite_toSet.union (Set.finite_singleton z)).isClosed)
  have hΛU : Λ ⊆ U := inter_subset_left
  have hTU : ∀ q ∈ T, q ∉ ball p r := fun q hq hb => by
    have h1 := (hTS q hq).1
    rw [mem_sphere] at h1
    rw [mem_ball] at hb
    linarith
  have hWsub : W ⊆ ball (0 : ℂ) 1 \ (T : Set ℂ) := fun x hx => ⟨hx.1, fun h => hx.2 (Or.inl h)⟩
  have hUW : U ⊆ W := by
    intro x hx
    refine ⟨hx.2, ?_⟩
    rintro (hxT | hxz)
    · exact hTU x (Finset.mem_coe.1 hxT) hx.1
    · have hxz' : x = z := Set.mem_singleton_iff.1 hxz
      exact hzC (hxz' ▸ ball_subset_closedBall hx.1)
  have hHcW : ContinuousOn H W := hHc.mono hWsub
  have hOW : ContinuousOn (odometer μ 1 z τ) W :=
    (odometer_continuousOn_one hμ hV1 hz hτ).mono fun x hx =>
      ⟨ball_subset_closedBall hx.1, fun h => hx.2 (Or.inr h)⟩
  have hFW : ContinuousOn F W := hOW.sub (continuousOn_const.mul hHcW)
  have hΛopen : IsOpen Λ := (hFW.mono hUW).isOpen_inter_preimage hUopen isOpen_Ioi
  have hF0 : ∀ x ∈ Λ, 0 < F x := fun x hx => hx.2
  -- the positivity set lies in the cluster and the active identity applies
  have hΛsub : Λ ⊆ (ball (0 : ℂ) 1 \ {z}) ∩ cluster μ 1 z τ := by
    intro x hx
    have hxU : x ∈ U := hΛU hx
    have hHx : 0 ≤ H x := hpos x hxU
    have hxz : x ≠ z := fun h => hzC (h ▸ ball_subset_closedBall hxU.1)
    refine ⟨⟨hxU.2, hxz⟩, ?_⟩
    rw [mem_cluster_iff]
    refine ⟨hxU.2, Or.inr ?_⟩
    have hF : F x = odometer μ 1 z τ x - κ * H x := rfl
    have hkH := mul_nonneg hκ.le hHx
    linarith [hF0 x hx]
  have hHL : HasLaplacian (odometer μ 1 z τ) (μ.restrict Λ) 0 Λ :=
    Section6.odometer_hasLaplacian_on_cluster hμ one_pos hV1 hz hτ hΛsub
  have hsum : LaplacianGE F 0 Λ :=
    laplacianGE_sub_of_hasLaplacian hμ hΛU hκ.le hκN hHL hLap
  have hsubF : IsSubharmonicOn Λ F :=
    isSubharmonicOn_of_laplacianGE_zero hΛopen (hFW.mono (hΛU.trans hUW)) hsum
  set g0 : ℂ → ℝ := fun x => max (F x) 0 with hg0def
  have hg0W : ContinuousOn g0 W := continuous_max.comp_continuousOn (hFW.prodMk continuousOn_const)
  have hsubg0 : IsSubharmonicOn Λ g0 :=
    isSubharmonicOn_congr_of_eqOn hsubF (fun x hx => (max_eq_left (le_of_lt (hF0 x hx))).symm)
  -- boundary sign of F on the sphere away from the poles
  have hsphF : ∀ x ∈ sphere p r ∩ ball (0 : ℂ) 1, x ∉ (T : Set ℂ) → F x ≤ 0 := by
    intro x hx hxT
    have hxcb : x ∈ closedBall p r ∩ ball (0 : ℂ) 1 :=
      ⟨mem_closedBall.2 (mem_sphere.1 hx.1).le, hx.2⟩
    have hxT' : ∀ q ∈ T, x ≠ q := fun q hq hxq => hxT (hxq ▸ Finset.mem_coe.2 hq)
    have hHx := hcS x ⟨hx.1, ball_subset_closedBall hx.2⟩ hxT'
    have hu := hbound x hxcb
    have hG := hGM x hxcb
    have hsG : s * greenFunction (ball (0 : ℂ) 1) z x ≤ s * M := mul_le_mul_of_nonneg_left hG hs
    have hκH : κ * c ≤ κ * H x := mul_le_mul_of_nonneg_left hHx hκ.le
    show odometer μ 1 z τ x - κ * H x ≤ 0
    linarith
  -- the frontier of the positivity set carries zero boundary values of the positive part
  have hfrontW : ∀ x ∈ W ∩ frontier Λ, g0 x = 0 := by
    rintro x ⟨hxW, hxfr⟩
    have hxcl : x ∈ closure Λ := hxfr.1
    have hxnot : x ∉ Λ := fun hxΛ => hxfr.2 (by rw [hΛopen.interior_eq]; exact hxΛ)
    have hFx0 : 0 ≤ F x :=
      nonneg_of_mem_closure_of_pos (hFW.continuousAt (hWopen.mem_nhds hxW)) hF0 hxcl
    have hFxle : F x ≤ 0 := by
      by_cases hxU : x ∈ U
      · exact not_lt.1 (fun h => hxnot ⟨hxU, h⟩)
      · have hcl : closure Λ ⊆ closedBall p r :=
          closure_minimal (fun y hy => ball_subset_closedBall (hΛU hy).1) isClosed_closedBall
        have hxs : x ∈ sphere p r := by
          have h1 := hcl hxcl
          rw [mem_closedBall] at h1
          rw [mem_sphere]
          refine le_antisymm h1 (not_lt.1 fun h => hxU ⟨?_, hxW.1⟩)
          rw [mem_ball]
          exact h
        exact hsphF x ⟨hxs, hxW.1⟩ (fun h => hxW.2 (Or.inl h))
    have hF_eq : F x = 0 := le_antisymm hFxle hFx0
    simp only [hg0def, hF_eq, max_self]
  have hgW : ContinuousOn (Λ.indicator g0) W :=
    Section6.continuousOn_indicator_of_zero_frontier hg0W hfrontW
  have hgl : LaplacianGE (Λ.indicator g0) 0 U :=
    Section6.laplacianGE_indicator_of_zero_frontier hUopen hΛopen (hg0W.mono hUW)
      (fun x _ => le_max_right _ _) (fun x hx => hfrontW x ⟨hUW hx.1, hx.2⟩) hsubg0
  set g : ℂ → ℝ := Λ.indicator g0 with hgdef
  -- the removed closed set and the identification of the comparison domain
  have hKc : IsClosed K :=
    (isClosed_le continuous_const continuous_norm).union T.finite_toSet.isClosed
  have hclosedsub : closedBall p r \ K ⊆ W := by
    intro x hx
    obtain ⟨hxcb, hxK⟩ := hx
    have hx1 : ‖x‖ < 1 := by
      by_contra h
      exact hxK (Or.inl (not_lt.1 h))
    have hxT : x ∉ (T : Set ℂ) := fun h => hxK (Or.inr h)
    refine ⟨mem_ball_zero_iff.2 hx1, ?_⟩
    rintro (h | h)
    · exact hxT h
    · exact hzC (Set.mem_singleton_iff.1 h ▸ hxcb)
  have hcont : ContinuousOn g (closedBall p r \ K) := hgW.mono hclosedsub
  have hUK : ball p r \ K = U := by
    ext x
    constructor
    · rintro ⟨hxb, hxK⟩
      refine ⟨hxb, mem_ball_zero_iff.2 ?_⟩
      by_contra h
      exact hxK (Or.inl (not_lt.1 h))
    · rintro ⟨hxb, hx1⟩
      refine ⟨hxb, fun hxK => ?_⟩
      rcases hxK with h | h
      · exact absurd (mem_ball_zero_iff.1 hx1) (not_lt.2 h)
      · exact hTU x (Finset.mem_coe.1 h) hxb
  have hsubU : IsSubharmonicOn (ball p r \ K) g := by
    rw [hUK]
    exact isSubharmonicOn_of_laplacianGE_zero hUopen (hgW.mono hUW) hgl
  have hS'U : ball p r \ K ⊆ U := hUK.subset
  -- pointwise bounds on the comparison set
  have hgle : ∀ x ∈ ball p r \ K, g x ≤ max (F x) 0 := by
    intro x hx
    by_cases hxΛ : x ∈ Λ
    · rw [hgdef, Set.indicator_of_mem hxΛ]
    · rw [hgdef, Set.indicator_of_notMem hxΛ]
      exact le_max_right _ _
  have hFle : ∀ x ∈ ball p r \ K, F x ≤ s * M - κ * H x := by
    intro x hx
    have hxU := hS'U hx
    have hxcb : x ∈ closedBall p r ∩ ball (0 : ℂ) 1 :=
      ⟨ball_subset_closedBall hxU.1, hxU.2⟩
    have hu := hbound x hxcb
    have hG := hGM x hxcb
    have hsG : s * greenFunction (ball (0 : ℂ) 1) z x ≤ s * M := mul_le_mul_of_nonneg_left hG hs
    show odometer μ 1 z τ x - κ * H x ≤ s * M - κ * H x
    linarith
  have hgs : ∀ x ∈ ball p r \ K, g x ≤ s * greenFunction (ball (0 : ℂ) 1) z x := by
    intro x hx
    have hxU := hS'U hx
    have hxcb : x ∈ closedBall p r ∩ ball (0 : ℂ) 1 :=
      ⟨ball_subset_closedBall hxU.1, hxU.2⟩
    have hu := hbound x hxcb
    have hkH := mul_nonneg hκ.le (hpos x hxU)
    have hFx : F x ≤ s * greenFunction (ball (0 : ℂ) 1) z x := by
      show odometer μ 1 z τ x - κ * H x ≤ _
      linarith
    exact (hgle x hx).trans (max_le hFx (mul_nonneg hs (greenFunction_ball_nonneg 1 z x)))
  -- near the removed set: poles and the unit circle
  have hnear : ∀ η : ℝ, 0 < η → ∀ y ∈ K, ∀ᶠ x in 𝓝[ball p r \ K] y, g x < η := by
    intro η hη y hyK
    by_cases hyT : y ∈ (T : Set ℂ)
    · -- a pole: the barrier blows up while the odometer stays bounded
      have hyS : y ∈ sphere p r := (hTS y (Finset.mem_coe.1 hyT)).1
      have hyb : y ∉ ball p r := fun h => by
        have h1 := mem_sphere.1 hyS
        rw [mem_ball] at h
        linarith
      have hne : ball p r \ K ⊆ {y}ᶜ := fun x hx hxy => hyb (hxy ▸ hx.1)
      have hblow : ∀ᶠ x in 𝓝[≠] y, s * M - η < κ * H x :=
        ((hTend y (Finset.mem_coe.1 hyT)).const_mul_atTop hκ).eventually_gt_atTop (s * M - η)
      have hev : ∀ᶠ x in 𝓝[ball p r \ K] y, s * M - η < κ * H x :=
        Filter.Eventually.filter_mono (nhdsWithin_mono y hne) hblow
      filter_upwards [hev, eventually_mem_nhdsWithin] with x hx1 hx2
      have hFx : F x < η := by
        have := hFle x hx2
        linarith
      exact lt_of_le_of_lt (hgle x hx2) (max_lt hFx hη)
    · -- a point of the unit circle: the Green function tends to zero there
      have hyK' : 1 ≤ ‖y‖ := by
        rcases hyK with h | h
        · exact h
        · exact absurd h hyT
      by_cases hy1 : 1 < ‖y‖
      · have hout : ∀ᶠ x in 𝓝 y, 1 < ‖x‖ :=
          (isOpen_lt continuous_const continuous_norm).mem_nhds hy1
        filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds hout,
          eventually_mem_nhdsWithin] with x h1 h2
        exact absurd (mem_ball_zero_iff.1 (hS'U h2).2) (not_lt.2 h1.le)
      · have hynorm : ‖y‖ = 1 := le_antisymm (not_lt.1 hy1) hyK'
        have hyb1 : y ∉ ball (0 : ℂ) 1 := fun h => by
          rw [mem_ball_zero_iff] at h
          linarith
        have hyz : y ≠ z := fun h => by
          have := mem_ball_zero_iff.1 hz
          rw [h] at hynorm
          linarith
        have hyc : y ∈ closedBall (0 : ℂ) 1 \ {z} :=
          ⟨mem_closedBall_zero_iff.2 hynorm.le, fun h => hyz (Set.mem_singleton_iff.1 h)⟩
        have hGy : greenFunction (ball (0 : ℂ) 1) z y = 0 :=
          greenFunction_of_notMem_right hyb1 z
        have hsubS : ball p r \ K ⊆ closedBall (0 : ℂ) 1 \ {z} := fun x hx =>
          ⟨mem_closedBall_zero_iff.2 (mem_ball_zero_iff.1 (hS'U hx).2).le,
            fun h => hzC (Set.mem_singleton_iff.1 h ▸ ball_subset_closedBall (hS'U hx).1)⟩
        have hGc := greenFunction_continuousOn_closedBall_one hμ hV1 hz hτ
        have hGlim : Tendsto (fun x => s * greenFunction (ball (0 : ℂ) 1) z x)
            (𝓝[ball p r \ K] y) (𝓝 0) := by
          have hw := ((hGc y hyc).mono hsubS).tendsto
          have := hw.const_mul s
          rw [hGy, mul_zero] at this
          exact this
        filter_upwards [hGlim.eventually_lt_const hη, eventually_mem_nhdsWithin] with x hx1 hx2
        exact lt_of_le_of_lt (hgs x hx2) hx1
  have key : ∀ η : ℝ, 0 < η → ∀ x ∈ ball p r \ K, g x ≤ η := by
    intro η hη
    -- points of the sphere away from the removed set have `g = 0`
    have hbd : ∀ y ∈ sphere p r, y ∉ K → g y ≤ η := by
      intro y hy _
      have hxnΛ : y ∉ Λ := fun hyΛ => by
        have h1 := (hΛU hyΛ).1
        rw [mem_ball] at h1
        rw [mem_sphere] at hy
        linarith
      rw [hgdef, Set.indicator_of_notMem hxnΛ]
      exact hη.le
    exact fun x hx => isSubharmonicOn_ball_sdiff_le_of_eventually_lt hKc hcont hsubU (hnear η hη) hbd x hx
  intro x hxU
  have hxS' : x ∈ ball p r \ K := by rw [hUK]; exact hxU
  by_contra hcon
  have hFpos : 0 < F x := by
    have : κ * H x < odometer μ 1 z τ x := lt_of_not_ge hcon
    show 0 < odometer μ 1 z τ x - κ * H x
    linarith
  have hxΛ : x ∈ Λ := ⟨hxU, hFpos⟩
  have h1 := key (F x / 2) (by linarith) x hxS'
  have h2 : g x = F x := by
    rw [hgdef, Set.indicator_of_mem hxΛ, hg0def]
    exact max_eq_left hFpos.le
  linarith

/-! ## Stage 1: local persistence away from the old cluster (`eq:local-persistence-zero`) -/

/-- **Stage 1 (local persistence).** Fix `z` in the open unit disc, a time `t > 0` and a point `p` of the
closed unit disc outside the closure of the cluster `Λ_{B_1;z}(t)`. On the event where the small auxiliary
clusters of radius four are small (`hsmall`) and the volume growth holds (`hVR`), there are `r, δ > 0` such
that the cluster at all times `t + s`, `0 ≤ s ≤ δ`, avoids the ball `B_{r/2}(p)`. -/
theorem local_persistence {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hVR : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    (hsmall : ∀ q ∈ closedBall (0 : ℂ) 1, ∀ a : ℝ, 0 < a →
      ∃ σ : ℝ, 0 < σ ∧ closure (cluster μ 4 q σ) ⊆ ball q a)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t) {p : ℂ} (hp : p ∈ closedBall (0 : ℂ) 1)
    (hpK : p ∉ closure (cluster μ 1 z t)) :
    ∃ r : ℝ, 0 < r ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 ≤ s → s ≤ δ →
      ∀ x ∈ ball p (r / 2), x ∉ cluster μ 1 z (t + s) := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isClosed_closure.isOpen_compl p hpK
  set r : ℝ := min (ε / 4) (1 / 16) with hrdef
  have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
  have hr1 : r < 1 / 8 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hfar : ∀ x : ℂ, dist x p < ε → x ∉ cluster μ 1 z t := fun x hx hxc =>
    hball (mem_ball.2 hx) (subset_closure hxc)
  have hzcl : z ∈ cluster μ 1 z t := mem_cluster_iff.2 ⟨hz, Or.inl rfl⟩
  have hzC : z ∉ closedBall p r := fun h =>
    hball (mem_ball.2 (lt_of_le_of_lt (mem_closedBall.1 h) hrε)) (subset_closure hzcl)
  -- the finite auxiliary barrier at radius `r`
  have hsm : ∀ q ∈ sphere p r ∩ closedBall (0 : ℂ) 1,
      ∃ σ : ℝ, 0 < σ ∧ closure (cluster μ 4 q σ) ⊆ ball q (r / 4) :=
    fun q hq => hsmall q hq.2 (r / 4) (by linarith)
  obtain ⟨T, σ, H, -, hTS, hσpos, hHdef, hHpos, -, hHzero, ⟨c, hc, hcS⟩, hTend, hLap⟩ :=
    finite_auxiliary_barrier_boundary_touching μ hμ (hVR 4 (by norm_num)) hp hr0 hr1 hsm
  -- continuity of the barrier off its poles
  have hz4 : ∀ q ∈ T, q ∈ ball (0 : ℂ) 4 := fun q hq =>
    mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 (hTS q hq).2) (by norm_num))
  have hHc : ContinuousOn H (ball (0 : ℂ) 1 \ (T : Set ℂ)) := by
    rw [hHdef]
    refine continuousOn_finsetSum T fun q hq =>
      ((continuousOn_odometer_off_pole hμ (hVR 4 (by norm_num)) (hz4 q hq) (hσpos q hq)).mono ?_)
    intro x hx
    refine ⟨mem_closedBall_zero_iff.2 ?_, fun h => hx.2 ?_⟩
    · have := mem_ball_zero_iff.1 hx.1
      linarith
    · rw [Set.mem_singleton_iff.1 h]
      exact Finset.mem_coe.2 hq
  -- a uniform bound for the Green function on the comparison set
  have hKcpt : IsCompact (closedBall p r ∩ closedBall (0 : ℂ) 1) :=
    (isCompact_closedBall p r).inter_right isClosed_closedBall
  have hKsub : closedBall p r ∩ closedBall (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1 \ {z} := fun x hx =>
    ⟨hx.2, fun h => hzC (Set.mem_singleton_iff.1 h ▸ hx.1)⟩
  obtain ⟨M, hM⟩ := hKcpt.exists_bound_of_continuousOn
    ((greenFunction_continuousOn_closedBall_one hμ (hVR 1 one_pos) hz ht).mono hKsub)
  have hGM : ∀ x ∈ closedBall p r ∩ ball (0 : ℂ) 1, greenFunction (ball (0 : ℂ) 1) z x ≤ M :=
    fun x hx => le_trans (le_abs_self _)
      (by rw [← Real.norm_eq_abs]; exact hM x ⟨hx.1, ball_subset_closedBall hx.2⟩)
  -- the constants `κ` and `δ`
  set N : ℝ := (T.card : ℝ) with hNdef
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set Mp : ℝ := max M 0 with hMpdef
  have hMp0 : 0 ≤ Mp := le_max_right _ _
  set κ : ℝ := 1 / (N + 1) with hκdef
  set δ : ℝ := c / ((N + 1) * (Mp + 1)) with hδdef
  have hκpos : 0 < κ := by
    rw [hκdef]
    exact div_pos one_pos (by linarith)
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos hc (mul_pos (by linarith) (by linarith))
  have hκN : κ * N ≤ 1 := by
    rw [hκdef, div_mul_eq_mul_div, one_mul, div_le_one (by linarith)]
    linarith
  have hκδc : δ * (Mp + 1) = κ * c := by
    rw [hδdef, hκdef]
    field_simp
  have hκcs : ∀ s : ℝ, 0 ≤ s → s ≤ δ → s * M ≤ κ * c := by
    intro s hs hsδ
    have h1 : s * M ≤ s * Mp := mul_le_mul_of_nonneg_left (le_max_left _ _) hs
    have h2 : s * Mp ≤ δ * Mp := mul_le_mul_of_nonneg_right hsδ hMp0
    have h3 : δ * Mp ≤ δ * (Mp + 1) := mul_le_mul_of_nonneg_left (by linarith) hδpos.le
    linarith [hκδc]
  -- the odometer at time `t + s` is controlled by the Green function
  have hbound : ∀ s : ℝ, 0 ≤ s → ∀ x ∈ closedBall p r ∩ ball (0 : ℂ) 1,
      odometer μ 1 z (t + s) x ≤ s * greenFunction (ball (0 : ℂ) 1) z x := by
    intro s hs x hx
    have hxc : x ∈ closedBall p r := hx.1
    have hxz : x ≠ z := fun h => hzC (h ▸ hxc)
    have hxcl : x ∉ cluster μ 1 z t := hfar x (lt_of_le_of_lt (mem_closedBall.1 hxc) hrε)
    have h0 : odometer μ 1 z t x = 0 := odometer_eq_zero_of_not_mem_cluster_ball' ht.le hx.2 hxcl
    have hle := odometer_le_add_green (μ := μ) ht.le (le_add_of_nonneg_right hs)
      (ball_subset_closedBall hx.2) hxz
    have e : t + s - t = s := by ring
    rw [h0, e, zero_add] at hle
    exact hle
  have hLapC : LaplacianLE H ((T.card : ℝ≥0∞) • μ) (ball p r ∩ ball (0 : ℂ) 1) := by
    rw [Nat.cast_smul_eq_nsmul]
    exact hLap
  refine ⟨r, hr0, δ, hδpos, fun s hs0 hsδ x hx hxc => ?_⟩
  have hxball1 : x ∈ ball (0 : ℂ) 1 := (mem_cluster_iff.1 hxc).1
  have hxr : x ∈ ball p r := ball_subset_ball (by linarith) hx
  have hxU : x ∈ ball p r ∩ ball (0 : ℂ) 1 := ⟨hxr, hxball1⟩
  have hxz : x ≠ z := fun h => hzC (h ▸ ball_subset_closedBall hxr)
  have hposu : 0 < odometer μ 1 z (t + s) x := (mem_cluster_iff.1 hxc).2.resolve_left hxz
  have hle := odometer_le_mul_on_ball hμ (hVR 1 one_pos) hz (by linarith : (0 : ℝ) < t + s) hzC
    hTS hHpos hHc hcS hTend hLapC hκpos hκN hs0 (hκcs s hs0 hsδ) hGM (hbound s hs0) x hxU
  have hH0 : H x = 0 := hHzero x ⟨hxU, hx⟩
  rw [hH0, mul_zero] at hle
  linarith

/-! ## Stage 2: compactness and the uniform right-continuity estimate (lines 1230-1253) -/

/-- The closure of a set lies in its Minkowski sum with an open ball. -/
theorem closure_subset_add_ball (A : Set ℂ) {ε : ℝ} (hε : 0 < ε) :
    closure A ⊆ A + ball (0 : ℂ) ε := by
  intro x hx
  obtain ⟨y, hy, hdist⟩ := Metric.mem_closure_iff.1 hx ε hε
  rw [dist_eq_norm] at hdist
  exact ⟨y, hy, x - y, mem_ball_zero_iff.2 hdist, by ring⟩

/-- A finite family of positive reals has a common positive lower bound. -/
theorem exists_pos_le_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i ∈ s, δ ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun i hi => by simp at hi⟩
  | @insert a s _ ih =>
    obtain ⟨δ, hδ, hle⟩ := ih
    refine ⟨min δ (f a), lt_min hδ (hf a), fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi'
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hle i hi')

/-- **Stage 2 (compactness).** On the event of stage 1, for every `ε > 0` there is `δ > 0` such that the closure
of the cluster at all times `t' ∈ [t, t + δ]` lies in the `ε`-neighbourhood of the cluster at time `t`. The
complement of that neighbourhood, inside the closed unit disc, is compact and covered by the stage-1 balls. -/
theorem closure_cluster_small_of_local {μ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ) {βm βp : ℝ}
    (hVR : ∀ R : ℝ, 0 < R → VolumeGrowth μ R βm βp)
    (hsmall : ∀ q ∈ closedBall (0 : ℂ) 1, ∀ a : ℝ, 0 < a →
      ∃ σ : ℝ, 0 < σ ∧ closure (cluster μ 4 q σ) ⊆ ball q a)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) {t : ℝ} (ht : 0 < t) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t' ∈ Icc t (t + δ),
      closure (cluster μ 1 z t') ⊆ cluster μ 1 z t + ball (0 : ℂ) ε := by
  classical
  set A : Set ℂ := cluster μ 1 z t + ball (0 : ℂ) ε with hAdef
  have hAopen : IsOpen A := IsOpen.add_left isOpen_ball
  set L : Set ℂ := closedBall (0 : ℂ) 1 \ A with hLdef
  have hLc : IsCompact L := (isCompact_closedBall _ _).diff hAopen
  -- local persistence at every point of the compact set `L`
  have hloc : ∀ p : ℂ, ∃ ρ δ : ℝ, 0 < ρ ∧ 0 < δ ∧
      (p ∈ L → ∀ s : ℝ, 0 ≤ s → s ≤ δ → ∀ x ∈ ball p ρ, x ∉ cluster μ 1 z (t + s)) := by
    intro p
    by_cases hp : p ∈ L
    · have hpK : p ∉ closure (cluster μ 1 z t) := fun h => hp.2 (closure_subset_add_ball _ hε h)
      obtain ⟨r, hr, δ, hδ, hpers⟩ := local_persistence hμ hVR hsmall hz ht hp.1 hpK
      exact ⟨r / 2, δ, by linarith, hδ, fun _ s hs0 hsδ x hx => hpers s hs0 hsδ x hx⟩
    · exact ⟨1, 1, one_pos, one_pos, fun h => absurd h hp⟩
  choose ρ δ hρ hδ hpers using hloc
  obtain ⟨F, hFL, hFcov⟩ :=
    hLc.elim_nhds_subcover (fun p => ball p (ρ p)) (fun p _ => ball_mem_nhds p (hρ p))
  obtain ⟨δ₀, hδ₀, hle⟩ := exists_pos_le_finset F δ hδ
  refine ⟨δ₀, hδ₀, fun t' ht' => ?_⟩
  intro y hy
  by_contra hyA
  have hcl : cluster μ 1 z t' ⊆ closedBall (0 : ℂ) 1 := fun x hx =>
    ball_subset_closedBall (mem_cluster_iff.1 hx).1
  have hyL : y ∈ L := ⟨closure_minimal hcl isClosed_closedBall hy, hyA⟩
  obtain ⟨p, hpF, hyp⟩ := mem_iUnion₂.1 (hFcov hyL)
  obtain ⟨x, hxball, hxcl⟩ := mem_closure_iff.1 hy (ball p (ρ p)) isOpen_ball hyp
  have hs0 : 0 ≤ t' - t := by linarith [ht'.1]
  have hsδ : t' - t ≤ δ p := by linarith [ht'.2, hle p hpF]
  have hxnot := hpers p (hFL p hpF) (t' - t) hs0 hsδ x hxball
  have e : t + (t' - t) = t' := by ring
  rw [e] at hxnot
  exact hxnot hxcl

/-- **Proposition 5.2, boundary-touching step, from the numbered predecessor `h71` and the explicit field inputs
of the LQG measure.** The almost-sure event is the small-auxiliary-cluster event of `SmallAuxiliaryClusterEvent.lean`
together with the volume growth at every radius, which follows from the LQG chain `LQGVolumeGrowthAllScalesStmt`
(with the Weyl-scaling, existence and non-atomicity field inputs). The conclusion is `ClusterBoundaryTouchingRightContinuityStep`
(GRAPH G12); the proof is conditional on the field inputs named in the hypotheses. -/
theorem clusterBoundaryTouching_of_fields (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ClusterBoundaryTouchingRightContinuityStep.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have hsm := ae_radiusFour_cluster_small_all_centres h71 (hAff Ω P hC hcirc)
    (hCC Ω P γ α₀ hC hcirc) hγ hγ2 hα hGFF hμ
  have hI2 : LQGVolumeGrowthAllScalesStmt.{u} :=
    lqgVolumeGrowthAllScalesStmt_of_literature hDG hAff
      (fun Ω _ P γ hC hcirc => hCC Ω P γ 0 hC hcirc) hW hE hN
  have hA : 0 < (2 - γ) ^ 2 / 2 := div_pos (pow_pos (by linarith) 2) two_pos
  have hB : 0 < γ * (lqgQ γ - α₀) := mul_pos hγ (by linarith)
  have hβp : 0 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) / 2 :=
    div_pos (lt_min hA hB) two_pos
  have hβp' : min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) / 2 <
      min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) := by
    linarith [lt_min hA hB]
  have hβm : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) <
      max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1 := by linarith
  have hvol := ae_isLocallyFiniteMeasure_volumeGrowth_of_exponents hI2 hγ hγ2 hα hβp hβp' hβm
    hGFF hμ
  filter_upwards [hsm, hvol] with ω hω1 hω2
  intro z hz t ht _
  refine ⟨1, one_pos, fun ε hε => ?_⟩
  obtain ⟨δ, hδ, hcl⟩ := closure_cluster_small_of_local hω2.1 hω2.2 hω1
    (ball_subset_ball (by norm_num) hz) ht hε.1
  exact ⟨δ, hδ, hcl⟩

/-- **Proposition 5.2 (`ClusterContinuityStmt`) from the staged inputs.** -/
theorem clusterContinuity_of_staged (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (h33 : ClusterMonotoneStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBounds P γ hC hcirc)
    (hAff : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hW : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureWeylScaling P γ 0 hC hcirc)
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureExistence P γ 0 hC hcirc)
    (hN : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ClusterContinuityStmt.{u} :=
  clusterContinuity_of_boundaryTouching h71 h33 h72
    (clusterBoundaryTouching_of_fields h71 hDG hAff hCC hW hE hN)

end HarmonicBalls

#print axioms HarmonicBalls.local_persistence
#print axioms HarmonicBalls.closure_cluster_small_of_local
#print axioms HarmonicBalls.clusterBoundaryTouching_of_fields
#print axioms HarmonicBalls.clusterContinuity_of_staged
