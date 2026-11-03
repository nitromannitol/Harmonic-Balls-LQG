import HarmonicBalls.Draft.SectionA
import HarmonicBalls.Draft.Section2

/-!
# Appendix A, Phase B: shared notions, shared steps and glue lemmas

Carving of the proofs of Appendix A (sec:obstacle-appendix, lines 3522-3906) of the corrected draft of
Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795). This file holds what
several of the Lemmas A.1-A.6 share: the classical (mean-value) notion of a superharmonic function used by the
printed proofs, the potential-theory steps they cite, and small proved glue lemmas.

## Notions

* `IsSuperharmonicOn U g`: `g : ℂ → ℝ` is superharmonic on `U` in the classical sense of Armitage–Gardiner
  (AG01, Chapter 3), restricted to finite-valued functions: lower semicontinuous on `U` and
  `M(g; x, r) ≤ g(x)` for every closed disc `closedBall x r ⊆ U`, with `M` the circle average
  (`Real.circleAverage`). The circle integrability conjunct is automatic for finite-valued superharmonic
  functions (the lower integral is `≤ g(x) < ∞` and `g` is bounded below on the circle), so the notion agrees
  with the classical definition on finite-valued functions. The printed proofs of Lemmas A.1 and A.2 work in this class
  ("admissible superharmonic functions need only be lower semicontinuous", line 3598).
* `IsSubharmonicOn U g := IsSuperharmonicOn U (-g)`.

## Shared steps (each a `def ... : Prop`; difficulty in brackets)

* `SuperharmonicOfLaplacianLEStep` — Weyl's lemma, superharmonic form (I4): a continuous `w` with
  `Δw ≤ 0` distributionally on open `U` is classically superharmonic on `U`. [medium-hard, 2 rounds:
  mollification, the mean-value formula for smooth functions, locally uniform limits]
* `LaplacianLEOfSuperharmonicStep` — converse: a continuous classically superharmonic `w` has `Δw ≤ 0` on `U`.
  [medium, 1-2 rounds: `∫ (M_r w - w) φ = ∫ w (M_r φ - φ)` and `(M_r φ - φ)/r² → Δφ/4`]
* `HasLaplacianOfLaplacianLEGEStep` — `Δw ≤ 0` and `Δw ≥ 0` on open `U` give `Δw = 0` on `U` (all test functions,
  not only nonnegative ones). [easy-medium, 1 round: a smooth cut-off `χ = 1` on `tsupport φ`]
* `GreenPotentialBallContinuousStep` — property 1 of `q_{B_R}` (line 3538): continuity on `closedBall 0 R`
  under the volume growth condition ("same argument as Prop 2.5", line 3542). [medium-hard, 2 rounds]
* `GreenPotentialBallLaplacianStep` — property 2 of `q_{B_R}` (line 3539): `Δ q_{B_R} = -μ` on `B_R`
  (AG01 Thm 4.3.8, line 3543). [hard, 2-3 rounds: symmetry of `G_{B_R}`, Prop 2.3, Fubini]
* `ObstacleTendstoAtBotStep` — the obstacle `β_t` tends to `-∞` at the pole (`β_t(z) = -∞` in the paper, line
  3551). Used for the openness of `Λ_t` at the pole and in the repair G2 of Lemma A.1, Step 3. [easy, ≤ 1 round:
  `log_div_le_greenFunction`, Proofs/Potential/GreenPositivity.lean]

Properties 3 (zero boundary values of `q_{B_R}`) and 4 (positivity) of line 3540-3541: 3 is proved below
(`greenPotentialBall_eq_zero_of_notMem`); 4 is not used by Lemmas A.1-A.6.

## Proved glue

`LaplacianLE.congr_eqOn`, `LaplacianLE.mono_set`, `LaplacianGE.of_laplacianLE_neg`,
`continuousOn_greenFunction_ball_of_stmt` (from Prop 2.3, `GreenFunctionBallStmt`), `continuousOn_obstacle`,
`greenPotentialBall_eq_zero_of_notMem`, `obstacle_eq_zero_of_notMem`.
-/

namespace HarmonicBalls

open MeasureTheory Metric Filter Topology Set Laplacian

/-! ## Classical superharmonic and subharmonic functions -/

/-- `g` is *superharmonic on `U`* in the classical sense (Armitage–Gardiner, *Classical potential theory*,
Chapter 3; local characterizations: AG01 Thm 3.2.2, cited at line 3672), restricted to finite-valued functions: `g` is lower semicontinuous on `U` and satisfies the
super-mean-value inequality `M(g; x, r) ≤ g(x)` for every closed disc `closedBall x r ⊆ U`, where `M(g; x, r)` is
the average of `g` over the circle `∂B_r(x)`. The circle integrability conjunct is a consequence of the
inequality for finite-valued lower semicontinuous `g`. This is the class of "admissible superharmonic functions"
of eq:lsc-leastsuperharmonic (line 3594), which "need only be lower semicontinuous" (line 3598). -/
def IsSuperharmonicOn (U : Set ℂ) (g : ℂ → ℝ) : Prop :=
  LowerSemicontinuousOn g U ∧
    ∀ x ∈ U, ∀ r : ℝ, 0 < r → closedBall x r ⊆ U →
      CircleIntegrable g x r ∧ Real.circleAverage g x r ≤ g x

/-- `g` is *subharmonic on `U`* in the classical sense: `-g` is superharmonic on `U`. -/
def IsSubharmonicOn (U : Set ℂ) (g : ℂ → ℝ) : Prop :=
  IsSuperharmonicOn U (-g)

/-! ## Shared steps -/

/-- **Shared step (Weyl's lemma, superharmonic form; I4).** A function `w` continuous on an open set `U` with
`Δw ≤ 0` on `U` in the distributional sense (line 326, `LaplacianLE w 0 U`) is superharmonic on `U` in the
classical sense. This is how the printed proofs pass from the supersolutions of eq:shifted-supersolutions
(line 3556, defined with `Δw ≤ 0`) to the superharmonic functions of AG01 (lines 3594-3600, 3666, 3672).
Route: mollify (`w * ρ_ε` is smooth with `Δ ≤ 0` on `U_ε`), apply the mean-value formula
`d/dr M(u; x, r) = (2πr)⁻¹ ∫_{B_r(x)} Δu` for smooth `u`, and let `ε → 0` (locally uniform convergence).
Difficulty: medium-hard (2 rounds). -/
def SuperharmonicOfLaplacianLEStep : Prop :=
  ∀ (U : Set ℂ) (w : ℂ → ℝ), IsOpen U → ContinuousOn w U → LaplacianLE w 0 U → IsSuperharmonicOn U w

/-- **Shared step (converse of Weyl's lemma).** A function `w` continuous and classically superharmonic on an
open set `U` satisfies `Δw ≤ 0` on `U` in the distributional sense. Used to put the functions built in the printed
proofs (the lower semicontinuous infimum `f_t` of Lemma A.1, line 3600) back into `S̃(t)`.
Route: for a nonnegative test function `φ` and small `r`, `∫ w (M_r φ - φ) = ∫ (M_r w - w) φ ≤ 0`, and
`(M_r φ - φ)/r² → Δφ/4` uniformly. Difficulty: medium (1-2 rounds). -/
def LaplacianLEOfSuperharmonicStep : Prop :=
  ∀ (U : Set ℂ) (w : ℂ → ℝ), IsOpen U → ContinuousOn w U → IsSuperharmonicOn U w → LaplacianLE w 0 U

/-- **Shared step.** On an open set `U`, `Δw ≤ 0` and `Δw ≥ 0` (tested against nonnegative test functions) give
`Δw = 0` against all test functions (`HasLaplacian w 0 0 U`). Used for the conclusion `Δ ṽ_t = 0` on `Λ_t` of
Lemma A.2 (line 3654). Route: for a test function `φ`, choose a smooth cut-off `0 ≤ χ ≤ 1` with `χ = 1` on
`tsupport φ` and `tsupport χ ⊆ U` compact; test with `C χ ± φ ≥ 0`. Difficulty: easy-medium (1 round). -/
def HasLaplacianOfLaplacianLEGEStep : Prop :=
  ∀ (U : Set ℂ) (w : ℂ → ℝ), IsOpen U → LaplacianLE w 0 U → LaplacianGE w 0 U → HasLaplacian w 0 0 U

/-- **Shared step (property 1 of `q_{B_R}`, line 3538).** Under the volume growth condition (eq:volume-growth,
line 3526) the potential `q_{B_R}` (eq:expected-exit-time, line 3532) is continuous on `closedBall 0 R`. The paper
asserts Hölder continuity "by the same argument outlined in the proof of Proposition 2.5" (line 3542); only
continuity is used in Appendix A. Route: the upper bound `μ(B_r(x)) ≤ r^{β⁺}` makes the logarithmic singularity of
`G_{B_R}(·, x)` uniformly integrable; `G_{B_R}(y, x) → 0` as `x → ∂B_R`. Difficulty: medium-hard (2 rounds). -/
def GreenPotentialBallContinuousStep : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
    ContinuousOn (greenPotentialBall μ R) (closedBall 0 R)

/-- **Shared step (property 2 of `q_{B_R}`, line 3539).** Under the volume growth condition, `Δ q_{B_R} = -μ` on
`B_R` in the distributional sense (`HasLaplacian q 0 μ (B_R)`); in particular `q_{B_R}` is superharmonic. The paper
cites AG01 Thm 4.3.8 (line 3543). Route: symmetry `G_{B_R}(y, x) = G_{B_R}(x, y)`, `ΔG_{B_R}(y, ·) = -δ_y`
(Prop 2.3, `GreenFunctionBallStmt`) and Fubini. Difficulty: hard (2-3 rounds). -/
def GreenPotentialBallLaplacianStep : Prop :=
  ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → ∀ R βminus βplus : ℝ, 0 < R → VolumeGrowth μ R βminus βplus →
    HasLaplacian (greenPotentialBall μ R) 0 μ (ball 0 R)

/-- **Shared step (the obstacle at the pole).** If `q_{B_R}` is continuous on the closed ball, the obstacle
`β_t = -t G_{B_R}(z, ·) + q_{B_R}` tends to `-∞` at the pole `z` (the paper's value `β_t(z) = -∞`, line 3551).
Used for the openness of `Λ_t` at the pole (Lemma A.2, Step 1, line 3658) and in the repair G2 of Lemma A.1,
Step 3 (lines 3626-3628). Route: `G_{B_R}(z, x) ≥ (2π)⁻¹ log (r / |x - z|)` near `z`
(`log_div_le_greenFunction`, Proofs/Potential/GreenPositivity.lean) and `q_{B_R}` bounded near `z`.
Difficulty: easy (≤ 1 round). -/
def ObstacleTendstoAtBotStep : Prop :=
  ∀ (μ : Measure ℂ) (R : ℝ) (z : ℂ) (t : ℝ), 0 < R → z ∈ ball (0 : ℂ) R → 0 < t →
    ContinuousOn (greenPotentialBall μ R) (closedBall 0 R) →
    Tendsto (obstacle μ R z t) (𝓝[≠] z) atBot

/-! ## Glue: distributional Laplacians -/

/-- The Laplacian of a function vanishes outside its topological support. -/
theorem laplacian_eq_zero_of_notMem_tsupport {φ : ℂ → ℝ} {x : ℂ} (hx : x ∉ tsupport φ) : Δ φ x = 0 := by
  rw [notMem_tsupport_iff_eventuallyEq] at hx
  rw [(InnerProductSpace.laplacian_congr_nhds hx).eq_of_nhds]
  have : (0 : ℂ → ℝ) = fun _ => (0 : ℝ) := rfl
  rw [this, InnerProductSpace.laplacian_const]
  rfl

/-- `Δw ≤ μ` on `U` only depends on the values of `w` on `U`. -/
theorem LaplacianLE.congr_eqOn {w w' : ℂ → ℝ} {μ : Measure ℂ} {U : Set ℂ} (h : LaplacianLE w μ U)
    (hU : MeasurableSet U) (heq : EqOn w w' U) : LaplacianLE w' μ U := by
  refine ⟨h.1.congr ((ae_restrict_iff' hU).2 (Eventually.of_forall heq)), fun φ hφ hφ0 hφμ => ?_⟩
  have hfun : (fun x => w' x * Δ φ x) = fun x => w x * Δ φ x := by
    funext x
    by_cases hx : x ∈ U
    · rw [heq hx]
    · rw [laplacian_eq_zero_of_notMem_tsupport (fun hx' => hx (hφ.2.2 hx')), mul_zero, mul_zero]
  rw [hfun]
  exact h.2 φ hφ hφ0 hφμ

/-- `Δw ≤ μ` on `U` implies `Δw ≤ μ` on every `V ⊆ U`. -/
theorem LaplacianLE.mono_set {w : ℂ → ℝ} {μ : Measure ℂ} {U V : Set ℂ} (h : LaplacianLE w μ U) (hVU : V ⊆ U) :
    LaplacianLE w μ V :=
  ⟨h.1.mono_set hVU, fun φ hφ hφ0 hφμ => h.2 φ ⟨hφ.1, hφ.2.1, hφ.2.2.trans hVU⟩ hφ0 hφμ⟩

/-- `Δ(-w) ≤ 0` implies `Δw ≥ 0`. -/
theorem LaplacianGE.of_laplacianLE_neg {w : ℂ → ℝ} {U : Set ℂ} (h : LaplacianLE (-w) 0 U) :
    LaplacianGE w 0 U := by
  refine ⟨by simpa using h.1.neg, fun φ hφ hφ0 => ⟨integrable_zero_measure, ?_⟩⟩
  have h2 := h.2 φ hφ hφ0 integrable_zero_measure
  simp only [integral_zero_measure, Pi.neg_apply, neg_mul, integral_neg] at h2 ⊢
  linarith

/-! ## Glue: the Green function of a ball and the obstacle -/

/-- Continuity of `G_{B_R}(z, ·)` on `closedBall 0 R \ {z}`, from Proposition 2.3 (smoothness off the pole and
zero boundary values). -/
theorem continuousOn_greenFunction_ball_of_stmt (h23 : GreenFunctionBallStmt) {R : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) : ContinuousOn (greenFunction (ball 0 R) z) (closedBall 0 R \ {z}) := by
  obtain ⟨-, -, hbd, hsmooth⟩ := h23 R hR z hz
  intro x hx
  by_cases hxb : x ∈ ball (0 : ℂ) R
  · have hopen : IsOpen (ball (0 : ℂ) R \ {z}) := isOpen_ball.sdiff isClosed_singleton
    exact ((hsmooth.continuousOn.continuousAt (hopen.mem_nhds ⟨hxb, hx.2⟩))).continuousWithinAt
  · have hxs : x ∈ sphere (0 : ℂ) R := by
      rw [← closedBall_sdiff_ball]; exact ⟨hx.1, hxb⟩
    obtain ⟨hx0, htend⟩ := hbd x hxs
    have hsub : closedBall (0 : ℂ) R \ {z} ⊆ ball 0 R ∪ sphere 0 R := by
      intro y hy
      by_cases hyb : y ∈ ball (0 : ℂ) R
      · exact Or.inl hyb
      · exact Or.inr (by rw [← closedBall_sdiff_ball]; exact ⟨hy.1, hyb⟩)
    refine ContinuousWithinAt.mono ?_ hsub
    rw [ContinuousWithinAt, hx0, nhdsWithin_union]
    refine htend.sup ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact ((hbd y hy).1).symm

/-- Zero boundary values of `q_{B_R}` (property 3, line 3540): `q_{B_R}(x) = 0` for `x ∉ B_R`. -/
theorem greenPotentialBall_eq_zero_of_notMem {μ : Measure ℂ} {R : ℝ} {x : ℂ} (hx : x ∉ ball (0 : ℂ) R) :
    greenPotentialBall μ R x = 0 := by
  simp [greenPotentialBall, greenFunction_of_notMem_right hx]

/-- The obstacle vanishes off `B_R`, in particular on `∂B_R`. -/
theorem obstacle_eq_zero_of_notMem {μ : Measure ℂ} {R t : ℝ} {z x : ℂ} (hx : x ∉ ball (0 : ℂ) R) :
    obstacle μ R z t x = 0 := by
  simp [obstacle, greenFunction_of_notMem_right hx, greenPotentialBall_eq_zero_of_notMem hx]

/-- Continuity of the obstacle `β_t` on `closedBall 0 R \ {z}`, given the continuity of `q_{B_R}`. -/
theorem continuousOn_obstacle (h23 : GreenFunctionBallStmt) {μ : Measure ℂ} {R t : ℝ} (hR : 0 < R) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) R) (hq : ContinuousOn (greenPotentialBall μ R) (closedBall 0 R)) :
    ContinuousOn (obstacle μ R z t) (closedBall 0 R \ {z}) :=
  (continuousOn_const.mul (continuousOn_greenFunction_ball_of_stmt h23 hR hz)).add (hq.mono sdiff_subset)

end HarmonicBalls
