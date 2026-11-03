import Mathlib
import HarmonicBalls.Defs.Brownian
import HarmonicBalls.Defs.LQG

/-! # Liouville Brownian motion

Section 2.3 of Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795),
paper/lqg_harmonic_ball-corrected.tex, lines 515-560: Liouville Brownian motion (LBM), the expected exit time of LBM
(Prop. 2.5, prop:lbm-exit-time, line 524), reflected LBM in a square and its heat kernel
(eq:defining-property-of-kernel, lines 546-548; Prop. 2.6, prop:lbm-continuity, line 554).

LBM is planar Brownian motion `𝓑`, sampled independently of the field `h`, run with the *LQG clock*
`F(t) = lim_{ε → 0} ∫_0^t ε^{γ²/2} e^{γ h_ε(𝓑_s)} ds`: `𝓑^{LBM}_t = 𝓑_{F⁻¹(t)}` (line 517).
All objects here are *quenched*: the circle averages `hε ε z = h_ε(z)` of one realization of the field are fixed,
and probabilities are taken over the Brownian path only. Since `𝓑` is independent of `h`, these are the conditional
probabilities `P[· | h]` of line 547.

## The LQG clock (`lqgClockApprox`, `IsLQGClock`)

* Berestycki 2015 (*Diffusion in planar Liouville quantum gravity*, AIHP 51(3); arXiv:1301.3356; pages of the
  arXiv version, likewise below): for a zero-boundary GFF `h` on a domain `D`, a fixed starting point and the
  circle-average approximations `h_ε` with exactly the normalization `ε^{γ²/2} e^{γ h_ε}`
  (`h̄_ε = γ h_ε + (γ²/2) log ε`, Section 2, p. 6), Definition 1.1 and Theorem 1.2 (p. 4) give convergence of
  the clock *almost surely under the joint law of `(h, 𝓑)`*, up to the exit time of `D`; the proof (Section 2,
  p. 6) establishes it along the dyadic scales `ε = 2^{-k}` only. Section 3 (pp. 9-16) proves that the limit is
  a.s. continuous and strictly increasing.
* Garban-Rhodes-Vargas 2016 (*Liouville Brownian motion*, Ann. Probab. 44(4); arXiv:1301.2876): for a massive GFF on
  `ℝ²` with a white-noise cutoff `X_n`, Theorem 2.7 (pp. 10-11) proves that, almost surely in the field, there is a
  unique positive continuous additive functional `F` with Revuz measure the Liouville measure (item 1) such that,
  *for all starting points `x` simultaneously* and all `T > 0`, the approximating clocks converge to `F` *in
  `P^𝓑_x`-probability, uniformly on `[0, T]`* (item 2); `F` is `P^𝓑_x`-a.s. strictly increasing (item 3) with
  `F(t) → ∞` (item 4). Definition 2.17 (p. 24) defines LBM as `𝓑_{F⁻¹(t)}`.

`IsLQGClock Q γ hε x F` adopts the weakest of these modes, which is implied by both: under the path law `Q x`, the
approximations `∫_0^t ε^{γ²/2} e^{γ hε ε (b s)} ds` at `ε = 2^{-k}` converge to `F b t` in probability, uniformly
on every `[0, T]` (Berestycki's a.s. dyadic convergence gives it for a.e. field by Fubini, since the limit is
continuous and nondecreasing; GRV's mode is the same with a different regularization). The path law `Q` is planar
Brownian motion (`planarBrownianMotion`) or reflected Brownian motion in a square (`reflectedPlanarBrownianMotion`).

## Time change and LBM (`IsTimeChangeClock`, `clockInverse`, `liouvilleBrownianPath`)

`clockInverse f t = inf {s ≥ 0 : f s > t}` is the right-continuous inverse used by Berestycki (eq. (2), p. 3). On
the a.s. event `IsTimeChangeClock (F b)` (`F` continuous, strictly increasing, `F 0 = 0`, `F → ∞`; GRV Theorem 2.7
(3)-(4)) it is the inverse function of `F b`, and `liouvilleBrownianPath F b t = b (F⁻¹ t)` is the LBM path.

## Exit times (`pathExitTime`, `lbmExitTime`, `expectedLBMExitTime`)

The exit time of LBM from `O` is the first time its path leaves `O` (the formula of MarkovProcess's
`ContinuousPath.exitTime`); the expected exit time of LBM from `O` started at `x` (Prop. 2.5, line 526) is its
`planarBrownianMotion x`-expectation in `[0, ∞]`.

## Reflected Brownian motion and reflected LBM in a square (`closedSquare`, `squareFold`)

Reflected (Neumann) Brownian motion in the closed square `K = [a₁, a₁ + L] × [a₂, a₂ + L]` started from `x ∈ K` is the
image of planar Brownian motion started from `x` under the folding map of `ℂ` onto `K`, which folds each coordinate
by the triangle wave `u ↦ arccos (cos (π u)) / π` (reflected Brownian motion on an interval is folded Brownian
motion; the coordinates are independent). Reflected LBM in `K` (line 545) is reflected Brownian motion run with
the LQG clock of the reflected path.

## Heat kernel (`IsLBMHeatKernel`)

eq:defining-property-of-kernel (line 547) with correction [C5] (~/paper-fleets/hb/CORRECTIONS-PROPOSED.md):
`P[𝓑_t^x ∈ dy | h] = p^K_t(x, y) μ_h(dy)` on `K`. The printed reference measure `dy` cannot be right, since the law
of LBM at a fixed time is absolutely continuous with respect to `μ_h`, which is singular with respect to Lebesgue
measure (line 92): the Liouville heat kernel is a density with respect to the Liouville measure
(Garban-Rhodes-Vargas, *On the heat kernel and the Dirichlet form of Liouville Brownian motion*, EJP 19 (2014),
no. 96, Theorem 17 (Theorem 4 of the introduction); arXiv:1302.6050). Kigami 2019 (Mem. AMS 259(1250), Theorem 13.1,
cited at line 557) constructs the time change of reflected Brownian motion on `[0,1]²` by a Liouville measure and its
jointly continuous heat kernel with respect to that measure.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory MarkovProcess Filter Topology Set
open scoped ENNReal NNReal

/-! ### The LQG clock -/

/-- The approximating LQG clock `∫_0^t ε^{γ²/2} e^{γ h_ε(b_s)} ds` of a path `b` (line 517; Berestycki 2015,
Section 2, p. 6), where `hε ε z = h_ε(z)` is the circle average of the field. -/
noncomputable def lqgClockApprox (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) (b : ContinuousPath ℂ) (t : ℝ≥0) : ℝ :=
  ∫ s in (0 : ℝ)..(t : ℝ), ε ^ (γ ^ 2 / 2) * Real.exp (γ * hε ε (b s.toNNReal))

/-- `IsLQGClock Q γ hε x F`: `F` is the *LQG clock* (line 517) of the path law `Q x` (planar or reflected Brownian
motion started from `x`) for the field with circle averages `hε`: for every `T ≥ 0` and `η > 0`,
`Q x {b : ∃ t ≤ T, |∫_0^t ε^{γ²/2} e^{γ h_ε(b_s)} ds - F b t| ≥ η} → 0` along `ε = 2^{-k}`, i.e. convergence in
`Q x`-probability, uniformly on `[0, T]` (Garban-Rhodes-Vargas 2016, Theorem 2.7 (2), pp. 10-11; implied by the
a.s. dyadic convergence of Berestycki 2015, Theorem 1.2, p. 4, and Section 2, p. 6). Intended for `γ ∈ (0, 2)`. -/
def IsLQGClock (Q : Kernel ℂ (ContinuousPath ℂ)) (γ : ℝ) (hε : ℝ → ℂ → ℝ) (x : ℂ)
    (F : ContinuousPath ℂ → ℝ≥0 → ℝ) : Prop :=
  ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
    Tendsto (fun k : ℕ => Q x {b | ∃ t ≤ T, η ≤ |lqgClockApprox γ hε (dyadicScale k) b t - F b t|})
      atTop (𝓝 0)

/-- `IsTimeChangeClock f`: `f` is a continuous strictly increasing clock with `f 0 = 0` and `f t → ∞`, so that
`t ↦ b (f⁻¹ t)` is a time change of a path `b` with infinite lifetime. The LQG clock has these properties almost
surely (Garban-Rhodes-Vargas 2016, Theorem 2.7 (3)-(4), p. 11; Berestycki 2015, Section 3, p. 16). -/
structure IsTimeChangeClock (f : ℝ≥0 → ℝ) : Prop where
  /-- The clock starts at `0`. -/
  map_zero : f 0 = 0
  /-- The clock is continuous. -/
  continuous : Continuous f
  /-- The clock is strictly increasing. -/
  strictMono : StrictMono f
  /-- The clock tends to `∞` (infinite lifetime). -/
  tendsto_atTop : Tendsto f atTop atTop

/-! ### Liouville Brownian motion -/

/-- The right-continuous inverse `f⁻¹(t) = inf {s ≥ 0 : f s > t}` of a clock (Berestycki 2015, eq. (2), p. 3). For an
`IsTimeChangeClock` it is the inverse function of `f`. -/
noncomputable def clockInverse (f : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ≥0 :=
  sInf {s | (t : ℝ) < f s}

/-- The *Liouville Brownian motion path* `t ↦ b (F⁻¹(t))`: the path `b` run with the clock `F b` (line 517;
Garban-Rhodes-Vargas 2016, Definition 2.17, p. 24). Under `planarBrownianMotion x` with `F` the LQG clock it is
γ-LBM started from `x`; under `reflectedPlanarBrownianMotion a L x` it is γ-LBM reflected in the square
`closedSquare a L` (line 545). -/
noncomputable def liouvilleBrownianPath (F : ContinuousPath ℂ → ℝ≥0 → ℝ) (b : ContinuousPath ℂ) (t : ℝ≥0) : ℂ :=
  b (clockInverse (F b) t)

/-! ### Exit times -/

/-- The first time `inf {t ≥ 0 : f t ∉ U} ∈ [0, ∞]` at which a (not necessarily continuous) path `f` leaves `U`; the
formula of MarkovProcess's `ContinuousPath.exitTime`. -/
noncomputable def pathExitTime {α : Type*} (U : Set α) (f : ℝ≥0 → α) : ℝ≥0∞ :=
  sInf {s : ℝ≥0∞ | ∃ t : ℝ≥0, s = (t : ℝ≥0∞) ∧ f t ∉ U}

/-- The *exit time of Liouville Brownian motion* from `O`: the first time the LBM path `t ↦ b (F⁻¹(t))` leaves `O`
(Prop. 2.5, line 526). -/
noncomputable def lbmExitTime (F : ContinuousPath ℂ → ℝ≥0 → ℝ) (O : Set ℂ) (b : ContinuousPath ℂ) : ℝ≥0∞ :=
  pathExitTime O (liouvilleBrownianPath F b)

/-- The *expected exit time of Liouville Brownian motion* from `O` started at `x` (Prop. 2.5, line 526), for the clock
`F` (`IsLQGClock planarBrownianMotion γ hε x F`): `E_x[τ^{LBM}_O] ∈ [0, ∞]`. -/
noncomputable def expectedLBMExitTime (F : ContinuousPath ℂ → ℝ≥0 → ℝ) (O : Set ℂ) (x : ℂ) : ℝ≥0∞ :=
  ∫⁻ b, lbmExitTime F O b ∂(planarBrownianMotion x)

/-! ### Reflected Brownian motion in a square -/

/-- The closed axis-parallel square `[a₁, a₁ + L] × [a₂, a₂ + L]` with lower-left corner `a = a₁ + i a₂` and side
length `L` (line 545). -/
def closedSquare (a : ℂ) (L : ℝ) : Set ℂ :=
  Icc a.re (a.re + L) ×ℂ Icc a.im (a.im + L)

/-- The triangle wave `u ↦ arccos (cos (π u)) / π`, the distance from `u` to `2ℤ`: it folds `ℝ` onto `[0, 1]`, is the
identity on `[0, 1]`, even and `2`-periodic. -/
noncomputable def unitIntervalFold (u : ℝ) : ℝ :=
  Real.arccos (Real.cos (Real.pi * u)) / Real.pi

/-- The folding map of `ℂ` onto `closedSquare a L`: each coordinate is folded onto its side by the triangle wave. -/
noncomputable def squareFold (a : ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  ⟨a.re + L * unitIntervalFold ((z.re - a.re) / L), a.im + L * unitIntervalFold ((z.im - a.im) / L)⟩

theorem continuous_unitIntervalFold : Continuous unitIntervalFold := by
  unfold unitIntervalFold
  fun_prop

theorem continuous_squareFold (a : ℂ) (L : ℝ) : Continuous (squareFold a L) := by
  have h1 : Continuous fun z : ℂ => a.re + L * unitIntervalFold ((z.re - a.re) / L) :=
    continuous_const.add (continuous_const.mul
      (continuous_unitIntervalFold.comp ((Complex.continuous_re.sub continuous_const).div_const _)))
  have h2 : Continuous fun z : ℂ => a.im + L * unitIntervalFold ((z.im - a.im) / L) :=
    continuous_const.add (continuous_const.mul
      (continuous_unitIntervalFold.comp ((Complex.continuous_im.sub continuous_const).div_const _)))
  exact Complex.equivRealProdCLM.symm.continuous.comp (h1.prodMk h2)

/-- The folding map as a continuous map. -/
noncomputable def squareFoldCM (a : ℂ) (L : ℝ) : C(ℂ, ℂ) :=
  ⟨squareFold a L, continuous_squareFold a L⟩

theorem measurable_comp_squareFoldCM (a : ℂ) (L : ℝ) :
    Measurable fun b : ContinuousPath ℂ => (squareFoldCM a L).comp b :=
  (ContinuousMap.continuous_postcomp (squareFoldCM a L)).measurable

/-- *Reflected (Neumann) planar Brownian motion* in the square `closedSquare a L` (line 545), as a Markov kernel from
the starting point: the law of the folded path `squareFold a L ∘ 𝓑^x`. For `x ∈ closedSquare a L` it starts from `x`
and stays in the square. -/
noncomputable def reflectedPlanarBrownianMotion (a : ℂ) (L : ℝ) : Kernel ℂ (ContinuousPath ℂ) :=
  planarBrownianMotion.map fun b => (squareFoldCM a L).comp b

instance isMarkovKernel_reflectedPlanarBrownianMotion (a : ℂ) (L : ℝ) :
    IsMarkovKernel (reflectedPlanarBrownianMotion a L) :=
  Kernel.IsMarkovKernel.map _ (measurable_comp_squareFoldCM a L)

/-! ### Heat kernel of reflected LBM -/

/-- `IsLBMHeatKernel Q F K μ p`: `p` is the *heat kernel* of the time-changed process `t ↦ b (F x b)⁻¹(t)` under
`Q x`, `x ∈ K`, with respect to the reference measure `μ` on `K` (eq:defining-property-of-kernel, line 547, with
correction [C5]: reference measure `μ_h`, not `dy`): for all `t > 0` and `x ∈ K`, `p t x ≥ 0` on `K` and
`Q x {b : b((F x b)⁻¹ t) ∈ A} = ∫_{A ∩ K} p t x y dμ(y)` for every Borel `A`. For Prop. 2.6 (line 554),
`Q = reflectedPlanarBrownianMotion a L`, `K = closedSquare a L`, `F x` the LQG clock of reflected Brownian motion
from `x` and `μ = μ_h`. -/
def IsLBMHeatKernel (Q : Kernel ℂ (ContinuousPath ℂ)) (F : ℂ → ContinuousPath ℂ → ℝ≥0 → ℝ) (K : Set ℂ)
    (μ : Measure ℂ) (p : ℝ → ℂ → ℂ → ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x ∈ K, (∀ y ∈ K, 0 ≤ p t x y) ∧
    ∀ A : Set ℂ, MeasurableSet A →
      Q x {b | liouvilleBrownianPath (F x) b t.toNNReal ∈ A} = ∫⁻ y in A ∩ K, ENNReal.ofReal (p t x y) ∂μ

/-! ### Sanity lemmas -/

theorem lqgClockApprox_zero (γ : ℝ) (hε : ℝ → ℂ → ℝ) (ε : ℝ) (b : ContinuousPath ℂ) :
    lqgClockApprox γ hε ε b 0 = 0 := by
  simp [lqgClockApprox]

/-- For the (deterministic) circle-average function `hε ε z = -(γ/2) log ε` the approximating clock is the identity
`t` for every `ε > 0` (compare `lqgApprox_neg_log`). -/
theorem lqgClockApprox_neg_log (γ : ℝ) {ε : ℝ} (hε : 0 < ε) (b : ContinuousPath ℂ) (t : ℝ≥0) :
    lqgClockApprox γ (fun r _ => -(γ / 2) * Real.log r) ε b t = t := by
  have h1 : ε ^ (γ ^ 2 / 2) * Real.exp (γ * (-(γ / 2) * Real.log ε)) = 1 := by
    rw [Real.rpow_def_of_pos hε, ← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  simp only [lqgClockApprox, h1, intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]

/-- Non-vacuity: for `hε ε z = -(γ/2) log ε` (the field whose LQG measure is Lebesgue measure, `isLQGLimit_volume`)
the LQG clock of any path law is the identity clock `F b t = t`, so LBM is the underlying Brownian motion. -/
theorem isLQGClock_neg_log (Q : Kernel ℂ (ContinuousPath ℂ)) (γ : ℝ) (x : ℂ) :
    IsLQGClock Q γ (fun r _ => -(γ / 2) * Real.log r) x fun _ t => t := by
  intro T η hη
  have h : ∀ k : ℕ, {b : ContinuousPath ℂ | ∃ t ≤ T, η ≤
      |lqgClockApprox γ (fun r _ => -(γ / 2) * Real.log r) (dyadicScale k) b t - t|} = ∅ := by
    intro k
    ext b
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_exists, not_and, not_le]
    intro t _
    rw [lqgClockApprox_neg_log γ (dyadicScale_pos k), sub_self, abs_zero]
    exact hη
  simp only [h, measure_empty]
  exact tendsto_const_nhds

theorem isTimeChangeClock_coe : IsTimeChangeClock fun t : ℝ≥0 => (t : ℝ) where
  map_zero := rfl
  continuous := NNReal.continuous_coe
  strictMono _ _ h := NNReal.coe_lt_coe.2 h
  tendsto_atTop := tendsto_atTop_atTop_of_monotone NNReal.coe_mono fun r => ⟨r.toNNReal, Real.le_coe_toNNReal r⟩

theorem clockInverse_coe (t : ℝ≥0) : clockInverse (fun s : ℝ≥0 => (s : ℝ)) t = t := by
  simp only [clockInverse, NNReal.coe_lt_coe]
  exact csInf_Ioi

/-- With the identity clock the LBM path is the path itself. -/
theorem liouvilleBrownianPath_coe (b : ContinuousPath ℂ) :
    liouvilleBrownianPath (fun _ t => (t : ℝ)) b = b := by
  funext t
  simp [liouvilleBrownianPath, clockInverse_coe]

/-- With the identity clock the LBM exit time is the Brownian exit time. -/
theorem lbmExitTime_coe (O : Set ℂ) (b : ContinuousPath ℂ) :
    lbmExitTime (fun _ t => (t : ℝ)) O b = ContinuousPath.exitTime O b := by
  simp only [lbmExitTime, liouvilleBrownianPath_coe]
  rfl

theorem unitIntervalFold_of_mem {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) : unitIntervalFold u = u := by
  have hπ := Real.pi_pos
  rw [unitIntervalFold, Real.arccos_cos (by nlinarith [hu.1]) (by nlinarith [hu.2])]
  field_simp

theorem unitIntervalFold_mem (u : ℝ) : unitIntervalFold u ∈ Icc (0 : ℝ) 1 := by
  have hπ := Real.pi_pos
  refine ⟨div_nonneg (Real.arccos_nonneg _) hπ.le, (div_le_one hπ).2 (Real.arccos_le_pi _)⟩

/-- The folding map takes values in the square. -/
theorem squareFold_mem (a : ℂ) {L : ℝ} (hL : 0 ≤ L) (z : ℂ) : squareFold a L z ∈ closedSquare a L := by
  have h1 := unitIntervalFold_mem ((z.re - a.re) / L)
  have h2 := unitIntervalFold_mem ((z.im - a.im) / L)
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [squareFold] <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- The folding map is the identity on the square. -/
theorem squareFold_of_mem (a : ℂ) {L : ℝ} (hL : 0 < L) {z : ℂ} (hz : z ∈ closedSquare a L) :
    squareFold a L z = z := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  have e1 : unitIntervalFold ((z.re - a.re) / L) = (z.re - a.re) / L :=
    unitIntervalFold_of_mem ⟨div_nonneg (by linarith) hL.le, (div_le_one hL).2 (by linarith)⟩
  have e2 : unitIntervalFold ((z.im - a.im) / L) = (z.im - a.im) / L :=
    unitIntervalFold_of_mem ⟨div_nonneg (by linarith) hL.le, (div_le_one hL).2 (by linarith)⟩
  apply Complex.ext <;> simp only [squareFold, e1, e2] <;> field_simp <;> ring

end HarmonicBalls
