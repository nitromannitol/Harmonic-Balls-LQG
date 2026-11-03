import HarmonicBalls.Defs.Laplacian
import HarmonicBalls.Defs.Green

/-! # The obstacle problem: supersolutions, least supersolution, cluster and odometer

Bou-Rabee and Gwynne, *Harmonic balls in Liouville quantum gravity* (arXiv:2208.11795).

* Section 3.1 (subsec:obstacle-def, lines 579-604): for a measure `μ` (the paper's `μ_h`), a radius `r > 0`, a pole
  `z ∈ B_r` and a mass `t > 0`, the supersolutions `S_{B_r;z}(t)`, the least supersolution `v_{B_r;z}(t)`, the
  cluster `Λ_{B_r;z}(t)` and the odometer `u_{B_r;z}(t)`.
* Appendix A (sec:obstacle-appendix, lines 3522-3583): the volume growth condition (eq:volume-growth), the potential
  `q_{B_R}`, the obstacle `β_t`, the shifted supersolutions `S̃(t)`, the least superharmonic majorant `ṽ_t`, the
  odometer `v_t = ṽ_t - β_t` and the non-coincidence set `Λ_t`. The paper takes `R = 1` and pole `0` (line 3547); we
  keep a general radius `R` (Lemma A.6, lemma:appendix-cluster-compatibility, line 3851, uses `B_s`, `s ≤ R`) and a
  general pole `z` (the Section 3 lemmas are stated for every `z ∈ B_r`); the paper's objects are the case `z = 0`.

All definitions are total: they make sense for every `r`, `z`, `t`; the paper's standing assumptions `r, t > 0` and
`z ∈ B_r` are hypotheses of the statements.

## The pole and junk values

`greenFunction (ball 0 r) z x` has the junk value `0` at `x = z`, where the paper's value is `+∞`. Accordingly:

* the obstacle constraint `w ≥ -t G_{B_r}(z,·)` is imposed only at `x ≠ z` (at `x = z` the paper's obstacle is `-∞`
  and imposes nothing);
* the cluster and the non-coincidence set contain the pole by definition (the paper's strict inequality
  `v(z) > -∞` holds at `z` as soon as `v(z)` is finite, Lemma 3.1);
* the odometers at the pole take the junk value `v(z)` (resp. `ṽ(z) - q_{B_R}(z)`); the paper's value is `+∞`.

On the sphere `∂B_r` the junk value `greenFunction (ball 0 r) z x = 0` for `x ∉ ball 0 r` is the true boundary value
of the Green function, so the constraint there is `w ≥ 0`, as in the paper.

## Paper typos followed in corrected form (ESCALATIONS E2, E3)

* eq:volume-growth (line 3526) prints `r^{β⁻} ≤ μ(B_r(z)) ≤ r^{β⁻}`; we use the upper exponent `β⁺`, as in
  Lemma 2.4 (lemma:volume-growth, eq:ball-volume, line 500), from which the condition is derived (line 3529).
* eq:limit-odometer (line 596) prints `v + t G_{B_r;z}(0,·)`; we use the pole `z`, as required by Lemma 3.2
  (`Δu = -t δ_z + ...`, line 635). `G_{B_r;z}(z,x)` in eq:non-co-set (line 592) is `G_{B_r}(z,x)`.
-/

namespace HarmonicBalls

open MeasureTheory Metric

/-! ## Section 3.1: the obstacle problem with Green function obstacle -/

/-- The set of *supersolutions* `S_{B_r;z}(t)` (eq:super-solutions, line 583): functions `w` continuous on the closed
ball `closedBall 0 r` with `Δw ≤ μ` in `B_r` (distributional sense, `LaplacianLE`) lying above the obstacle
`-t G_{B_r}(z,·)` on the closed ball. The constraint is imposed off the pole, where the paper's obstacle is `-∞`. The
values of `w` outside the closed ball are irrelevant to the paper's set `C(\overline{B_r})` and unconstrained here. -/
def supersolutions (μ : Measure ℂ) (r : ℝ) (z : ℂ) (t : ℝ) : Set (ℂ → ℝ) :=
  {w | ContinuousOn w (closedBall 0 r) ∧ LaplacianLE w μ (ball 0 r) ∧
    ∀ x ∈ closedBall (0 : ℂ) r, x ≠ z → -t * greenFunction (ball 0 r) z x ≤ w x}

/-- The *least supersolution* `v_{B_r;z}(t)` (eq:least-super-solution, line 588): the pointwise infimum of the
supersolutions, `x ↦ inf {w x | w ∈ S_{B_r;z}(t)}`.

Junk behaviour of `sInf` on `ℝ`: it returns `0` when the set of values is empty or not bounded below. For `x` in the
closed ball with `x ≠ z` the values are bounded below by the obstacle (`bddBelow_supersolutions`), so `sInf` is the
true infimum. At the pole the paper's infimum may a priori be `-∞`; Lemma 3.1 (lemma:basic-properties, line 621)
asserts it is finite, i.e. that the set of values is bounded below. Outside the closed ball the values of
supersolutions are unconstrained and the infimum is meaningless. -/
noncomputable def leastSupersolution (μ : Measure ℂ) (r : ℝ) (z : ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  sInf ((fun w : ℂ → ℝ => w x) '' supersolutions μ r z t)

/-- The *cluster* `Λ_{B_r;z}(t)` (eq:non-co-set, line 592): the points of `B_r` where the least supersolution lies
strictly above the obstacle, `{x ∈ B_r : v_{B_r;z}(t)(x) > -t G_{B_r}(z,x)}`. The pole `z` belongs to it since the
paper's obstacle is `-∞` there. -/
def cluster (μ : Measure ℂ) (r : ℝ) (z : ℂ) (t : ℝ) : Set ℂ :=
  {x ∈ ball (0 : ℂ) r |
    x = z ∨ -t * greenFunction (ball 0 r) z x < leastSupersolution μ r z t x}

/-- The *odometer* `u_{B_r;z}(t) = v_{B_r;z}(t) + t G_{B_r}(z,·)` (eq:limit-odometer, line 596, with the pole `z` in
place of the printed `0`, ESCALATIONS E3). At the pole it takes the junk value `v_{B_r;z}(t)(z)`; the paper's value is
`+∞`. -/
noncomputable def odometer (μ : Measure ℂ) (r : ℝ) (z : ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  leastSupersolution μ r z t x + t * greenFunction (ball 0 r) z x

/-! ## Appendix A: the shifted obstacle problem -/

/-- The *volume growth condition* (eq:volume-growth, line 3526) on `B_R`: the exponents `β⁻, β⁺` are positive and,
for all sufficiently small `r > 0` and all `z ∈ B_R`, `r^{β⁻} ≤ μ(B_r(z)) ≤ r^{β⁺}`. The printed upper bound
`r^{β⁻}` is a typo for `r^{β⁺}` (ESCALATIONS E2; cf. eq:ball-volume, line 500). The paper also assumes `μ` Radon
(line 3525); on `ℂ` this is `IsLocallyFiniteMeasure μ`, a separate hypothesis of the statements. -/
def VolumeGrowth (μ : Measure ℂ) (R βminus βplus : ℝ) : Prop :=
  0 < βminus ∧ 0 < βplus ∧
    ∃ r₀ > 0, ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
      ENNReal.ofReal (r ^ βminus) ≤ μ (ball z r) ∧ μ (ball z r) ≤ ENNReal.ofReal (r ^ βplus)

/-- The potential `q_{B_R}(x) = ∫_{B_R} G_{B_R}(y,x) μ(dy)` (eq:expected-exit-time, line 3532), with the integrand
`G_{B_R}(y,·)` as printed. It equals `greenPotential (ball 0 R) μ x` by the symmetry of the Green function (not yet a
theorem). Junk value `0` when `y ↦ G_{B_R}(y,x)` is not `μ`-integrable on `B_R`; if `μ` has an atom at `x`, the
diagonal junk value of `greenFunction` enters (the volume growth condition excludes atoms). For `μ` Lebesgue measure,
`q_{B_R}` is one half of the expected exit time of `B_R` by standard Brownian motion (generator `Δ/2`). -/
noncomputable def greenPotentialBall (μ : Measure ℂ) (R : ℝ) (x : ℂ) : ℝ :=
  ∫ y in ball (0 : ℂ) R, greenFunction (ball 0 R) y x ∂μ

/-- The *obstacle* `β_t = -t G_{B_R}(z,·) + q_{B_R}` (eq:obstacle, line 3551, where `R = 1` and `z = 0`). At the pole
the paper's value is `-∞` (the printed codomain `ℝ ∪ {∞}` should read `ℝ ∪ {-∞}`); here the junk value is
`q_{B_R}(z)`, and the constraints below are imposed off the pole. -/
noncomputable def obstacle (μ : Measure ℂ) (R : ℝ) (z : ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  -t * greenFunction (ball 0 R) z x + greenPotentialBall μ R x

/-- The set of *(shifted) supersolutions* `S̃(t)` (eq:shifted-supersolutions, line 3556, where `R = 1`, `z = 0`):
functions `w` continuous on `closedBall 0 R`, superharmonic in `B_R` in the distributional sense (`Δw ≤ 0`), lying
above the obstacle `β_t` on the closed ball off the pole. -/
def shiftedSupersolutions (μ : Measure ℂ) (R : ℝ) (z : ℂ) (t : ℝ) : Set (ℂ → ℝ) :=
  {w | ContinuousOn w (closedBall 0 R) ∧ LaplacianLE w 0 (ball 0 R) ∧
    ∀ x ∈ closedBall (0 : ℂ) R, x ≠ z → obstacle μ R z t x ≤ w x}

/-- The *least supersolution* or *least superharmonic majorant* `ṽ_t` (eq:appendix-least-supersolution, line 3563):
the pointwise infimum of `S̃(t)`. Same junk behaviour of `sInf` as `leastSupersolution`: the true infimum on the
closed ball off the pole (`bddBelow_shiftedSupersolutions`); finiteness at the pole is part of Lemma A.1
(lemma:appendix-basic-properties, line 3589). -/
noncomputable def shiftedLeastSupersolution (μ : Measure ℂ) (R : ℝ) (z : ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  sInf ((fun w : ℂ → ℝ => w x) '' shiftedSupersolutions μ R z t)

/-- The *odometer* `v_t = ṽ_t - β_t` of the shifted problem (eq:appendix-limit-odometer, line 3567). At the pole it
takes the junk value `ṽ_t(z) - q_{B_R}(z)`; the paper's value is `+∞`. -/
noncomputable def shiftedOdometer (μ : Measure ℂ) (R : ℝ) (z : ℂ) (t : ℝ) (x : ℂ) : ℝ :=
  shiftedLeastSupersolution μ R z t x - obstacle μ R z t x

/-- The *non-coincidence set* `Λ_t = {x ∈ B_R : ṽ_t(x) > β_t(x)}` (eq:appendix-non-co-set, line 3572). The pole
belongs to it since the paper's obstacle is `-∞` there. -/
def nonCoincidenceSet (μ : Measure ℂ) (R : ℝ) (z : ℂ) (t : ℝ) : Set ℂ :=
  {x ∈ ball (0 : ℂ) R | x = z ∨ obstacle μ R z t x < shiftedLeastSupersolution μ R z t x}

/-! ## Sanity lemmas -/

section Sanity

variable {μ : Measure ℂ} {r t : ℝ} {z x : ℂ}

/-- `0 ∈ S_{B_r;z}(t)` for `t ≥ 0` (line 599: "`S_{B_r;z}(t)` is non-empty as it contains the zero function"). -/
theorem zero_mem_supersolutions (μ : Measure ℂ) (r : ℝ) (z : ℂ) (ht : 0 ≤ t) : (0 : ℂ → ℝ) ∈ supersolutions μ r z t :=
  ⟨continuous_zero.continuousOn, laplacianLE_zero μ _, fun x _ _ => by
    simpa using mul_nonneg ht (greenFunction_nonneg isBounded_ball z x)⟩

theorem supersolutions_nonempty (μ : Measure ℂ) (r : ℝ) (z : ℂ) (ht : 0 ≤ t) : (supersolutions μ r z t).Nonempty :=
  ⟨0, zero_mem_supersolutions μ r z ht⟩

/-- Off the pole, on the closed ball, the values of the supersolutions are bounded below by the obstacle, so
`leastSupersolution` is a true infimum there. -/
theorem bddBelow_supersolutions (hx : x ∈ closedBall (0 : ℂ) r) (hxz : x ≠ z) :
    BddBelow ((fun w : ℂ → ℝ => w x) '' supersolutions μ r z t) :=
  ⟨-t * greenFunction (ball 0 r) z x, by rintro _ ⟨w, hw, rfl⟩; exact hw.2.2 x hx hxz⟩

theorem leastSupersolution_le {w : ℂ → ℝ} (hw : w ∈ supersolutions μ r z t) (hx : x ∈ closedBall (0 : ℂ) r)
    (hxz : x ≠ z) : leastSupersolution μ r z t x ≤ w x :=
  csInf_le (bddBelow_supersolutions hx hxz) ⟨w, hw, rfl⟩

/-- The least supersolution lies above the obstacle off the pole. -/
theorem le_leastSupersolution (ht : 0 ≤ t) (hx : x ∈ closedBall (0 : ℂ) r) (hxz : x ≠ z) :
    -t * greenFunction (ball 0 r) z x ≤ leastSupersolution μ r z t x :=
  le_csInf ((supersolutions_nonempty μ r z ht).image _) (by rintro _ ⟨w, hw, rfl⟩; exact hw.2.2 x hx hxz)

theorem leastSupersolution_nonpos (ht : 0 ≤ t) (hx : x ∈ closedBall (0 : ℂ) r) (hxz : x ≠ z) :
    leastSupersolution μ r z t x ≤ 0 :=
  leastSupersolution_le (zero_mem_supersolutions μ r z ht) hx hxz

theorem odometer_nonneg (ht : 0 ≤ t) (hx : x ∈ closedBall (0 : ℂ) r) (hxz : x ≠ z) :
    0 ≤ odometer μ r z t x := by
  have := le_leastSupersolution (μ := μ) ht hx hxz
  unfold odometer
  linarith

/-- The cluster is the positivity set of the odometer in `B_r`, together with the pole. -/
theorem mem_cluster_iff : x ∈ cluster μ r z t ↔ x ∈ ball (0 : ℂ) r ∧ (x = z ∨ 0 < odometer μ r z t x) := by
  unfold cluster odometer
  simp only [Set.mem_ofPred_eq]
  constructor <;> rintro ⟨hx, h | h⟩ <;> first | exact ⟨hx, Or.inl h⟩ | exact ⟨hx, Or.inr (by linarith)⟩

theorem self_mem_cluster (hz : z ∈ ball (0 : ℂ) r) : z ∈ cluster μ r z t :=
  ⟨hz, Or.inl rfl⟩

theorem cluster_subset_ball : cluster μ r z t ⊆ ball (0 : ℂ) r := fun _ hx => hx.1

/-- The volume growth condition on `B_R` implies it on `B_s` for `s ≤ R` (proof of Lemma A.6, line 3858). -/
theorem VolumeGrowth.mono {R s βminus βplus : ℝ} (h : VolumeGrowth μ R βminus βplus) (hs : s ≤ R) :
    VolumeGrowth μ s βminus βplus := by
  obtain ⟨h1, h2, r₀, hr₀, h⟩ := h
  exact ⟨h1, h2, r₀, hr₀, fun r hr hrr₀ z hz => h r hr hrr₀ z (ball_subset_ball hs hz)⟩

/-- Non-vacuity of the volume growth condition: Lebesgue measure satisfies it on every `B_R` with `β⁻ = 2`,
`β⁺ = 1`, since `r² ≤ π r² ≤ r` for `0 < r < 1/4`. -/
theorem volumeGrowth_volume (R : ℝ) : VolumeGrowth volume R 2 1 := by
  refine ⟨two_pos, one_pos, 1 / 4, by norm_num, fun r hr hr4 z _ => ?_⟩
  have hvol : volume (ball z r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
    rw [Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr.le, mul_comm,
      ← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  have hpir : Real.pi * r ≤ 1 := by nlinarith [Real.pi_le_four]
  rw [hvol, Real.rpow_two, Real.rpow_one]
  constructor <;> apply ENNReal.ofReal_le_ofReal
  · nlinarith [Real.pi_gt_three, sq_nonneg r]
  · nlinarith

/-- For `t ≥ 0` the obstacle lies below `q_{B_R}`, since `G_{B_R} ≥ 0`. -/
theorem obstacle_le_greenPotentialBall (μ : Measure ℂ) (R : ℝ) (z : ℂ) (ht : 0 ≤ t) (x : ℂ) :
    obstacle μ R z t x ≤ greenPotentialBall μ R x := by
  have := mul_nonneg ht (greenFunction_nonneg (isBounded_ball (x := (0 : ℂ)) (r := R)) z x)
  unfold obstacle
  linarith

/-- `q_{B_R} ∈ S̃(t)` (line 3570), granted the potential-theoretic facts "continuous on the closed ball" and
"superharmonic in `B_R`" (properties 1 and 2 of `q_{B_R}`, lines 3538-3539); the obstacle constraint is
`obstacle_le_greenPotentialBall`. -/
theorem greenPotentialBall_mem_shiftedSupersolutions {R : ℝ} (ht : 0 ≤ t)
    (hcont : ContinuousOn (greenPotentialBall μ R) (closedBall 0 R))
    (hsuper : LaplacianLE (greenPotentialBall μ R) 0 (ball 0 R)) :
    greenPotentialBall μ R ∈ shiftedSupersolutions μ R z t :=
  ⟨hcont, hsuper, fun x _ _ => obstacle_le_greenPotentialBall μ R z ht x⟩

theorem bddBelow_shiftedSupersolutions {R : ℝ} (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) :
    BddBelow ((fun w : ℂ → ℝ => w x) '' shiftedSupersolutions μ R z t) :=
  ⟨obstacle μ R z t x, by rintro _ ⟨w, hw, rfl⟩; exact hw.2.2 x hx hxz⟩

theorem shiftedLeastSupersolution_le {R : ℝ} {w : ℂ → ℝ} (hw : w ∈ shiftedSupersolutions μ R z t)
    (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) : shiftedLeastSupersolution μ R z t x ≤ w x :=
  csInf_le (bddBelow_shiftedSupersolutions hx hxz) ⟨w, hw, rfl⟩

/-- If `S̃(t)` is non-empty, the least superharmonic majorant lies above the obstacle off the pole. -/
theorem obstacle_le_shiftedLeastSupersolution {R : ℝ} (hne : (shiftedSupersolutions μ R z t).Nonempty)
    (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) :
    obstacle μ R z t x ≤ shiftedLeastSupersolution μ R z t x :=
  le_csInf (hne.image _) (by rintro _ ⟨w, hw, rfl⟩; exact hw.2.2 x hx hxz)

theorem shiftedOdometer_nonneg {R : ℝ} (hne : (shiftedSupersolutions μ R z t).Nonempty)
    (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) : 0 ≤ shiftedOdometer μ R z t x :=
  sub_nonneg.2 (obstacle_le_shiftedLeastSupersolution hne hx hxz)

/-- The non-coincidence set is the positivity set of the odometer `v_t` in `B_R`, together with the pole. -/
theorem mem_nonCoincidenceSet_iff {R : ℝ} :
    x ∈ nonCoincidenceSet μ R z t ↔ x ∈ ball (0 : ℂ) R ∧ (x = z ∨ 0 < shiftedOdometer μ R z t x) := by
  unfold nonCoincidenceSet shiftedOdometer
  simp only [Set.mem_ofPred_eq, sub_pos]

theorem self_mem_nonCoincidenceSet {R : ℝ} (hz : z ∈ ball (0 : ℂ) R) : z ∈ nonCoincidenceSet μ R z t :=
  ⟨hz, Or.inl rfl⟩

end Sanity

end HarmonicBalls
