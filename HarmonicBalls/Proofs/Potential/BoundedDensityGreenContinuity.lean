import HarmonicBalls.Proofs.Potential.GreenPoleL1Continuity

/-!
# Interior continuity of the Green potential of a bounded density

Let `U ⊆ ℂ` be bounded and open, let `f : ℂ → ℝ` be Lebesgue measurable with `|f| ≤ M` almost
everywhere (for `volume`), and let `G_U` be the Green function of Armitage–Gardiner (`Defs/Green.lean`:
zero outside `U`, pole in the first slot, integration variable in the second). Then:

* for every pole `x : ℂ` the function `y ↦ G_U(x, y) f(y)` is integrable;
* the Green potential `x ↦ ∫ G_U(x, y) f(y) dy` is continuous on `U`;
* for all poles `x, z`,
  `|∫ G_U(x, y) f(y) dy - ∫ G_U(z, y) f(y) dy| ≤ M ∫ |G_U(x, y) - G_U(z, y)| dy`.

Only the bounded measurability of `f` is used: no continuity, support, boundary or source-free
hypothesis on `f`, and no literature input. The interior continuity is the scalar L¹ continuity of the
Green row in its pole (`tendsto_integral_abs_greenFunction_sub_nhdsWithin`, `GreenPoleL1Continuity.lean`)
transported to the integral against `f` by the comparison estimate.

Credit: the local volume estimate behind the scalar input uses work of Leonardo Bonanno, reached through
the pinned Lattice-Probability lean-v4.35 port (module `LatticeProb.Prob.Birkhoff` in the import closure
of `GreenPoleL1Continuity`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology

/-- Integrability of the Green row against a bounded density. For every pole `x`, the function
`y ↦ G_U(x, y) f(y)` is integrable on `ℂ` when `f` is measurable and `|f| ≤ M` almost everywhere: the
row `G_U(x, ·)` is integrable by `integrable_greenFunction_pole`, and multiplication by a bounded
measurable factor preserves integrability (`Integrable.mul_bdd`). -/
theorem integrable_greenFunction_mul_bdd {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {f : ℂ → ℝ} (hf : AEStronglyMeasurable f volume) {M : ℝ}
    (hfM : ∀ᵐ y ∂(volume : Measure ℂ), |f y| ≤ M) (x : ℂ) :
    Integrable (fun y => greenFunction U x y * f y) :=
  (integrable_greenFunction_pole hU hUb x).mul_bdd (c := M) hf
    (hfM.mono fun y hy => by rwa [Real.norm_eq_abs])

/-- Comparison estimate for the Green potential of a bounded density: for all poles `x, z`,
`|∫ G_U(x, y) f(y) dy - ∫ G_U(z, y) f(y) dy| ≤ M ∫ |G_U(x, y) - G_U(z, y)| dy`. The difference of the
two potentials is the integral of `(G_U(x, y) - G_U(z, y)) f(y)`, which is bounded in absolute value by
`M |G_U(x, y) - G_U(z, y)|` almost everywhere. -/
theorem abs_integral_greenFunction_mul_sub_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {f : ℂ → ℝ} (hf : AEStronglyMeasurable f volume) {M : ℝ}
    (hfM : ∀ᵐ y ∂(volume : Measure ℂ), |f y| ≤ M) (x z : ℂ) :
    |(∫ y, greenFunction U x y * f y) - ∫ y, greenFunction U z y * f y|
      ≤ M * ∫ y, |greenFunction U x y - greenFunction U z y| := by
  have hsplit : ∫ y, (greenFunction U x y - greenFunction U z y) * f y
      = (∫ y, greenFunction U x y * f y) - ∫ y, greenFunction U z y * f y := by
    simp_rw [sub_mul]
    exact integral_sub (integrable_greenFunction_mul_bdd hU hUb hf hfM x)
      (integrable_greenFunction_mul_bdd hU hUb hf hfM z)
  have hdiff : Integrable (fun y => |greenFunction U x y - greenFunction U z y|) :=
    ((integrable_greenFunction_pole hU hUb x).sub
      (integrable_greenFunction_pole hU hUb z)).abs
  rw [← hsplit]
  calc |∫ y, (greenFunction U x y - greenFunction U z y) * f y|
      = ‖∫ y, (greenFunction U x y - greenFunction U z y) * f y‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ y, ‖(greenFunction U x y - greenFunction U z y) * f y‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ y, M * |greenFunction U x y - greenFunction U z y| := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun y => norm_nonneg _)
          (hdiff.const_mul M) ?_
        filter_upwards [hfM] with y hy
        show ‖(greenFunction U x y - greenFunction U z y) * f y‖
          ≤ M * |greenFunction U x y - greenFunction U z y|
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm M]
        exact mul_le_mul_of_nonneg_left hy (abs_nonneg _)
    _ = M * ∫ y, |greenFunction U x y - greenFunction U z y| := integral_const_mul _ _

/-- Interior continuity of the Green potential of a bounded density: `x ↦ ∫ G_U(x, y) f(y) dy` is
continuous on the bounded open set `U`. The proof squeezes the distance `dist (Φ z) (Φ x₀)`, `Φ` the
potential, between `0` and `M ∫ |G_U(z, y) - G_U(x₀, y)| dy`, which tends to `0` as `z → x₀` within `U`
by `tendsto_integral_abs_greenFunction_sub_nhdsWithin`. -/
theorem continuousOn_integral_greenFunction_mul_bdd {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {f : ℂ → ℝ} (hf : AEStronglyMeasurable f volume) {M : ℝ}
    (hfM : ∀ᵐ y ∂(volume : Measure ℂ), |f y| ≤ M) :
    ContinuousOn (fun x => ∫ y, greenFunction U x y * f y) U := by
  intro x0 hx0
  have hlim : Tendsto (fun z => M * ∫ y, |greenFunction U z y - greenFunction U x0 y|)
      (𝓝[U] x0) (𝓝 0) := by
    have h := (tendsto_integral_abs_greenFunction_sub_nhdsWithin hU hUb hx0).const_mul M
    rwa [mul_zero] at h
  unfold ContinuousWithinAt
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun z => dist_nonneg)
    (Eventually.of_forall fun z => ?_) hlim
  show dist (∫ y, greenFunction U z y * f y) (∫ y, greenFunction U x0 y * f y) ≤ _
  rw [Real.dist_eq]
  exact abs_integral_greenFunction_mul_sub_le hU hUb hf hfM z x0

/-- Green potential of a bounded density, interior statement (Armitage–Gardiner Green function, Lebesgue
measure). For a bounded open `U` and a measurable `f` with `|f| ≤ M` almost everywhere:
(i) every row `y ↦ G_U(x, y) f(y)` is integrable; (ii) `x ↦ ∫ G_U(x, y) f(y) dy` is continuous on `U`;
(iii) the comparison estimate holds for all poles `x, z`. The sign hypothesis `_hM : 0 ≤ M` is kept as
in the specification; it is not used, because the a.e. bound on the nonnull measure `volume` already
forces `0 ≤ M`. -/
theorem greenPotential_boundedDensity_interior {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {f : ℂ → ℝ} (hf : AEStronglyMeasurable f volume) {M : ℝ}
    (_hM : 0 ≤ M) (hfM : ∀ᵐ y ∂(volume : Measure ℂ), |f y| ≤ M) :
    (∀ x : ℂ, Integrable (fun y => greenFunction U x y * f y)) ∧
      ContinuousOn (fun x => ∫ y, greenFunction U x y * f y) U ∧
      ∀ x z : ℂ, |(∫ y, greenFunction U x y * f y) - ∫ y, greenFunction U z y * f y|
        ≤ M * ∫ y, |greenFunction U x y - greenFunction U z y| :=
  ⟨fun x => integrable_greenFunction_mul_bdd hU hUb hf hfM x,
    continuousOn_integral_greenFunction_mul_bdd hU hUb hf hfM,
    fun x z => abs_integral_greenFunction_mul_sub_le hU hUb hf hfM x z⟩

end HarmonicBalls
