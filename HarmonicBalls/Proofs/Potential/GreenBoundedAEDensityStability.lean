import HarmonicBalls.Proofs.Potential.BoundedDensityGreenContinuity
import HarmonicBalls.Proofs.Potential.GreenRowL1Continuous

/-!
# Uniform convergence of Green potentials under a.e. convergence of bounded densities

Let `U ⊆ ℂ` be bounded and open, and let `G_U` be the Green function of Armitage–Gardiner
(`Defs/Green.lean`, value `0` off `U`). For a real density `f` the Green potential is the literal integral
`x ↦ ∫ y, G_U(x, y) * f y`. For a compact `K ⊆ U` this file proves the stability of Green potentials under
almost-everywhere convergence of densities bounded by one common constant:

* `tendsto_greenPotential_of_ae_convergence`: pointwise convergence at every pole `x : ℂ`, by dominated
  convergence with the integrable bound `|M| * G_U(x, ·)`;
* `tendstoUniformlyOn_greenPotential_of_ae_convergence`: uniform convergence over `x ∈ K`. The potentials
  obey the common modulus `|∫ G_U(x, ·) f n - ∫ G_U(z, ·) f n| ≤ M ∫ |G_U(x, ·) - G_U(z, ·)|`
  (`abs_integral_greenFunction_mul_sub_le`), and the pole map `x ↦ G_U(x, ·)` is uniformly continuous into
  `L¹` on `K` (`uniformContinuousOn_greenRowL1`). A finite `δ`-net of `K` transfers the pointwise convergence
  at the net points to every point of `K`;
* `greenPotential_boundedAE_convergence_compact`: the explicit package, with the integrability of every
  literal integrand, the uniform convergence on `K`, and the `ε/N` form.

The hypotheses are measurability, the common bound `|f n| ≤ M` and `|g| ≤ M` almost everywhere, and the
almost-everywhere convergence `f n → g`. No uniform-convergence hypothesis, no abstract operator hypothesis
and no literature input enter. The local volume estimate and the potential-theoretic infrastructure reached
through the import closure use work of Leonardo Bonanno, through the pinned Lattice-Probability (lean-v4.35)
port.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Metric

/-- Pointwise convergence of Green potentials. If `f n → g` almost everywhere with `|f n| ≤ M` and
`|g| ≤ M` almost everywhere, then for every pole `x : ℂ`,
`∫ G_U(x, y) f n(y) dy → ∫ G_U(x, y) g(y) dy`. Dominated convergence applies with the integrable bound
`|M| * G_U(x, ·)`, the Green row `G_U(x, ·)` being integrable by `integrable_greenFunction_pole`. -/
theorem tendsto_greenPotential_of_ae_convergence {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {f : ℕ → ℂ → ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) volume)
    {g : ℂ → ℝ} {M : ℝ} (hfM : ∀ n, ∀ᵐ y ∂(volume : Measure ℂ), |f n y| ≤ M)
    (hconv : ∀ᵐ y ∂(volume : Measure ℂ), Tendsto (fun n => f n y) atTop (𝓝 (g y))) (x : ℂ) :
    Tendsto (fun n => ∫ y, greenFunction U x y * f n y) atTop
      (𝓝 (∫ y, greenFunction U x y * g y)) := by
  refine tendsto_integral_of_dominated_convergence (fun y => |M| * greenFunction U x y)
    (fun n => (integrable_greenFunction_mul_bdd hU hUb (hf n) (hfM n) x).aestronglyMeasurable)
    ((integrable_greenFunction_pole hU hUb x).const_mul |M|) ?_ ?_
  · intro n
    filter_upwards [hfM n] with y hy
    have hG : 0 ≤ greenFunction U x y := greenFunction_nonneg hUb x y
    show ‖greenFunction U x y * f n y‖ ≤ |M| * greenFunction U x y
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hG]
    calc greenFunction U x y * |f n y| ≤ greenFunction U x y * |M| :=
          mul_le_mul_of_nonneg_left (hy.trans (le_abs_self M)) hG
      _ = |M| * greenFunction U x y := mul_comm _ _
  · filter_upwards [hconv] with y hy
    exact hy.const_mul (greenFunction U x y)

/-- Three-step triangle estimate: if `|u - v| ≤ ε / 3`, `|v - w| < ε / 3` and `|w - t| ≤ ε / 3`, then
`|u - t| < ε`. -/
theorem abs_sub_lt_of_three_steps {u v w t ε : ℝ} (h₁ : |u - v| ≤ ε / 3) (h₂ : |v - w| < ε / 3)
    (h₃ : |w - t| ≤ ε / 3) : |u - t| < ε := by
  have e₁ := abs_sub_le u v t
  have e₂ := abs_sub_le v w t
  linarith

/-- Uniform convergence of Green potentials on a compact subset. Let `U` be bounded and open, `K ⊆ U`
compact, and `f n`, `g` measurable real densities with `|f n| ≤ M` and `|g| ≤ M` almost everywhere and
`f n → g` almost everywhere. Then `∫ G_U(x, y) f n(y) dy → ∫ G_U(x, y) g(y) dy` uniformly for `x ∈ K`.

Proof. Fix `ε > 0` and set `η = ε / (3 (|M| + 1))`. Uniform continuity of `x ↦ G_U(x, ·)` into `L¹` on `K`
(`uniformContinuousOn_greenRowL1`) gives `δ > 0` with `∫ |G_U(x, ·) - G_U(z, ·)| < η` for `x, z ∈ K`,
`dist x z < δ`. Compactness gives a finite `T ⊆ K` with `K ⊆ ⋃ z ∈ T, B(z, δ)`, and pointwise convergence
at the finitely many points of `T` gives an eventual bound `< ε / 3` there. For `x ∈ K` pick `z ∈ T`
with `dist x z < δ` and split `|P_g x - P_n x|` through `z`; each piece is at most `ε / 3`, the middle one
strictly. -/
theorem tendstoUniformlyOn_greenPotential_of_ae_convergence {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {K : Set ℂ} (hKU : K ⊆ U) (hK : IsCompact K)
    {f : ℕ → ℂ → ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) volume)
    {g : ℂ → ℝ} (hg : AEStronglyMeasurable g volume) {M : ℝ}
    (hfM : ∀ n, ∀ᵐ y ∂(volume : Measure ℂ), |f n y| ≤ M)
    (hgM : ∀ᵐ y ∂(volume : Measure ℂ), |g y| ≤ M)
    (hconv : ∀ᵐ y ∂(volume : Measure ℂ), Tendsto (fun n => f n y) atTop (𝓝 (g y))) :
    TendstoUniformlyOn (fun n x => ∫ y, greenFunction U x y * f n y)
      (fun x => ∫ y, greenFunction U x y * g y) atTop K := by
  have hmod := Metric.uniformContinuousOn_iff.mp (uniformContinuousOn_greenRowL1 hU hUb hKU hK)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hpos : 0 < ε / (3 * (|M| + 1)) := div_pos hε (by positivity)
  obtain ⟨δ, hδ, hδK⟩ := hmod (ε / (3 * (|M| + 1))) hpos
  obtain ⟨T, hTK, hTfin, hcover⟩ := finite_cover_balls_of_compact hK hδ
  have hev : ∀ᶠ n in atTop, ∀ z ∈ T,
      dist (∫ y, greenFunction U z y * f n y) (∫ y, greenFunction U z y * g y) < ε / 3 := by
    refine (Filter.eventually_all_finite hTfin).mpr fun z _ => ?_
    exact Metric.tendsto_nhds.mp (tendsto_greenPotential_of_ae_convergence hU hUb hf hfM hconv z)
      (ε / 3) (div_pos hε (by norm_num))
  filter_upwards [hev] with n hn
  intro x hx
  obtain ⟨z, hzT, hxz⟩ := Set.mem_iUnion₂.mp (hcover hx)
  have hzK : z ∈ K := hTK hzT
  have hI : dist (greenRowL1 hU hUb x) (greenRowL1 hU hUb z) < ε / (3 * (|M| + 1)) :=
    hδK x hx z hzK (Metric.mem_ball.mp hxz)
  rw [dist_greenRowL1 hU hUb x z] at hI
  have hI0 : 0 ≤ ∫ y, |greenFunction U x y - greenFunction U z y| :=
    integral_nonneg fun y => abs_nonneg _
  have hMI : |M| * (∫ y, |greenFunction U x y - greenFunction U z y|) ≤ ε / 3 := by
    have hL : (|M| + 1) ≠ 0 := by positivity
    calc |M| * (∫ y, |greenFunction U x y - greenFunction U z y|)
        ≤ |M| * (ε / (3 * (|M| + 1))) := mul_le_mul_of_nonneg_left hI.le (abs_nonneg M)
      _ ≤ (|M| + 1) * (ε / (3 * (|M| + 1))) :=
          mul_le_mul_of_nonneg_right (by linarith) hpos.le
      _ = ε / 3 := by field_simp
  have hgxz := (abs_integral_greenFunction_mul_sub_le hU hUb hg hgM x z).trans
    ((mul_le_mul_of_nonneg_right (le_abs_self M) hI0).trans hMI)
  have hfxz := (abs_integral_greenFunction_mul_sub_le hU hUb (hf n) (hfM n) x z).trans
    ((mul_le_mul_of_nonneg_right (le_abs_self M) hI0).trans hMI)
  have hfxz' : |(∫ y, greenFunction U z y * f n y) - ∫ y, greenFunction U x y * f n y| ≤ ε / 3 := by
    rw [abs_sub_comm]
    exact hfxz
  have hnz : |(∫ y, greenFunction U z y * g y) - ∫ y, greenFunction U z y * f n y| < ε / 3 := by
    have h := hn z hzT
    rw [Real.dist_eq, abs_sub_comm] at h
    exact h
  rw [Real.dist_eq]
  exact abs_sub_lt_of_three_steps hgxz hnz hfxz'

/-- Explicit `ε/N` form of the uniform convergence on a compact subset: for every `ε > 0` there is `N`
such that for all `n ≥ N` and all `x ∈ K`,
`|∫ G_U(x, y) f n(y) dy - ∫ G_U(x, y) g(y) dy| < ε`. -/
theorem exists_forall_abs_greenPotential_sub_lt_of_ae_convergence {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {K : Set ℂ} (hKU : K ⊆ U) (hK : IsCompact K)
    {f : ℕ → ℂ → ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) volume)
    {g : ℂ → ℝ} (hg : AEStronglyMeasurable g volume) {M : ℝ}
    (hfM : ∀ n, ∀ᵐ y ∂(volume : Measure ℂ), |f n y| ≤ M)
    (hgM : ∀ᵐ y ∂(volume : Measure ℂ), |g y| ≤ M)
    (hconv : ∀ᵐ y ∂(volume : Measure ℂ), Tendsto (fun n => f n y) atTop (𝓝 (g y)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ x ∈ K,
      |(∫ y, greenFunction U x y * f n y) - ∫ y, greenFunction U x y * g y| < ε := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (Metric.tendstoUniformlyOn_iff.mp
      (tendstoUniformlyOn_greenPotential_of_ae_convergence hU hUb hKU hK hf hg hfM hgM hconv) ε hε)
  refine ⟨N, fun n hn x hx => ?_⟩
  have h := hN n hn x hx
  rw [Real.dist_eq, abs_sub_comm] at h
  exact h

/-- The packaged compact-set stability of Green potentials of a.e.-convergent bounded densities. Under the
hypotheses of `tendstoUniformlyOn_greenPotential_of_ae_convergence`, with `K ⊆ U` compact:
* every literal integrand `y ↦ G_U(x, y) f n(y)` and `y ↦ G_U(x, y) g(y)` is integrable, for every pole `x`;
* the literal Green potentials converge uniformly over `x ∈ K`;
* explicitly, for every `ε > 0` there is `N` with `|∫ G_U(x, y) f n(y) dy - ∫ G_U(x, y) g(y) dy| < ε` for
  all `n ≥ N` and all `x ∈ K`. -/
theorem greenPotential_boundedAE_convergence_compact {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {K : Set ℂ} (hKU : K ⊆ U) (hK : IsCompact K)
    {f : ℕ → ℂ → ℝ} (hf : ∀ n, AEStronglyMeasurable (f n) volume)
    {g : ℂ → ℝ} (hg : AEStronglyMeasurable g volume) {M : ℝ}
    (hfM : ∀ n, ∀ᵐ y ∂(volume : Measure ℂ), |f n y| ≤ M)
    (hgM : ∀ᵐ y ∂(volume : Measure ℂ), |g y| ≤ M)
    (hconv : ∀ᵐ y ∂(volume : Measure ℂ), Tendsto (fun n => f n y) atTop (𝓝 (g y))) :
    (∀ n x, Integrable (fun y => greenFunction U x y * f n y) volume) ∧
    (∀ x, Integrable (fun y => greenFunction U x y * g y) volume) ∧
    TendstoUniformlyOn (fun n x => ∫ y, greenFunction U x y * f n y)
      (fun x => ∫ y, greenFunction U x y * g y) atTop K ∧
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ x ∈ K,
      |(∫ y, greenFunction U x y * f n y) - ∫ y, greenFunction U x y * g y| < ε :=
  ⟨fun n x => integrable_greenFunction_mul_bdd hU hUb (hf n) (hfM n) x,
    fun x => integrable_greenFunction_mul_bdd hU hUb hg hgM x,
    tendstoUniformlyOn_greenPotential_of_ae_convergence hU hUb hKU hK hf hg hfM hgM hconv,
    fun _ hε => exists_forall_abs_greenPotential_sub_lt_of_ae_convergence hU hUb hKU hK hf hg hfM hgM
      hconv hε⟩

end HarmonicBalls
