import HarmonicBalls.Proofs.Potential.GreenPoleL1Continuity

/-!
# Uniform row mass and stability of the Green potential of a bounded density

For a bounded open planar set `U` and a pole `x : ℂ`, the zero-extended Green row
`y ↦ G_U(x, y)` is `greenFunction U x` (value `0` off `U`, as in `Defs/Green.lean`, the Green function
of Armitage–Gardiner). This file proves:

* (row mass) there is `C ≥ 0`, depending only on `U`, such that every row is integrable on `ℂ` with
  `∫ G_U(x, y) dy ≤ C` for every pole `x` (`exists_greenFunction_row_integral_le`);
* (integrability) for a real density `f` that is measurable and bounded almost everywhere, the Green
  potential `y ↦ G_U(x, y) f(y)` is integrable for every pole (`integrable_greenFunction_mul_of_ae_bounded`);
* (explicit stability) if `ε ≥ 0` and `|f - g| ≤ ε` almost everywhere, then
  `|∫ G_U(x, y) f(y) dy - ∫ G_U(x, y) g(y) dy| ≤ C ε` for every `x : ℂ`, with `C` independent of the
  densities and of the pole (`abs_integral_greenFunction_mul_sub_le_of_row_bound`, packaged with the row
  mass in `exists_greenPotential_boundedDensity_stability`);
* (uniform convergence) if bounded measurable densities `F n` satisfy `|F n - f| ≤ ε n` almost everywhere
  against a bounded measurable limit `f`, with `ε n → 0`, then the Green potentials converge uniformly on `ℂ`
  (`tendstoUniformly_greenPotential_of_ae_error`).

Proof outline. Enclose `U ⊆ B(0, R)`. A row vanishes off `U`, so `∫_ℂ G_U(x, ·) = ∫_{B(0, R)} G_U(x, ·)`,
which is at most the uniform local volume estimate `C R² (1 + |log R|)` of `GreenLocalVolumeBound`.
The difference estimate follows from `|∫ G (f - g)| ≤ ∫ G |f - g| ≤ ε ∫ G`, using `G_U ≥ 0`.

Only `IsOpen U` and `IsBounded U` are assumed. No boundary regularity, no normal representative and no
literature input enter. The local volume estimate and the potential-theoretic infrastructure reached through
the import closure use work of Leonardo Bonanno, through the pinned Lattice-Probability (lean-v4.35) port.
-/

namespace HarmonicBalls

open MeasureTheory Filter Topology Real Metric

/-- Uniform row mass of the zero-extended Green rows: for a bounded open `U` there is `C ≥ 0`, depending
only on `U`, such that for every pole `x` the row `y ↦ G_U(x, y)` is integrable on `ℂ` with integral at
most `C`. -/
theorem exists_greenFunction_row_integral_le {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℂ, Integrable (greenFunction U x) ∧ (∫ y, greenFunction U x y) ≤ C := by
  obtain ⟨R, hR, hsub⟩ := hUb.subset_ball_lt 0 (0 : ℂ)
  obtain ⟨K, hK, hloc⟩ := exists_greenFunction_local_volume_bound hU hUb
  refine ⟨K * R ^ 2 * (1 + |Real.log R|),
    mul_nonneg (mul_nonneg hK (sq_nonneg R)) (by positivity), fun x => ?_⟩
  refine ⟨integrable_greenFunction_pole hU hUb x, ?_⟩
  have hzero : ∀ y, y ∉ ball (0 : ℂ) R → greenFunction U x y = 0 := fun y hy =>
    greenFunction_of_notMem_right (fun hyU => hy (hsub hyU)) x
  have heq : (∫ y, greenFunction U x y) = ∫ y in ball (0 : ℂ) R, greenFunction U x y :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  rw [heq]
  exact (hloc R hR x 0).2

/-- Integrability of the Green potential of a density bounded almost everywhere: for a bounded open `U`,
every pole `x`, and a measurable `f` with `|f| ≤ M` almost everywhere, the function
`y ↦ G_U(x, y) f(y)` is integrable on `ℂ`. -/
theorem integrable_greenFunction_mul_of_ae_bounded {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) (x : ℂ) {f : ℂ → ℝ} (hf : AEStronglyMeasurable f volume)
    {M : ℝ} (hfM : ∀ᵐ y ∂volume, |f y| ≤ M) :
    Integrable (fun y => greenFunction U x y * f y) volume := by
  have hbound : ∀ᵐ y ∂volume, ‖f y‖ ≤ M :=
    hfM.mono fun y hy => by rwa [Real.norm_eq_abs]
  exact (integrable_greenFunction_pole hU hUb x).mul_bdd hf hbound

/-- Explicit stability of the Green potential of a bounded density. If every row has integral at most `C`
and `|f - g| ≤ ε` almost everywhere with `ε ≥ 0`, then for every pole `x`,
`|∫ G_U(x, y) f(y) dy - ∫ G_U(x, y) g(y) dy| ≤ C ε`. -/
theorem abs_integral_greenFunction_mul_sub_le_of_row_bound {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {C : ℝ} (hC : ∀ x : ℂ, (∫ y, greenFunction U x y) ≤ C) (x : ℂ)
    {f g : ℂ → ℝ} (hf : AEStronglyMeasurable f volume) {Mf : ℝ} (hfM : ∀ᵐ y ∂volume, |f y| ≤ Mf)
    (hg : AEStronglyMeasurable g volume) {Mg : ℝ} (hgM : ∀ᵐ y ∂volume, |g y| ≤ Mg)
    {ε : ℝ} (hε : 0 ≤ ε) (hfg : ∀ᵐ y ∂volume, |f y - g y| ≤ ε) :
    |(∫ y, greenFunction U x y * f y) - (∫ y, greenFunction U x y * g y)| ≤ C * ε := by
  have hint_f := integrable_greenFunction_mul_of_ae_bounded hU hUb x hf hfM
  have hint_g := integrable_greenFunction_mul_of_ae_bounded hU hUb x hg hgM
  have key : (∫ y, greenFunction U x y * f y) - (∫ y, greenFunction U x y * g y)
      = ∫ y, greenFunction U x y * (f y - g y) := by
    simp only [mul_sub]
    exact (integral_sub hint_f hint_g).symm
  have hint_diff : Integrable (fun y => greenFunction U x y * (f y - g y)) volume := by
    refine (hint_f.sub hint_g).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply, mul_sub]
  have hint_row := integrable_greenFunction_pole hU hUb x
  rw [key]
  calc |∫ y, greenFunction U x y * (f y - g y)|
      ≤ ∫ y, |greenFunction U x y * (f y - g y)| := abs_integral_le_integral_abs
    _ ≤ ∫ y, greenFunction U x y * ε := by
        refine integral_mono_ae hint_diff.abs (hint_row.mul_const ε) ?_
        filter_upwards [hfg] with y hy
        rw [abs_mul, abs_of_nonneg (greenFunction_nonneg hUb x y)]
        exact mul_le_mul_of_nonneg_left hy (greenFunction_nonneg hUb x y)
    _ = (∫ y, greenFunction U x y) * ε := integral_mul_const ε (fun y => greenFunction U x y)
    _ ≤ C * ε := mul_le_mul_of_nonneg_right (hC x) hε

/-- Stability of the Green potentials of bounded densities, with one constant `C ≥ 0` depending only on `U`.
For measurable real densities `f`, `g`, each bounded almost everywhere, every Green potential is integrable
for every pole, and whenever `ε ≥ 0` and `|f - g| ≤ ε` almost everywhere,
`|∫ G_U(x, y) f(y) dy - ∫ G_U(x, y) g(y) dy| ≤ C ε` for every `x : ℂ`. -/
theorem exists_greenPotential_boundedDensity_stability {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : ℂ → ℝ), AEStronglyMeasurable f volume →
      AEStronglyMeasurable g volume →
      (∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ y ∂volume, |f y| ≤ M) →
      (∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ y ∂volume, |g y| ≤ M) →
      (∀ x : ℂ, Integrable (fun y => greenFunction U x y * f y) volume ∧
        Integrable (fun y => greenFunction U x y * g y) volume) ∧
      ∀ ε : ℝ, 0 ≤ ε → (∀ᵐ y ∂volume, |f y - g y| ≤ ε) →
        ∀ x : ℂ, |(∫ y, greenFunction U x y * f y) - (∫ y, greenFunction U x y * g y)| ≤ C * ε := by
  obtain ⟨C, hC0, hrow⟩ := exists_greenFunction_row_integral_le hU hUb
  refine ⟨C, hC0, fun f g hf hg hfb hgb => ?_⟩
  obtain ⟨_Mf, -, hfM⟩ := hfb
  obtain ⟨_Mg, -, hgM⟩ := hgb
  refine ⟨fun x => ⟨integrable_greenFunction_mul_of_ae_bounded hU hUb x hf hfM,
    integrable_greenFunction_mul_of_ae_bounded hU hUb x hg hgM⟩, fun ε hε hfg x => ?_⟩
  exact abs_integral_greenFunction_mul_sub_le_of_row_bound hU hUb (fun z => (hrow z).2) x
    hf hfM hg hgM hε hfg

/-- Uniform convergence of Green potentials on `ℂ`. Let `f` be a bounded measurable limit and `F n` bounded
measurable densities with `|F n - f| ≤ ε n` almost everywhere, where `ε n → 0`. Then
`∫ G_U(x, y) F n(y) dy → ∫ G_U(x, y) f(y) dy` uniformly in `x : ℂ`. -/
theorem tendstoUniformly_greenPotential_of_ae_error {U : Set ℂ} (hU : IsOpen U)
    (hUb : Bornology.IsBounded U) {f : ℂ → ℝ} (hf : AEStronglyMeasurable f volume)
    (hfM : ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ y ∂volume, |f y| ≤ M)
    (F : ℕ → ℂ → ℝ) (hF : ∀ n, AEStronglyMeasurable (F n) volume)
    (hFM : ∀ n, ∃ M : ℝ, 0 ≤ M ∧ ∀ᵐ y ∂volume, |F n y| ≤ M)
    (ε : ℕ → ℝ) (hεF : ∀ n, ∀ᵐ y ∂volume, |F n y - f y| ≤ ε n)
    (hεlim : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformly (fun n x => ∫ y, greenFunction U x y * F n y)
      (fun x => ∫ y, greenFunction U x y * f y) atTop := by
  obtain ⟨C, hC0, hrow⟩ := exists_greenFunction_row_integral_le hU hUb
  obtain ⟨_Mf, -, hfM'⟩ := hfM
  have hε0 : ∀ n, 0 ≤ ε n := fun n => by
    obtain ⟨y, hy⟩ := (hεF n).exists
    exact le_trans (abs_nonneg _) hy
  rw [Metric.tendstoUniformly_iff]
  intro δ hδ
  have hthr : 0 < δ / (C + 1) := div_pos hδ (by linarith)
  filter_upwards [hεlim.eventually (gt_mem_nhds hthr)] with n hn
  intro x
  obtain ⟨_Mn, -, hMn⟩ := hFM n
  have hdiff := abs_integral_greenFunction_mul_sub_le_of_row_bound hU hUb
    (fun z => (hrow z).2) x (hF n) hMn hf hfM' (hε0 n) (hεF n)
  have hC_small : C * ε n < δ := by
    have h1 : C * ε n ≤ C * (δ / (C + 1)) := mul_le_mul_of_nonneg_left hn.le hC0
    have h2 : C * (δ / (C + 1)) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt hdiff hC_small

end HarmonicBalls
