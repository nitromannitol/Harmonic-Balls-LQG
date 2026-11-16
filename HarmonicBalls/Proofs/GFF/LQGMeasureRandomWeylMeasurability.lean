import HarmonicBalls.Proofs.GFF.LQGMeasureContinuumWeylScaling
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-!
# Measurability of the LQG measure reweighted by a random continuous function

Let `F : Ω → ℂ → ℝ` be a random continuous function: `F ω` is continuous for every `ω` and
`ω ↦ F ω z` is measurable for every `z`. For a measurable random measure `μ` on `ℂ`, the random
measure `ω ↦ (μ ω).withDensity (exp (γ F ω))` is measurable. No finiteness of `μ ω` is used. The
density is bounded below by step functions on square grids whose values are infima over a countable
dense set, and Fatou's lemma writes each mass as a limit inferior of measurable functions of `ω`.

For the LQG measure `μ_h` of the field `h = h^ℂ - α log |·|`, the reweighted measure is
`μ_{h+F} = e^{γ F} μ_h` (Fact 2.1 III, with `f` random continuous as allowed at line 406). On one
almost sure event, the circle-average approximations of `h + F` converge to it at all positive
radii, tested against every continuous compactly supported function. Since the LQG measure is
almost everywhere measurable as a measure-valued map, the reweighted measure is almost everywhere
measurable without a measurability hypothesis on `μ`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls

namespace RandomWeylMeasurability

/-- The index of the grid square of mesh `1 / (n + 1)` containing `z`. -/
private noncomputable def gridIndex (n : ℕ) (z : ℂ) : ℤ × ℤ :=
  (⌊((n : ℝ) + 1) * z.re⌋, ⌊((n : ℝ) + 1) * z.im⌋)

/-- The open grid square of mesh `1 / (n + 1)` with index `p`. -/
private def gridBox (n : ℕ) (p : ℤ × ℤ) : Set ℂ :=
  Ioo ((p.1 : ℝ) / ((n : ℝ) + 1)) (((p.1 : ℝ) + 1) / ((n : ℝ) + 1)) ×ℂ
    Ioo ((p.2 : ℝ) / ((n : ℝ) + 1)) (((p.2 : ℝ) + 1) / ((n : ℝ) + 1))

/-- The infimum of `g` over the points of the dense sequence in an open grid square. -/
private noncomputable def gridInf (g : ℂ → ℝ≥0∞) (n : ℕ) (p : ℤ × ℤ) : ℝ≥0∞ :=
  ⨅ (k : ℕ) (_ : TopologicalSpace.denseSeq ℂ k ∈ gridBox n p), g (TopologicalSpace.denseSeq ℂ k)

private theorem measurable_gridIndex (n : ℕ) : Measurable (gridIndex n) :=
  ((measurable_const.mul Complex.measurable_re).floor).prodMk
    ((measurable_const.mul Complex.measurable_im).floor)

private theorem isOpen_gridBox (n : ℕ) (p : ℤ × ℤ) : IsOpen (gridBox n p) :=
  isOpen_Ioo.reProdIm isOpen_Ioo

private theorem mem_Icc_floor {N : ℝ} (hN : 0 < N) (r : ℝ) :
    r ∈ Icc ((⌊N * r⌋ : ℝ) / N) (((⌊N * r⌋ : ℝ) + 1) / N) := by
  have h1 := Int.floor_le (N * r)
  have h2 := Int.lt_floor_add_one (N * r)
  constructor
  · rw [div_le_iff₀ hN]
    linarith [mul_comm N r]
  · rw [le_div_iff₀ hN]
    linarith [mul_comm N r]

private theorem div_ne_add_one_div {N : ℝ} (hN : 0 < N) (a : ℝ) : a / N ≠ (a + 1) / N :=
  (div_lt_div_of_pos_right (by linarith) hN).ne

private theorem mem_closure_gridBox (n : ℕ) (z : ℂ) : z ∈ closure (gridBox n (gridIndex n z)) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [gridBox, Complex.closure_reProdIm, closure_Ioo (div_ne_add_one_div hN _),
    closure_Ioo (div_ne_add_one_div hN _)]
  exact ⟨mem_Icc_floor hN z.re, mem_Icc_floor hN z.im⟩

private theorem abs_sub_le_of_mem {N a x y : ℝ} (hx : x ∈ Icc (a / N) ((a + 1) / N))
    (hy : y ∈ Ioo (a / N) ((a + 1) / N)) : |y - x| ≤ 1 / N := by
  have e : (a + 1) / N = a / N + 1 / N := add_div _ _ _
  rw [e] at hx hy
  exact abs_sub_le_iff.mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩

private theorem dist_le_of_mem_gridBox (n : ℕ) (z : ℂ) {y : ℂ} (hy : y ∈ gridBox n (gridIndex n z)) :
    dist y z ≤ 2 / ((n : ℝ) + 1) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hz := mem_closure_gridBox n z
  rw [gridBox, Complex.closure_reProdIm, closure_Ioo (div_ne_add_one_div hN _),
    closure_Ioo (div_ne_add_one_div hN _)] at hz
  have hre := abs_sub_le_of_mem hz.1 hy.1
  have him := abs_sub_le_of_mem hz.2 hy.2
  rw [Complex.dist_eq]
  calc ‖y - z‖ ≤ |(y - z).re| + |(y - z).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ 1 / ((n : ℝ) + 1) + 1 / ((n : ℝ) + 1) := by
        rw [Complex.sub_re, Complex.sub_im]
        exact add_le_add hre him
    _ = 2 / ((n : ℝ) + 1) := by ring

private theorem gridInf_le {g : ℂ → ℝ≥0∞} (hg : Continuous g) (n : ℕ) (z : ℂ) :
    gridInf g n (gridIndex n z) ≤ g z := by
  set p := gridIndex n z
  have hsub : gridBox n p ∩ range (TopologicalSpace.denseSeq ℂ) ⊆ {y | gridInf g n p ≤ g y} := by
    rintro y ⟨hy, k, rfl⟩
    change gridInf g n p ≤ g (TopologicalSpace.denseSeq ℂ k)
    unfold gridInf
    exact iInf₂_le k hy
  have hcl : IsClosed {y | gridInf g n p ≤ g y} := isClosed_le continuous_const hg
  have hz : z ∈ closure (gridBox n p ∩ range (TopologicalSpace.denseSeq ℂ)) := by
    have h1 := Dense.open_subset_closure_inter (TopologicalSpace.denseRange_denseSeq ℂ)
      (isOpen_gridBox n p)
    have h2 := closure_mono h1 (mem_closure_gridBox n z)
    rwa [closure_closure] at h2
  exact closure_minimal hsub hcl hz

private theorem le_liminf_gridInf {g : ℂ → ℝ≥0∞} (hg : Continuous g) (z : ℂ) :
    g z ≤ liminf (fun n => gridInf g n (gridIndex n z)) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun t ht => ?_
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (isOpen_lt continuous_const hg) z ht
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / δ)
  refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  refine le_iInf₂ fun k hk => (hball ?_).le
  have hd := dist_le_of_mem_gridBox n z hk
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlt : 2 / ((n : ℝ) + 1) < δ := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  exact mem_ball.mpr (by linarith)

end RandomWeylMeasurability

open RandomWeylMeasurability in
/-- **Measurability of a random measure reweighted by a random continuous density.** If `m` is a
measurable random measure on `ℂ` and `g ω` is continuous for every `ω` with `ω ↦ g ω z` measurable
for every `z`, then `ω ↦ (m ω).withDensity (g ω)` is measurable. No finiteness of `m ω` is
assumed. -/
theorem measurable_withDensity_of_continuous {Ω : Type*} [MeasurableSpace Ω] {m : Ω → Measure ℂ}
    (hm : Measurable m) {g : Ω → ℂ → ℝ≥0∞} (hgc : ∀ ω, Continuous (g ω))
    (hgm : ∀ z, Measurable fun ω => g ω z) :
    Measurable fun ω => (m ω).withDensity (g ω) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp_rw [withDensity_apply _ hs]
  have hstep : ∀ n ω, ∫⁻ z in s, gridInf (g ω) n (gridIndex n z) ∂(m ω) =
      ∑' p : ℤ × ℤ, gridInf (g ω) n p * m ω (gridIndex n ⁻¹' {p} ∩ s) := by
    intro n ω
    rw [← lintegral_map (f := gridInf (g ω) n) (g := gridIndex n) (measurable_of_countable _)
      (measurable_gridIndex n), lintegral_countable']
    refine tsum_congr fun p => ?_
    rw [Measure.map_apply (measurable_gridIndex n) (measurableSet_singleton p),
      Measure.restrict_apply (measurable_gridIndex n (measurableSet_singleton p))]
  have hstepm : ∀ n, Measurable fun ω => ∫⁻ z in s, gridInf (g ω) n (gridIndex n z) ∂(m ω) := by
    intro n
    simp_rw [hstep]
    refine Measurable.tsum fun p => Measurable.mul ?_ ?_
    · simp only [gridInf]
      exact Measurable.iInf fun k => Measurable.iInf fun _ => hgm _
    · exact (Measure.measurable_coe
        ((measurable_gridIndex n (measurableSet_singleton p)).inter hs)).comp hm
  have hlim : ∀ ω, ∫⁻ z in s, g ω z ∂(m ω) =
      liminf (fun n => ∫⁻ z in s, gridInf (g ω) n (gridIndex n z) ∂(m ω)) atTop := by
    intro ω
    apply le_antisymm
    · calc ∫⁻ z in s, g ω z ∂(m ω)
          ≤ ∫⁻ z in s, liminf (fun n => gridInf (g ω) n (gridIndex n z)) atTop ∂(m ω) :=
            lintegral_mono fun z => le_liminf_gridInf (hgc ω) z
        _ ≤ _ := lintegral_liminf_le (f := fun n z => gridInf (g ω) n (gridIndex n z)) fun n =>
            (measurable_of_countable (gridInf (g ω) n)).comp (measurable_gridIndex n)
    · refine Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_)
      exact lintegral_mono fun z => gridInf_le (hgc ω) n z
  simp_rw [hlim]
  exact Measurable.liminf hstepm

/-- The random measure `ω ↦ e^{γ F ω} μ_ω` is measurable for a measurable random measure `μ` and a
random continuous function `F`. -/
theorem measurable_withDensity_exp_of_continuous {Ω : Type*} [MeasurableSpace Ω]
    {μ : Ω → Measure ℂ} (hμ : Measurable μ) (γ : ℝ) {F : Ω → ℂ → ℝ}
    (hFc : ∀ ω, Continuous (F ω)) (hFm : ∀ z, Measurable fun ω => F ω z) :
    Measurable fun ω => (μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * F ω z)) :=
  measurable_withDensity_of_continuous hμ
    (fun ω => ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul (hFc ω))))
    (fun z => (measurable_const.mul (hFm z)).exp.ennreal_ofReal)

/-- For the LQG measure `μ_h` of a whole-plane field and a random continuous function `F`, the random
measure `ω ↦ e^{γ F ω} μ_h(ω)` is almost everywhere measurable. -/
theorem IsWholePlaneGFF.aemeasurable_withDensity_exp_lqgMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) {γ α : ℝ}
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    {F : Ω → ℂ → ℝ} (hFc : ∀ ω, Continuous (F ω)) (hFm : ∀ z, Measurable fun ω => F ω z) :
    AEMeasurable (fun ω => (μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * F ω z))) P := by
  have hae := hh.aemeasurable_lqgMeasure hμ
  refine ⟨fun ω => (hae.mk μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * F ω z)),
    measurable_withDensity_exp_of_continuous hae.measurable_mk γ hFc hFm, ?_⟩
  filter_upwards [hae.ae_eq_mk] with ω hω
  rw [hω]

/-- **Weyl scaling for a random continuous shift.** Let `h = h^ℂ - α log |·|` be a whole-plane field
with `0 < γ < 2` and `α < Q`, let `μ` be its LQG measure, measurable as a random measure, and let
`F` be a random continuous function. Then the random measure `μ_{h+F} = e^{γ F} μ_h` is measurable,
and almost surely the circle-average approximations of `h + F` converge to it at all positive radii,
tested against every continuous compactly supported function. -/
theorem measurable_and_ae_tendsto_integral_lqgApprox_continuum_add_random
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc)
    {γ α : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ)
    {μ : Ω → Measure ℂ} (hμ : IsLQGMeasureOfField P γ α hcirc μ) (hμm : Measurable μ)
    {F : Ω → ℂ → ℝ} (hFc : ∀ ω, Continuous (F ω)) (hFm : ∀ z, Measurable fun ω => F ω z) :
    Measurable (fun ω => (μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * F ω z))) ∧
      ∀ᵐ ω ∂P, ∀ φ : ℂ → ℝ, Continuous φ → HasCompactSupport φ →
        Tendsto (fun s : ℝ =>
            ∫ z, φ z ∂(lqgApprox γ (addCircleAverage (fieldCircleAverage α (hcirc ω)) (F ω)) s))
          (𝓝[>] 0)
          (𝓝 (∫ z, φ z ∂((μ ω).withDensity fun z => ENNReal.ofReal (Real.exp (γ * F ω z))))) := by
  refine ⟨measurable_withDensity_exp_of_continuous hμm γ hFc hFm, ?_⟩
  filter_upwards [ae_tendsto_integral_lqgApprox_continuum_add_continuous hh hγ0 hγ2 hαQ hμ]
    with ω hω
  exact hω (F ω) (hFc ω)

end HarmonicBalls
