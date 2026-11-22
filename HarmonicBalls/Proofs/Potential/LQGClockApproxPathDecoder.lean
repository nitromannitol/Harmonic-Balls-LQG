import HarmonicBalls.Defs.LBM

/-! # Measurable reconstruction of approximating clocks

The approximating clock `∫_0^t ε^{γ²/2} e^{γ u(b_s)} ds` of a continuous profile `u` and a path
`b` is a jointly measurable function of the pair `(u, b)`, where profiles `u : ℂ → ℝ` carry the
product (evaluation) σ-algebra: the density `ε^{γ²/2} e^{γ u(z)}` is the lower limit of its values
at the simple approximations of `z`, which depend measurably on `(u, z)` since each simple
function takes finitely many values, and the clock is the integral of this density along the path.
-/

open MeasureTheory MarkovProcess Filter Topology Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- For every `γ`, every scale `ε ≥ 0` and every time `t` there is a measurable map `D` on pairs
of a profile and a path that equals the approximating clock `∫_0^t ε^{γ²/2} e^{γ u(b_s)} ds`
whenever the profile `u` is continuous. -/
theorem exists_measurable_lqgClockApprox_decoder (γ : ℝ) {ε : ℝ} (hε : 0 ≤ ε) (t : ℝ≥0) :
    ∃ D : (ℂ → ℝ) × ContinuousPath ℂ → ℝ, Measurable D ∧
      ∀ u : ℂ → ℝ, Continuous u → ∀ b : ContinuousPath ℂ,
        D (u, b) = lqgClockApprox γ (fun _ => u) ε b t := by
  classical
  let A : ℕ → SimpleFunc ℂ ℂ := (stronglyMeasurable_id : StronglyMeasurable (id : ℂ → ℂ)).approx
  have hA : ∀ z : ℂ, Tendsto (fun n => A n z) atTop (𝓝 z) :=
    (stronglyMeasurable_id : StronglyMeasurable (id : ℂ → ℂ)).tendsto_approx
  have hm : ∀ n, Measurable (fun p : (ℂ → ℝ) × ℂ => p.1 (A n p.2)) := by
    intro n
    have h : Measurable (fun p : (ℂ → ℝ) × (A n).range => p.1 p.2) :=
      measurable_from_prod_countable_left fun z => measurable_pi_apply z.1
    have hAmeas : Measurable (fun p : (ℂ → ℝ) × ℂ =>
        (⟨A n p.2, SimpleFunc.mem_range_self _ _⟩ : (A n).range)) :=
      Measurable.subtype_mk ((A n).measurable.comp measurable_snd)
    exact h.comp (measurable_fst.prodMk hAmeas)
  let g : (ℂ → ℝ) × ℂ → ℝ≥0∞ := fun p =>
    Filter.liminf (fun n => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * p.1 (A n p.2)))) atTop
  have hg : Measurable g := by
    apply Measurable.liminf
    intro n
    exact (measurable_const.mul ((measurable_const.mul (hm n)).exp)).ennreal_ofReal
  have hg_eq (u : ℂ → ℝ) (hu : Continuous u) (z : ℂ) :
      g (u, z) = ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * u z)) := by
    apply Filter.Tendsto.liminf_eq
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((tendsto_const_nhds.mul (Real.continuous_exp.tendsto _ |>.comp
        (tendsto_const_nhds.mul ((hu.tendsto z).comp (hA z))))))
  have hpath : Measurable (fun q : ((ℂ → ℝ) × ContinuousPath ℂ) × ℝ => q.1.2 q.2.toNNReal) := by
    have hc : Continuous (fun q : ContinuousPath ℂ × ℝ => q.1 q.2.toNNReal) :=
      continuous_eval.comp (continuous_id.prodMap continuous_real_toNNReal)
    exact hc.measurable.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hint : Measurable (fun q : ((ℂ → ℝ) × ContinuousPath ℂ) × ℝ =>
      g (q.1.1, q.1.2 q.2.toNNReal)) :=
    hg.comp ((measurable_fst.comp measurable_fst).prodMk hpath)
  refine ⟨fun p => (∫⁻ s in Ioc (0 : ℝ) t, g (p.1, p.2 s.toNNReal)).toReal,
    (hint.lintegral_prod_right').ennreal_toReal, ?_⟩
  intro u hu b
  have hcont : Continuous (fun s : ℝ => ε ^ (γ ^ 2 / 2) * Real.exp (γ * u (b s.toNNReal))) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (hu.comp (b.continuous.comp continuous_real_toNNReal))))
  simp only [hg_eq u hu]
  rw [lqgClockApprox, intervalIntegral.integral_of_le t.coe_nonneg,
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun s =>
      mul_nonneg (Real.rpow_nonneg hε _) (Real.exp_pos _).le)
      hcont.aestronglyMeasurable]

end HarmonicBalls
