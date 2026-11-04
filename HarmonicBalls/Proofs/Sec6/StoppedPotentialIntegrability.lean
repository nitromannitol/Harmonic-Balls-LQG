import HarmonicBalls.Proofs.Sec6.GreenPotentialStoppedReduction
import MarkovProcess.Trajectory.ExitLaw

/-!
# Integrability of stopped potentials

A bounded measurable potential evaluated at the exit time of a bounded open set
is integrable under planar Brownian motion.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Set Filter MarkovProcess Metric
open scoped ENNReal NNReal Topology

/-- Bounded measurable functions of a finite Brownian exit position are integrable. -/
theorem integrable_at_exitTime_of_bounded_measurable
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    {q : ℂ → ℝ} (hq : Measurable q) {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M) (x : ℂ) :
    Integrable (fun ω : ContinuousPath ℂ =>
      q (ω ((ContinuousPath.exitTime D ω).toNNReal))) (planarBrownianMotion x) := by
  have hmeas : Measurable (fun ω : ContinuousPath ℂ =>
      q (ω ((ContinuousPath.exitTimeTop D ω).untopD 0))) :=
    hq.comp (ContinuousPath.measurable_eval_untopD_exitTimeTop D hD)
  have hint : Integrable (fun ω : ContinuousPath ℂ =>
      q (ω ((ContinuousPath.exitTimeTop D ω).untopD 0))) (planarBrownianMotion x) :=
    Integrable.of_bound hmeas.aestronglyMeasurable M (Eventually.of_forall fun ω => hM _)
  apply hint.congr
  filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hDb] with ω hfin
  rw [ContinuousPath.untopD_exitTimeTop_eq_toNNReal D ω hfin.ne]

/-- A function continuous on the closure of a set and zero off that closure is
Borel measurable. -/
theorem measurable_of_continuousOn_closure_of_zero {U : Set ℂ} {q : ℂ → ℝ}
    (hcont : ContinuousOn q (closure U)) (hzero : ∀ y ∉ closure U, q y = 0) :
    Measurable q := by
  classical
  have hm : Measurable ((closure U).piecewise q (fun _ => 0)) :=
    hcont.measurable_piecewise continuousOn_const isClosed_closure.measurableSet
  convert hm using 1
  ext y
  by_cases hy : y ∈ closure U
  · simp [hy]
  · simp [hy, hzero y hy]

/-- A bounded measurable function's expectations at truncated exit times
converge to its expectation at the finite exit time. -/
theorem tendsto_integral_exitTimeTrunc_of_bounded_measurable
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    {q : ℂ → ℝ} (hq : Measurable q) {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M) (x : ℂ) :
    Tendsto (fun n : ℕ => ∫ ω : ContinuousPath ℂ,
      q (ω (ContinuousPath.exitTimeTrunc D n ω)) ∂(planarBrownianMotion x)) atTop
      (𝓝 (∫ ω : ContinuousPath ℂ,
        q (ω ((ContinuousPath.exitTime D ω).toNNReal)) ∂(planarBrownianMotion x))) := by
  apply tendsto_integral_of_dominated_convergence (fun _ => M)
  · intro n
    exact (hq.comp (ContinuousPath.measurable_eval_stoppingTime_borel _
      (ContinuousPath.isStoppingTime_exitTimeTrunc D hD n))).aestronglyMeasurable
  · exact integrable_const M
  · intro n
    exact Eventually.of_forall fun ω => hM _
  · filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hDb] with ω hfin
    obtain ⟨N, hN⟩ := exists_nat_ge (ContinuousPath.exitTime D ω).toNNReal
    have hevent : ∀ᶠ n : ℕ in atTop,
        q (ω (ContinuousPath.exitTimeTrunc D n ω)) =
          q (ω ((ContinuousPath.exitTime D ω).toNNReal)) := by
      filter_upwards [eventually_ge_atTop N] with n hn
      have hle : ContinuousPath.exitTime D ω ≤ (n : ℝ≥0∞) := by
        rw [← ENNReal.coe_toNNReal hfin.ne, ← ENNReal.coe_natCast, ENNReal.coe_le_coe]
        exact hN.trans (by exact_mod_cast hn)
      have ht : ContinuousPath.exitTimeTrunc D n ω =
          (ContinuousPath.exitTime D ω).toNNReal := by
        apply ENNReal.coe_injective
        have hle' : ContinuousPath.exitTime D ω ≤ ((n : ℝ≥0) : ℝ≥0∞) := by
          simpa only [ENNReal.coe_natCast] using hle
        rw [ContinuousPath.coe_exitTimeTrunc_ennreal, min_eq_left hle',
          ENNReal.coe_toNNReal hfin.ne]
      rw [ht]
    exact tendsto_const_nhds.congr' (hevent.mono fun _ hn => hn.symm)

/-- A lower bound for all truncated exit expectations persists at the full
exit time. -/
theorem integral_exitTime_lower_of_truncations
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D)
    {q : ℂ → ℝ} (hq : Measurable q) {M : ℝ} (hM : ∀ y, ‖q y‖ ≤ M)
    (x : ℂ) {a : ℝ}
    (htrunc : ∀ n : ℕ, a ≤ ∫ ω : ContinuousPath ℂ,
      q (ω (ContinuousPath.exitTimeTrunc D n ω)) ∂(planarBrownianMotion x)) :
    a ≤ ∫ ω : ContinuousPath ℂ,
      q (ω ((ContinuousPath.exitTime D ω).toNNReal)) ∂(planarBrownianMotion x) :=
  le_of_tendsto_of_tendsto tendsto_const_nhds
    (tendsto_integral_exitTimeTrunc_of_bounded_measurable hD hDb hq hM x)
    (Eventually.of_forall htrunc)

/-- Hölder regularity and a positive extrema ratio give integrability of the
restricted Green potential at the exit from the punctured domain. -/
theorem integrable_restricted_greenPotential_at_exitTime
    {μ : Measure ℂ} {U S L : Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hL : IsCompact L) (hLU : L ⊆ U)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure U)) →
      (∀ x ∈ closure U, IntegrableOn (fun y => greenFunction U x y * f y) U μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in U, greenFunction U x y * f y ∂μ) (closure U))
    (hpos : 0 < greenPotentialExtremaRatio U S μ) (x : ℂ) :
    Integrable (fun ω : ContinuousPath ℂ => ∫ y in L,
      greenFunction U (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal)) y ∂μ)
      (planarBrownianMotion x) := by
  obtain ⟨_, C, t, ht, hcont⟩ := hholder (L.indicator (fun _ => 1))
    ((memLp_top_const (1 : ℝ)).indicator hL.measurableSet)
  have heq : (fun z => ∫ y in U, greenFunction U z y * L.indicator (fun _ => 1) y ∂μ) =
      (fun z => ∫ y in L, greenFunction U z y ∂μ) := by
    funext z
    have hind : (fun y => greenFunction U z y * L.indicator (fun _ => 1) y) =
        L.indicator (greenFunction U z) := by
      funext y
      by_cases hy : y ∈ L <;> simp [hy]
    rw [hind, integral_indicator hL.measurableSet, Measure.restrict_restrict_of_subset hLU]
  rw [heq] at hcont
  have hmeas : Measurable (fun z => ∫ y in L, greenFunction U z y ∂μ) :=
    measurable_of_continuousOn_closure_of_zero (hcont.continuousOn ht) (by
      intro z hz
      have hzU : z ∉ U := fun hzU => hz (subset_closure hzU)
      simp only [greenFunction_of_notMem_left hzU, integral_zero])
  obtain ⟨_, hsuptop⟩ := greenPotential_sup_ne_zero_and_top_of_ratio_pos hpos
  have hint : ∀ z ∈ U, IntegrableOn (greenFunction U z) U μ := by
    obtain ⟨h, _⟩ := hholder (fun _ => 1) (memLp_top_const (1 : ℝ))
    intro z hz
    simpa only [mul_one] using h z (subset_closure hz)
  apply integrable_at_exitTime_of_bounded_measurable (hU.sdiff hL.isClosed)
    (hUb.subset sdiff_subset) hmeas (M :=
      (⨆ z : U, ENNReal.ofReal (greenPotential U μ z)).toReal) ?_ x
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (greenFunction_nonneg hUb z))]
  apply (restricted_greenPotential_le hUb hLU hint z).trans
  by_cases hz : z ∈ U
  · have hle := ENNReal.toReal_mono hsuptop
      (le_iSup (fun w : U => ENNReal.ofReal (greenPotential U μ w)) ⟨z, hz⟩)
    simpa only [ENNReal.toReal_ofReal (greenPotential_nonneg hUb μ z)] using hle
  · simp only [greenPotential, greenFunction_of_notMem_left hz, integral_zero]
    exact ENNReal.toReal_nonneg

/-- A real stopped Green-potential representation supplies the full-mass
compact-union hitting estimate, with integrability obtained from Hölder
regularity and the positive extrema ratio. -/
theorem greenPotentialExtremaRatio_hitting_union_of_real_stopped_representation
    {μ : Measure ℂ} {U S : Set ℂ} {K : ℕ → Set ℂ}
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hS : IsCompact S) (hSU : S ⊆ closure U)
    (hK : ∀ n, IsCompact (K n)) (hKmono : Monotone K)
    (hfull : μ (U \ ⋃ n, K n) = 0)
    (hholder : ∀ f : ℂ → ℝ, MemLp f ⊤ (μ.restrict (closure U)) →
      (∀ x ∈ closure U, IntegrableOn (fun y => greenFunction U x y * f y) U μ) ∧
      ∃ C t : ℝ≥0, 0 < t ∧
        HolderOnWith C t (fun x => ∫ y in U, greenFunction U x y * f y ∂μ) (closure U))
    (hpos : 0 < greenPotentialExtremaRatio U S μ)
    (hrep : ∀ L : Set ℂ, IsCompact L → L ⊆ U → ∀ x ∈ S, x ∉ L →
      (∫ y in L, greenFunction U x y ∂μ) ≤ ∫ ω,
        (∫ y in L, greenFunction U
          (ω ((ContinuousPath.exitTime (U \ L) ω).toNNReal)) y ∂μ)
            ∂(planarBrownianMotion x)) :
    ∀ x ∈ S, ENNReal.ofReal (greenPotentialExtremaRatio U S μ) ≤
      planarBrownianMotion x {ω | ContinuousPath.exitTime (⋃ n, K n)ᶜ ω ≤
        ContinuousPath.exitTime U ω} := by
  apply greenPotentialExtremaRatio_hitting_union_of_stopped_representation_off_obstacle
    hU hUb hS hSU hK hKmono hfull hholder hpos
  intro L hL hLU x hx hxL
  apply stopped_lintegral_representation_of_integral_representation U L
    (fun z => ∫ y in L, greenFunction U z y ∂μ) x
    (fun z => integral_nonneg (greenFunction_nonneg hUb z))
    (integrable_restricted_greenPotential_at_exitTime hU hUb hL hLU hholder hpos x)
    (hrep L hL hLU x hx hxL)

end HarmonicBalls.Section6
