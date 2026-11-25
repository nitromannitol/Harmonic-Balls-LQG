import HarmonicBalls.Proofs.Potential.ReflectedRevuzFormula
import LatticeProb.Prob.VitaliSquareBounded
import LatticeProb.MeasureTheory.ExtOfLintegralCompactlySupported

/-!
# Identification of the Revuz measure of a limit of clocks with densities

Let `A` be a positive continuous additive functional of reflected Brownian motion in the unit
square `K₀` and let `c_k(t, b) = ∫_0^t ρ_k(b_s) ds` be clocks with continuous densities `ρ_k ≥ 0`
that converge to `A`, uniformly on `[0, 1]` in probability, from every start in `K₀`. Suppose that
the expected occupation integrals `E_y ∫_{(0,1]} ρ_k(b_s) ds` are bounded uniformly in `k` and
`y ∈ K₀`, and that `ρ_k dz` on `K₀` converges to a finite measure `ν` against continuous
compactly supported test functions. Then the Revuz measure of `A` is `ν`
(`unitSquareRevuzMeasure_eq_of_density_clocks`).

The proof, for a test function `f ≥ 0`: under the path law `P` of reflected Brownian motion started
from Lebesgue measure on `K₀` (`unitSquareLebesguePathLaw`), the occupation integrals
`X_k = ∫_{(0,1]} f ρ_k(b_s) ds` converge in measure to the occupation integral of `A`
(`tendstoInMeasure_integral_clockOccupationMeasure`, dominated convergence in the start), and
have bounded second moments (`lintegral_windowOccupation_sq_le`), so their means converge
(Vitali's theorem, `LatticeProb.tendsto_integral_of_tendstoInMeasure_of_lintegral_sq_le`). By the
invariance of Lebesgue measure the mean of `X_k` is `∫_{K₀} f ρ_k`, and by the Revuz formula the
mean of the limit is `∫ f d(Rev A)`. Two measures with the same integrals of all such `f` agree
(`LatticeProb.ext_of_lintegral_ofReal_eq_of_hasCompactSupport`).

Credit: the argument follows MatedCRT/FirstPass/Derived/OccupationBallLawInMeasure.lean,
OccupationBallLawL2Bound.lean, OccupationBallLawVitali.lean and OccupationBallLawAssembly.lean of
the IDLA-Mated-CRT formalization (planar Brownian motion started from Lebesgue measure on discs),
here for reflected Brownian motion in the unit square, which needs no passage to the whole plane.
Source commit: IDLA-Mated-CRT ea80b70d7b8c8c59778c86b6bd4b06c1060b6fbe.
Changes: planar Brownian motion started from Lebesgue measure on discs (`ballLaw`) replaced by
reflected Brownian motion started from Lebesgue measure on `K₀` (`unitSquareLebesguePathLaw`); the
tail truncation over the plane dropped; the approximate Liouville clocks replaced by any clocks with
continuous densities and a uniform Green bound; proofs otherwise as in the source.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Topology MarkovProcess
open scoped ENNReal NNReal

/-- The law of reflected Brownian motion in the unit square started from Lebesgue measure on the
unit square. -/
noncomputable def unitSquareLebesguePathLaw : Measure (ContinuousPath ℂ) :=
  ((volume : Measure ℂ).restrict (closedSquare 0 1)).bind (reflectedPlanarBrownianMotion 0 1)

theorem unitSquareLebesguePathLaw_apply {S : Set (ContinuousPath ℂ)} (hS : MeasurableSet S) :
    unitSquareLebesguePathLaw S =
      ∫⁻ z in closedSquare 0 1, reflectedPlanarBrownianMotion 0 1 z S :=
  Measure.bind_apply hS (reflectedPlanarBrownianMotion 0 1).measurable.aemeasurable

instance isFiniteMeasure_unitSquareLebesguePathLaw : IsFiniteMeasure unitSquareLebesguePathLaw :=
  ⟨by
    rw [unitSquareLebesguePathLaw_apply MeasurableSet.univ]
    simp only [measure_univ, lintegral_const, one_mul, Measure.restrict_apply_univ]
    exact (isCompact_closedSquare 0 1).measure_lt_top⟩

theorem lintegral_unitSquareLebesguePathLaw {F : ContinuousPath ℂ → ℝ≥0∞}
    (hF : AEMeasurable F unitSquareLebesguePathLaw) :
    ∫⁻ b, F b ∂unitSquareLebesguePathLaw =
      ∫⁻ z in closedSquare 0 1, ∫⁻ b, F b ∂(reflectedPlanarBrownianMotion 0 1 z) :=
  Measure.lintegral_bind (reflectedPlanarBrownianMotion 0 1).measurable.aemeasurable hF

/-- **Convergence in measure from every start gives convergence in measure from Lebesgue
measure** (dominated convergence in the start). -/
theorem tendstoInMeasure_unitSquareLebesguePathLaw_of_forall {X : ℕ → ContinuousPath ℂ → ℝ}
    {Φ : ContinuousPath ℂ → ℝ} (hX : ∀ k, Measurable (X k)) (hΦ : Measurable Φ)
    (h : ∀ z ∈ closedSquare 0 1, TendstoInMeasure (reflectedPlanarBrownianMotion 0 1 z) X atTop Φ) :
    TendstoInMeasure unitSquareLebesguePathLaw X atTop Φ := by
  intro ε hε
  have hS : ∀ k, MeasurableSet {b | ε ≤ edist (X k b) (Φ b)} := fun k =>
    measurableSet_le measurable_const ((hX k).edist hΦ)
  simp_rw [unitSquareLebesguePathLaw_apply (hS _)]
  have := tendsto_lintegral_of_dominated_convergence
    (μ := (volume : Measure ℂ).restrict (closedSquare 0 1))
    (F := fun k z => reflectedPlanarBrownianMotion 0 1 z {b | ε ≤ edist (X k b) (Φ b)})
    (f := fun _ => 0) (fun _ => 1)
    (fun k => (reflectedPlanarBrownianMotion 0 1).measurable_coe (hS k))
    (fun k => ae_of_all _ fun z => prob_le_one)
    (by
      simp only [lintegral_const, one_mul, Measure.restrict_apply_univ]
      exact (isCompact_closedSquare 0 1).measure_lt_top.ne)
    ((ae_restrict_iff' (isCompact_closedSquare 0 1).isClosed.measurableSet).2
      (ae_of_all _ fun z hz => h z hz ε hε))
  simpa using this

/-- **The expected window occupation integral under the Lebesgue-started law** is the integral
over the unit square (invariance of Lebesgue measure). -/
theorem lintegral_windowOccupation_unitSquareLebesguePathLaw {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ b, windowOccupation g b ∂unitSquareLebesguePathLaw = ∫⁻ z in closedSquare 0 1, g z := by
  have hev : ∀ s : ℝ≥0, Measurable fun b : ContinuousPath ℂ => g (b s) := fun s =>
    hg.comp (continuous_eval_const s).measurable
  rw [lintegral_windowOccupation_eq hg]
  have h : ∀ s : ℝ, ∫⁻ b, g (b s.toNNReal) ∂unitSquareLebesguePathLaw =
      ∫⁻ z in closedSquare 0 1, g z := fun s => by
    rw [lintegral_unitSquareLebesguePathLaw (hev _).aemeasurable,
      lintegral_lintegral_reflectedPlanarBrownianMotion_eval _ hg]
  simp_rw [h]
  rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]

/-- A clock with a continuous density `φ ≥ 0` is nondecreasing and continuous. -/
theorem monotone_continuous_of_density {φ : ℝ → ℝ} (hφ : Continuous φ) (hφ0 : ∀ s, 0 ≤ φ s)
    {c : ℝ≥0 → ℝ≥0} (hc : ∀ t : ℝ≥0, (c t : ℝ) = ∫ s in (0 : ℝ)..t, φ s) :
    Monotone c ∧ Continuous c := by
  have hint : ∀ u v : ℝ, IntervalIntegrable φ volume u v := fun u v => hφ.intervalIntegrable u v
  refine ⟨fun s t hst => ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, hc, hc, ← intervalIntegral.integral_add_adjacent_intervals
      (hint 0 s) (hint s t), le_add_iff_nonneg_right]
    exact intervalIntegral.integral_nonneg (by exact_mod_cast hst) fun u _ => hφ0 u
  · refine continuous_induced_rng.2 ?_
    have h : Continuous fun t : ℝ => ∫ s in (0 : ℝ)..t, φ s :=
      intervalIntegral.continuous_primitive hint 0
    convert h.comp NNReal.continuous_coe using 1
    funext t
    exact hc t

/-- The occupation measure of a path along a clock is a finite measure. -/
theorem isFiniteMeasure_clockOccupationMeasure (a : ℝ≥0 → ℝ≥0) (b : ContinuousPath ℂ) :
    IsFiniteMeasure (clockOccupationMeasure a b) := by
  unfold clockOccupationMeasure
  have : IsFiniteMeasure ((clockStieltjesFunction a).measure.restrict (Ioc (0 : ℝ) 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  infer_instance

theorem windowOccupation_const_mul_le {g : ℂ → ℝ≥0∞} (hg : Measurable g) {h : ℂ → ℝ≥0∞}
    {K : ℝ≥0∞} (hh : ∀ z, h z ≤ K * g z) (b : ContinuousPath ℂ) :
    windowOccupation h b ≤ K * windowOccupation g b := by
  unfold windowOccupation
  rw [← lintegral_const_mul _ (show Measurable fun s : ℝ => g (b s.toNNReal) from
    hg.comp (b.continuous.comp continuous_real_toNNReal).measurable)]
  exact lintegral_mono fun s => hh _

theorem enorm_toReal_le_self' (x : ℝ≥0∞) : ‖x.toReal‖ₑ ≤ x := by
  rw [Real.enorm_eq_ofReal ENNReal.toReal_nonneg]
  exact ENNReal.ofReal_toReal_le

/-- **Identification of the Revuz measure of a limit of clocks with densities.** -/
theorem unitSquareRevuzMeasure_eq_of_density_clocks {A : ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hA : IsUnitSquarePCAF A) {ρ : ℕ → ℂ → ℝ} (hρc : ∀ k, Continuous (ρ k))
    (hρ0 : ∀ k z, 0 ≤ ρ k z) {c : ℕ → ℝ≥0 → ContinuousPath ℂ → ℝ≥0}
    (hc : ∀ k t b, (c k t b : ℝ) = ∫ s in (0 : ℝ)..t, ρ k (b s.toNNReal))
    (hconv : ∀ x ∈ closedSquare 0 1, ∀ η : ℝ, 0 < η → Tendsto (fun k =>
      reflectedPlanarBrownianMotion 0 1 x
        {b | ∃ t : ℝ≥0, t ≤ 1 ∧ η ≤ |(c k t b : ℝ) - (A t b : ℝ)|}) atTop (𝓝 0))
    {U : ℝ≥0∞} (hU : U ≠ ⊤) (hgreen : ∀ k, ∀ y ∈ closedSquare 0 1,
      ∫⁻ b, windowOccupation (fun z => ENNReal.ofReal (ρ k z)) b
        ∂(reflectedPlanarBrownianMotion 0 1 y) ≤ U)
    {ν : Measure ℂ} [IsFiniteMeasure ν]
    (hlim : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → 0 ≤ f →
      Tendsto (fun k => ∫⁻ z in closedSquare 0 1, ENNReal.ofReal (f z) * ENNReal.ofReal (ρ k z))
        atTop (𝓝 (∫⁻ z, ENNReal.ofReal (f z) ∂ν))) :
    unitSquareRevuzMeasure A = ν := by
  refine LatticeProb.ext_of_lintegral_ofReal_eq_of_hasCompactSupport fun f hf hfc hf0 => ?_
  have hf0' : ∀ x, 0 ≤ f x := hf0
  obtain ⟨K₀, hK₀⟩ := hf.bounded_above_of_compact_support hfc
  set K : ℝ := max K₀ 0 with hKdef
  have hfK : ∀ x, f x ≤ K := fun x => by
    have := hK₀ x
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0' x)] at this
    exact this.trans (le_max_left _ _)
  have hfm : Measurable fun x => ENNReal.ofReal (f x) := ENNReal.measurable_ofReal.comp hf.measurable
  have hρm : ∀ k, Measurable fun z => ENNReal.ofReal (ρ k z) := fun k =>
    ENNReal.measurable_ofReal.comp (hρc k).measurable
  set h : ℕ → ℂ → ℝ≥0∞ := fun k z => ENNReal.ofReal (f z) * ENNReal.ofReal (ρ k z) with hh
  have hhm : ∀ k, Measurable (h k) := fun k => hfm.mul (hρm k)
  have hhK : ∀ k z, h k z ≤ ENNReal.ofReal K * ENNReal.ofReal (ρ k z) := fun k z =>
    mul_le_mul' (ENNReal.ofReal_le_ofReal (hfK z)) le_rfl
  set U' : ℝ≥0∞ := ENNReal.ofReal K * U with hU'
  have hU'ne : U' ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top hU
  have hgreen' : ∀ k, ∀ y ∈ closedSquare 0 1,
      ∫⁻ b, windowOccupation (h k) b ∂(reflectedPlanarBrownianMotion 0 1 y) ≤ U' := by
    intro k y hy
    calc ∫⁻ b, windowOccupation (h k) b ∂(reflectedPlanarBrownianMotion 0 1 y)
        ≤ ∫⁻ b, ENNReal.ofReal K * windowOccupation (fun z => ENNReal.ofReal (ρ k z)) b
            ∂(reflectedPlanarBrownianMotion 0 1 y) :=
          lintegral_mono fun b => windowOccupation_const_mul_le (hρm k) (hhK k) b
      _ = ENNReal.ofReal K * ∫⁻ b, windowOccupation (fun z => ENNReal.ofReal (ρ k z)) b
            ∂(reflectedPlanarBrownianMotion 0 1 y) :=
          lintegral_const_mul _ (measurable_windowOccupation (hρm k))
      _ ≤ U' := mul_le_mul' le_rfl (hgreen k y hy)
  -- the clocks
  have hcb : ∀ k b, Monotone (fun t => c k t b) ∧ Continuous (fun t => c k t b) := fun k b =>
    monotone_continuous_of_density ((hρc k).comp (b.continuous.comp continuous_real_toNNReal))
      (fun s => hρ0 k _) (hc k · b)
  -- the occupation integrals of the approximating clocks
  set Y : ℕ → ContinuousPath ℂ → ℝ := fun k b => (windowOccupation (h k) b).toReal with hY
  have hYm : ∀ k, Measurable (Y k) := fun k => (measurable_windowOccupation (hhm k)).ennreal_toReal
  have hXY : ∀ k, (fun b => ∫ x, f x ∂clockOccupationMeasure (fun t => c k t b) b) = Y k := by
    intro k
    funext b
    exact integral_clockOccupationMeasure_of_density
      ((hρc k).comp (b.continuous.comp continuous_real_toNNReal)) (fun s => hρ0 k _)
      (hc k · b) b hf hf0'
  obtain ⟨Φ, hΦm, hΦ0, hΦ⟩ := exists_measurable_version_integral_clockOccupationMeasure hA hf hf0'
  -- convergence in measure from every start, then from Lebesgue measure
  have hstart : ∀ z ∈ closedSquare 0 1,
      TendstoInMeasure (reflectedPlanarBrownianMotion 0 1 z) Y atTop Φ := by
    intro z hz
    have h1 := tendstoInMeasure_integral_clockOccupationMeasure
      (μ := reflectedPlanarBrownianMotion 0 1 z) (A := c) (G := A)
      (fun k => ae_of_all _ fun b => ⟨(hcb k b).2, (hcb k b).1⟩)
      ((hA.path z hz).mono fun b hb => ⟨hb.2.1, hb.2.2⟩) (hconv z hz) hf
      (fun k => by rw [hXY k]; exact (hYm k).aestronglyMeasurable)
    exact h1.congr (fun k => by rw [hXY k]) (hΦ z hz)
  have hP := tendstoInMeasure_unitSquareLebesguePathLaw_of_forall hYm hΦm hstart
  -- second moments
  have hvol : volume (closedSquare (0 : ℂ) 1) ≠ ⊤ := (isCompact_closedSquare 0 1).measure_lt_top.ne
  set B : ℝ≥0∞ := 2 * (U' * U') * volume (closedSquare (0 : ℂ) 1) with hB
  have hBne : B ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top hU'ne hU'ne)) hvol
  have hsq : ∀ k, ∫⁻ b, ‖Y k b‖ₑ ^ 2 ∂unitSquareLebesguePathLaw ≤ (B.toNNReal : ℝ≥0∞) := by
    intro k
    rw [ENNReal.coe_toNNReal hBne]
    calc ∫⁻ b, ‖Y k b‖ₑ ^ 2 ∂unitSquareLebesguePathLaw
        ≤ ∫⁻ b, windowOccupation (h k) b ^ 2 ∂unitSquareLebesguePathLaw :=
          lintegral_mono fun b => pow_le_pow_left' (enorm_toReal_le_self' _) 2
      _ = ∫⁻ z in closedSquare 0 1, ∫⁻ b, windowOccupation (h k) b ^ 2
            ∂(reflectedPlanarBrownianMotion 0 1 z) :=
          lintegral_unitSquareLebesguePathLaw
            ((measurable_windowOccupation (hhm k)).pow_const 2).aemeasurable
      _ ≤ ∫⁻ z in closedSquare 0 1, 2 * (U' * U') := by
          refine setLIntegral_mono' (isCompact_closedSquare 0 1).isClosed.measurableSet
            fun z hz => ?_
          refine (lintegral_windowOccupation_sq_le (hhm k) (hgreen' k) z).trans ?_
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (hgreen' k z hz))
      _ = B := by rw [setLIntegral_const]
  obtain ⟨hint, htend⟩ := LatticeProb.tendsto_integral_of_tendstoInMeasure_of_lintegral_sq_le
    (μ := unitSquareLebesguePathLaw) (f := Y) (g := Φ) (K := B.toNNReal)
    (fun k => (hYm k).aestronglyMeasurable) hsq hP
  -- the means of the approximations
  have hmean : ∀ k, ∫ b, Y k b ∂unitSquareLebesguePathLaw =
      (∫⁻ z in closedSquare 0 1, h k z).toReal := by
    intro k
    have hfin : ∫⁻ b, windowOccupation (h k) b ∂unitSquareLebesguePathLaw ≠ ⊤ := by
      rw [lintegral_unitSquareLebesguePathLaw (measurable_windowOccupation (hhm k)).aemeasurable]
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hU'ne hvol) ?_
      calc ∫⁻ z in closedSquare 0 1, ∫⁻ b, windowOccupation (h k) b
            ∂(reflectedPlanarBrownianMotion 0 1 z)
          ≤ ∫⁻ z in closedSquare 0 1, U' :=
            setLIntegral_mono' (isCompact_closedSquare 0 1).isClosed.measurableSet
              fun z hz => hgreen' k z hz
        _ = U' * volume (closedSquare (0 : ℂ) 1) := setLIntegral_const _ _
    rw [hY, integral_toReal (measurable_windowOccupation (hhm k)).aemeasurable
      (ae_lt_top (measurable_windowOccupation (hhm k)) hfin),
      lintegral_windowOccupation_unitSquareLebesguePathLaw (hhm k)]
  have hνfin : ∫⁻ z, ENNReal.ofReal (f z) ∂ν ≠ ⊤ := by
    refine ne_top_of_le_ne_top
      (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := K)) (measure_ne_top ν univ)) ?_
    calc ∫⁻ z, ENNReal.ofReal (f z) ∂ν ≤ ∫⁻ _, ENNReal.ofReal K ∂ν :=
          lintegral_mono fun z => ENNReal.ofReal_le_ofReal (hfK z)
      _ = ENNReal.ofReal K * ν univ := lintegral_const _
  have hlim' : Tendsto (fun k => ∫ b, Y k b ∂unitSquareLebesguePathLaw) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (f z) ∂ν).toReal) := by
    simp_rw [hmean]
    exact (ENNReal.tendsto_toReal hνfin).comp (hlim f hf hfc hf0)
  have hΦint : ∫ b, Φ b ∂unitSquareLebesguePathLaw = (∫⁻ z, ENNReal.ofReal (f z) ∂ν).toReal :=
    tendsto_nhds_unique htend hlim'
  -- the Revuz side
  rw [lintegral_unitSquareRevuzMeasure_of_isUnitSquarePCAF hA hfm]
  have hocc : ∀ b : ContinuousPath ℂ, ∫⁻ x, ENNReal.ofReal (f x) ∂clockOccupationMeasure
      (fun t => A t b) b = ENNReal.ofReal (∫ x, f x ∂clockOccupationMeasure (fun t => A t b) b) := by
    intro b
    have := isFiniteMeasure_clockOccupationMeasure (fun t => A t b) b
    exact (ofReal_integral_eq_lintegral_ofReal (hf.integrable_of_hasCompactSupport hfc)
      (ae_of_all _ hf0')).symm
  calc ∫⁻ z in closedSquare 0 1, ∫⁻ b, ∫⁻ x, ENNReal.ofReal (f x) ∂clockOccupationMeasure
        (fun t => A t b) b ∂(reflectedPlanarBrownianMotion 0 1 z)
      = ∫⁻ z in closedSquare 0 1, ∫⁻ b, ENNReal.ofReal (Φ b)
          ∂(reflectedPlanarBrownianMotion 0 1 z) := by
        refine setLIntegral_congr_fun (isCompact_closedSquare 0 1).isClosed.measurableSet
          fun z hz => lintegral_congr_ae ?_
        filter_upwards [hΦ z hz] with b hb
        rw [hocc b, hb]
    _ = ∫⁻ b, ENNReal.ofReal (Φ b) ∂unitSquareLebesguePathLaw :=
        (lintegral_unitSquareLebesguePathLaw (ENNReal.measurable_ofReal.comp hΦm).aemeasurable).symm
    _ = ENNReal.ofReal (∫ b, Φ b ∂unitSquareLebesguePathLaw) :=
        (ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hΦ0)).symm
    _ = ∫⁻ z, ENNReal.ofReal (f z) ∂ν := by rw [hΦint, ENNReal.ofReal_toReal hνfin]

end HarmonicBalls
