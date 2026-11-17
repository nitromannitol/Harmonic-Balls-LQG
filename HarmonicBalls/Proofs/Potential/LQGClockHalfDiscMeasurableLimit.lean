import HarmonicBalls.Proofs.Potential.LQGClockHalfDiscHorizon
import HarmonicBalls.Proofs.Potential.LQGClockAnnularGlobalMeasurableLimit

/-! # Measurable half-disc clock limit

The dyadic half-disc clocks have a jointly measurable locally uniform limit
in the parameter range of the inner cutoff estimates.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

/-- At each fixed start, the half-disc clock limit has a jointly measurable
field, path and time representative with regular time paths. -/
theorem exists_measurable_locally_uniform_limit_halfDiscClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ) (hγ2 : γ^2 < 2)
    (hsub : γ ^ 2 / 2 < 2 * (2-γ*α) / (2+γ*α)) :
    ∃ F : (Ω × ContinuousPath ℂ) × ℝ≥0 → ℝ, Measurable F ∧
      (∀ p, Continuous (fun t => F (p,t)) ∧ (∀ t, 0 ≤ F (p,t)) ∧
        Monotone (fun t => F (p,t))) ∧
      ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
          |(∫ s in (0 : ℝ)..(t : ℝ),
            {z : ℂ | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
              (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
                LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+1)) z))
                  (p.2 s.toNNReal)) - F (p,t)| < η := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let B : Set ℂ := {z | (0 : ℝ) ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hB : MeasurableSet B := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let Z (j : ℕ) (ω : Ω) (z : ℂ) : ℝ := (dyadicScale (j+1))^(γ^2/2) *
    Real.exp (γ * (H ω (dyadicScale (j+1)) z - α * Real.log (max (dyadicScale (j+1)) ‖z‖)))
  have hZm (j : ℕ) : Measurable (fun p : Ω × ℂ => Z j p.1 p.2) := by
    have he : Measurable (fun p : Ω × ℂ => H p.1 (dyadicScale (j+1)) p.2) :=
      (hHm _ (dyadicScale_pos (j+1))).comp measurable_swap
    exact measurable_const.mul (measurable_const.mul (he.sub (measurable_const.mul
      ((measurable_const.max measurable_snd.norm).log)))).exp
  let A (j : ℕ) (p : (Ω × ContinuousPath ℂ) × ℝ≥0) : ℝ :=
    ∫ s in (0 : ℝ)..(p.2 : ℝ), B.indicator (Z j p.1.1) (p.1.2 s.toNNReal)
  have hAm (j : ℕ) : Measurable (A j) := by
    have hev : Measurable (fun p : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
        p.1.1.2 p.2.toNNReal) :=
      (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable.comp
        (measurable_fst.fst.snd.prodMk measurable_snd)
    have hI : Measurable (fun p : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ =>
        B.indicator (Z j p.1.1.1) (p.1.1.2 p.2.toNNReal)) := by
      convert (hZm j).comp (measurable_fst.fst.fst.prodMk hev) |>.indicator
        (hev hB) using 1
      ext p
      rfl
    have hS : MeasurableSet {p : ((Ω × ContinuousPath ℂ) × ℝ≥0) × ℝ |
        0 < p.2 ∧ p.2 ≤ (p.1.2 : ℝ)} :=
      (measurableSet_lt measurable_const measurable_snd).inter
        (measurableSet_le measurable_snd (measurable_coe_nnreal_real.comp measurable_fst.snd))
    have h := (hI.indicator hS).stronglyMeasurable.integral_prod_right' (ν := volume)
    convert h.measurable using 1
    ext p
    dsimp only [A]
    rw [intervalIntegral.integral_of_le p.2.coe_nonneg, ← integral_indicator measurableSet_Ioc]
    rfl
  have hAe : ∀ᵐ ω ∂P, ∀ j b t,
      A j ((ω,b),t) = ∫ s in (0 : ℝ)..(t : ℝ), B.indicator (fun z =>
        (dyadicScale (j+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale (j+1)) z))
            (b s.toNNReal) := by
    filter_upwards [hHae] with ω hω j b t
    apply intervalIntegral.integral_congr
    intro s hs
    apply congrArg (fun f : ℂ → ℝ => B.indicator f (b s.toNNReal))
    funext z
    have he : H ω (dyadicScale (j+1)) z = hcirc ω (dyadicScale (j+1)) z := hω _ _
    have hl : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z (dyadicScale (j+1)) =
        Real.log (max (dyadicScale (j+1)) ‖z‖) := by
      simpa using LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 (dyadicScale_pos (j+1))
    simp only [Z, LatticeProb.Gauss.fieldCircleAverage, hl, he]
  have hconv : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)), ∃ G : ℝ≥0 → ℝ,
      Continuous G ∧ (∀ t, 0 ≤ G t) ∧ Monotone G ∧
      ∀ T : ℝ≥0, ∀ η : ℝ, 0 < η → ∀ᶠ j in atTop, ∀ t : ℝ≥0, t ≤ T →
        |A j (p,t) - G t| < η := by
    filter_upwards [ae_exists_locally_uniform_limit_halfDiscClock hh x hq0 hq2 hγ hγ2 hsub,
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hAe]
      with p hp he
    obtain ⟨G, hGc, hG0, hGm, hG⟩ := hp
    refine ⟨G, hGc, hG0, hGm, ?_⟩
    intro T η hη
    filter_upwards [hG T η hη] with j hj t ht
    rw [he j p.2 t]
    exact hj t ht
  obtain ⟨F, hFm, hFr, hF⟩ :=
    exists_measurable_locally_uniform_limit (P.prod (planarBrownianMotion x)) A hAm hconv
  refine ⟨F, hFm, hFr, ?_⟩
  filter_upwards [hF, (Measure.quasiMeasurePreserving_fst
    (μ := P) (ν := planarBrownianMotion x)).ae hAe] with p hp he
  intro T η hη
  filter_upwards [hp T η hη] with j hj t ht
  have h := hj t ht
  rw [he j p.2 t] at h
  exact h

end HarmonicBalls
