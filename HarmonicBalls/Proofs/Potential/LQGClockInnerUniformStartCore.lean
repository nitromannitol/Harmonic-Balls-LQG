import HarmonicBalls.Proofs.Potential.LQGClockInnerFirstMoment
import HarmonicBalls.Proofs.Potential.BrownianSingularShiftedRieszEnergy

/-! # Inner occupation first moments uniformly over the Brownian start

The expected unit-time occupation of a small disc around a singular point, weighted by the
singular power, decays like a power of the radius with a constant independent of the
Brownian start and of the centre. Consequently the expected inner occupations of the inserted
field have a first-moment bound uniform over the Brownian start.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- Singular occupation of a small disc, uniformly over the start and the centre. -/
theorem exists_planarBrownianMotion_unit_singular_occupation_tail_le_uniform {q p : ℝ}
    (hq : 0 < q) (hqp : q < p) (hp : p < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (x z : ℂ) (δ : ℝ), 0 < δ →
      (∫⁻ b, ∫⁻ t : ℝ≥0,
        (if ‖b t - z‖ < δ then (ENNReal.ofReal ‖b t - z‖) ^ (-q) else 0)
          ∂(Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
          ∂(planarBrownianMotion x)) ≤ (ENNReal.ofReal δ) ^ (p - q) * C := by
  have hp0 : 0 < p := lt_trans hq hqp
  obtain ⟨C, hC, hCle⟩ := exists_planarBrownianMotion_unit_singular_occupation_le hp0 hp
  refine ⟨C, hC, fun x z δ hδ => ?_⟩
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hδ0 : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  have hbound (b : ContinuousPath ℂ) (t : ℝ≥0) :
      (if ‖b t - z‖ < δ then (ENNReal.ofReal ‖b t - z‖) ^ (-q) else 0) ≤
        (ENNReal.ofReal δ) ^ (p - q) * (ENNReal.ofReal ‖b t - z‖) ^ (-p) := by
    split_ifs with h
    · by_cases ha : ENNReal.ofReal ‖b t - z‖ = 0
      · simp [ha, ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr hp0),
          (ENNReal.rpow_pos_of_nonneg hδ0 (show 0 ≤ p - q by linarith)).ne']
      · have hle : ENNReal.ofReal ‖b t - z‖ ≤ ENNReal.ofReal δ :=
          ENNReal.ofReal_le_ofReal h.le
        have hr := ENNReal.rpow_le_rpow hle (show 0 ≤ p - q by linarith)
        calc
          _ = (ENNReal.ofReal ‖b t - z‖) ^ (-p) *
              (ENNReal.ofReal ‖b t - z‖) ^ (p - q) := by
                rw [← ENNReal.rpow_add _ _ ha ENNReal.ofReal_ne_top]
                congr 1; ring
          _ ≤ (ENNReal.ofReal ‖b t - z‖) ^ (-p) * (ENNReal.ofReal δ) ^ (p - q) :=
            mul_le_mul_of_nonneg_left hr zero_le
          _ = _ := mul_comm _ _
    · exact bot_le
  have hne : (ENNReal.ofReal δ) ^ (p - q) ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
  calc
    _ ≤ ∫⁻ b, ∫⁻ t : ℝ≥0, (ENNReal.ofReal δ) ^ (p - q) *
        (ENNReal.ofReal ‖b t - z‖) ^ (-p) ∂ν ∂(planarBrownianMotion x) :=
      lintegral_mono fun b => lintegral_mono (hbound b)
    _ = ∫⁻ b, (ENNReal.ofReal δ) ^ (p - q) *
        (∫⁻ t : ℝ≥0, (ENNReal.ofReal ‖b t - z‖) ^ (-p) ∂ν) ∂(planarBrownianMotion x) := by
      congr 1; funext b
      rw [lintegral_const_mul' _ _ hne]
    _ = (ENNReal.ofReal δ) ^ (p - q) * ∫⁻ b, ∫⁻ t : ℝ≥0,
        (ENNReal.ofReal ‖b t - z‖) ^ (-p) ∂ν ∂(planarBrownianMotion x) := by
      rw [lintegral_const_mul' _ _ hne]
    _ ≤ (ENNReal.ofReal δ) ^ (p - q) * C := mul_le_mul_of_nonneg_left (hCle x z) zero_le

/-- The expected inner occupation of the inserted field has a power bound in the radius,
uniformly over the Brownian start and over measures below the unit-time occupation. -/
theorem exists_uniform_inner_inserted_density_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α p : ℝ)
    (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (x : ℂ) {ε δ : ℝ}, 0 < ε → ε ≤ 1/2 → 0 < δ → δ ≤ 1/2 →
      ∀ μ : ContinuousPath ℂ → Measure ℂ, (∀ b, SFinite (μ b)) →
      (∀ b, μ b ≤ (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).map b) →
      (∫⁻ b, ∫⁻ ω, ∫⁻ z, {z : ℂ | ‖z‖ < δ}.indicator
        (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z ∂(μ b) ∂P
            ∂(planarBrownianMotion x)) ≤ (ENNReal.ofReal δ) ^ (p - γ * α) * C := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_planarBrownianMotion_unit_singular_occupation_tail_le_uniform hq hqp hp
  refine ⟨C, hC, ?_⟩
  intro x ε δ hε hεhalf hδ hδhalf μ hμs hμ
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hmeas : Measurable (fun z : ℂ =>
      if ‖z‖ < δ then (ENNReal.ofReal ‖z‖) ^ (-(γ * α)) else 0) := by
    exact Measurable.ite (measurableSet_lt measurable_norm measurable_const) (by fun_prop)
      measurable_const
  calc
    _ ≤ ∫⁻ b, ∫⁻ z, (if ‖z‖ < δ then (ENNReal.ofReal ‖z‖) ^ (-(γ * α)) else 0)
          ∂(μ b) ∂(planarBrownianMotion x) := by
      apply lintegral_mono
      intro b
      let : SFinite (μ b) := hμs b
      exact lintegral_inner_inserted_density_le hh hε hεhalf hδhalf γ α hq (μ b)
    _ ≤ ∫⁻ b, ∫⁻ z, (if ‖z‖ < δ then (ENNReal.ofReal ‖z‖) ^ (-(γ * α)) else 0)
          ∂(ν.map b) ∂(planarBrownianMotion x) := by
      apply lintegral_mono
      intro b
      exact lintegral_mono' (hμ b) le_rfl
    _ = ∫⁻ b, ∫⁻ t : ℝ≥0,
        (if ‖b t - (0 : ℂ)‖ < δ then (ENNReal.ofReal ‖b t - (0 : ℂ)‖) ^ (-(γ * α)) else 0)
          ∂ν ∂(planarBrownianMotion x) := by
      apply lintegral_congr
      intro b
      rw [lintegral_map hmeas b.continuous.measurable]
      simp only [sub_zero]
    _ ≤ _ := hbound x 0 δ hδ


/-- Occupation of a small disc, uniformly over the start and the centre. -/
theorem exists_planarBrownianMotion_unit_ball_occupation_le_uniform {p : ℝ}
    (hp0 : 0 < p) (hp : p < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (x z : ℂ) (δ : ℝ), 0 < δ →
      (∫⁻ b, ∫⁻ t : ℝ≥0, (if ‖b t - z‖ < δ then (1 : ℝ≥0∞) else 0) ∂(Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))
          ∂(planarBrownianMotion x)) ≤ (ENNReal.ofReal δ) ^ p * C := by
  obtain ⟨C, hC, hCle⟩ := exists_planarBrownianMotion_unit_singular_occupation_le hp0 hp
  refine ⟨C, hC, fun x z δ hδ => ?_⟩
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hδ0 : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.mpr hδ
  have hne : (ENNReal.ofReal δ) ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp0.le ENNReal.ofReal_ne_top
  have hbound (b : ContinuousPath ℂ) (t : ℝ≥0) :
      (if ‖b t - z‖ < δ then (1 : ℝ≥0∞) else 0) ≤
        (ENNReal.ofReal δ) ^ p * (ENNReal.ofReal ‖b t - z‖) ^ (-p) := by
    split_ifs with h
    · have hle : ENNReal.ofReal ‖b t - z‖ ≤ ENNReal.ofReal δ := ENNReal.ofReal_le_ofReal h.le
      have hanti : (ENNReal.ofReal δ) ^ (-p) ≤ (ENNReal.ofReal ‖b t - z‖) ^ (-p) := by
        rw [ENNReal.rpow_neg, ENNReal.rpow_neg]
        exact ENNReal.inv_le_inv.mpr (ENNReal.rpow_le_rpow hle hp0.le)
      calc (1 : ℝ≥0∞) = (ENNReal.ofReal δ) ^ p * (ENNReal.ofReal δ) ^ (-p) := by
            rw [ENNReal.rpow_neg, ENNReal.mul_inv_cancel
              (ENNReal.rpow_pos hδ0 ENNReal.ofReal_ne_top).ne' hne]
        _ ≤ _ := mul_le_mul_of_nonneg_left hanti zero_le
    · exact zero_le
  calc
    _ ≤ ∫⁻ b, ∫⁻ t : ℝ≥0, (ENNReal.ofReal δ) ^ p *
        (ENNReal.ofReal ‖b t - z‖) ^ (-p) ∂ν ∂(planarBrownianMotion x) :=
      lintegral_mono fun b => lintegral_mono (hbound b)
    _ = (ENNReal.ofReal δ) ^ p * ∫⁻ b, ∫⁻ t : ℝ≥0,
        (ENNReal.ofReal ‖b t - z‖) ^ (-p) ∂ν ∂(planarBrownianMotion x) := by
      simp_rw [lintegral_const_mul' _ _ hne]
    _ ≤ (ENNReal.ofReal δ) ^ p * C := mul_le_mul_of_nonneg_left (hCle x z) zero_le

/-- For a nonpositive insertion, the expected inner occupation of the inserted field has a
power bound in the radius, uniformly over the Brownian start and over measures below the
unit-time occupation. -/
theorem exists_uniform_inner_inserted_density_le_of_nonpos {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α p : ℝ)
    (hq : γ * α ≤ 0) (hp0 : 0 < p) (hp : p < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (x : ℂ) {ε δ : ℝ}, 0 < ε → ε ≤ 1/2 → 0 < δ → δ ≤ 1/2 →
      ∀ μ : ContinuousPath ℂ → Measure ℂ, (∀ b, SFinite (μ b)) →
      (∀ b, μ b ≤ (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).map b) →
      (∫⁻ b, ∫⁻ ω, ∫⁻ z, {z : ℂ | ‖z‖ < δ}.indicator
        (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z ∂(μ b) ∂P
            ∂(planarBrownianMotion x)) ≤ (ENNReal.ofReal δ) ^ p * C := by
  obtain ⟨C, hC, hbound⟩ := exists_planarBrownianMotion_unit_ball_occupation_le_uniform hp0 hp
  refine ⟨C, hC, ?_⟩
  intro x ε δ hε hεhalf hδ hδhalf μ hμs hμ
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hmeas : Measurable (fun z : ℂ => if ‖z‖ < δ then (1 : ℝ≥0∞) else 0) :=
    Measurable.ite (measurableSet_lt measurable_norm measurable_const) measurable_const
      measurable_const
  calc
    _ = ∫⁻ b, ∫⁻ z, {z : ℂ | ‖z‖ < δ}.indicator
          (fun z => ENNReal.ofReal (Real.exp (-(γ * α) * Real.log (max ε ‖z‖)))) z
          ∂(μ b) ∂(planarBrownianMotion x) := by
      apply lintegral_congr
      intro b
      let : SFinite (μ b) := hμs b
      exact lintegral_inner_inserted_density_eq hh hε hεhalf hδhalf γ α (μ b)
    _ ≤ ∫⁻ b, ∫⁻ z, (if ‖z‖ < δ then (1 : ℝ≥0∞) else 0) ∂(μ b) ∂(planarBrownianMotion x) := by
      apply lintegral_mono
      intro b
      apply lintegral_mono
      intro z
      simp only
      by_cases hz : ‖z‖ < δ
      · rw [Set.indicator_of_mem (show z ∈ {z : ℂ | ‖z‖ < δ} from hz)]
        simp only [hz, ↓reduceIte]
        apply ENNReal.ofReal_le_one.mpr
        apply Real.exp_le_one_iff.mpr
        have hmax : max ε ‖z‖ ≤ 1 := max_le (by linarith) (by linarith)
        have hlog : Real.log (max ε ‖z‖) ≤ 0 :=
          Real.log_nonpos (le_trans hε.le (le_max_left _ _)) hmax
        nlinarith
      · rw [Set.indicator_of_notMem (show z ∉ {z : ℂ | ‖z‖ < δ} from hz)]
        simp only [hz, ↓reduceIte, le_refl]
    _ ≤ ∫⁻ b, ∫⁻ z, (if ‖z‖ < δ then (1 : ℝ≥0∞) else 0) ∂(ν.map b)
          ∂(planarBrownianMotion x) := by
      apply lintegral_mono
      intro b
      exact lintegral_mono' (hμ b) le_rfl
    _ = ∫⁻ b, ∫⁻ t : ℝ≥0,
        (if ‖b t - (0 : ℂ)‖ < δ then (1 : ℝ≥0∞) else 0) ∂ν ∂(planarBrownianMotion x) := by
      apply lintegral_congr
      intro b
      rw [lintegral_map hmeas b.continuous.measurable]
      simp only [sub_zero]
    _ ≤ _ := hbound x 0 δ hδ

end HarmonicBalls
