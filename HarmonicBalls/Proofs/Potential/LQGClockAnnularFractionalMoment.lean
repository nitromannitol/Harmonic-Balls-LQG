import HarmonicBalls.Proofs.Potential.LQGClockAnnularCoarseCellMoment

/-! # Fractional moments of annular clock cells

At scales bounded away from zero, the actual annular clock cell has moments
of orders at most two uniformly over Brownian starting points and time cells.
-/

open MeasureTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- At smoothing scales bounded below by `η`, annular clock cells have a
fractional moment bound, uniformly in the Brownian start and cell location. -/
theorem lintegral_prod_brownian_annular_cell_rpow_le_of_scale_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {η ε : ℝ} (hη : 0 < η) (hηε : η ≤ ε) (hε : ε ≤ 1)
    (γ α δ u h : ℝ) {p : ℝ} (hp : 0 < p) (hp2 : p ≤ 2) :
    (∫⁻ q : Ω × ContinuousPath ℂ, (∫⁻ s in Ioc u (u + h), ENNReal.ofReal
      ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal))) ^ p
          ∂(P.prod (planarBrownianMotion x))) ≤
      (ENNReal.ofReal (2 * (Real.exp (|γ * α| * |Real.log η|) ^ 2 *
        Real.exp (((2 * γ) ^ 2 / 2) * (-Real.log η + 2 * Real.log 3))))) ^ (p / 2) *
          (ENNReal.ofReal h) ^ p := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let μ := P.prod (planarBrownianMotion x)
  let X : Ω × ContinuousPath ℂ → ℝ≥0∞ := fun q =>
    ∫⁻ s in Ioc u (u + h), ENNReal.ofReal
      ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal))
  let C : ℝ≥0∞ := ENNReal.ofReal (2 * (Real.exp (|γ * α| * |Real.log η|) ^ 2 *
    Real.exp (((2 * γ) ^ 2 / 2) * (-Real.log η + 2 * Real.log 3))))
  have hX : AEMeasurable X μ :=
    aemeasurable_annular_inserted_clock_cell hh (planarBrownianMotion x)
      (hη.trans_le hηε) γ α δ u (u + h)
  have hsq : (∫⁻ q, X q ^ (2 : ℝ) ∂μ) ≤ C * (ENNReal.ofReal h) ^ (2 : ℝ) := by
    simpa only [μ, X, C, ENNReal.rpow_ofNat] using
      lintegral_prod_brownian_annular_cell_sq_le_of_scale_lower_bound
        hh x hη hηε hε γ α δ u h
  change (∫⁻ q, X q ^ p ∂μ) ≤ C ^ (p / 2) * (ENNReal.ofReal h) ^ p
  calc
    _ = ∫⁻ q, (X q ^ (2 : ℝ)) ^ (p / 2) ∂μ := by
      congr 1
      funext q
      rw [← ENNReal.rpow_mul]
      congr 1
      ring
    _ ≤ (∫⁻ q, X q ^ (2 : ℝ) ∂μ) ^ (p / 2) :=
      LatticeProb.lintegral_rpow_le_rpow_lintegral μ (by positivity) (by linarith)
        (hX.pow_const (2 : ℝ))
    _ ≤ (C * (ENNReal.ofReal h) ^ (2 : ℝ)) ^ (p / 2) :=
      ENNReal.rpow_le_rpow hsq (by positivity)
    _ = C ^ (p / 2) * (ENNReal.ofReal h) ^ p := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul]
      congr 1
      ring

/-- Coarse-scale annular mesh cells have an explicit moment decay, uniformly
in the scale above the cutoff, the cell index and the Brownian start. -/
theorem lintegral_prod_brownian_annular_mesh_cell_rpow_le_of_scale_lower_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {η ε : ℝ} (hη : 0 < η) (hηε : η ≤ ε) (hε : ε ≤ 1)
    (γ α δ : ℝ) {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (m : ℕ) (hm : 0 < m) (j : Fin m) :
    (∫⁻ q : Ω × ContinuousPath ℂ,
      (∫⁻ s in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m), ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) ε z)) (q.2 s.toNNReal))) ^ p
          ∂(P.prod (planarBrownianMotion x))) ≤
      (ENNReal.ofReal (2 * (Real.exp (|γ * α| * |Real.log η|) ^ 2 *
        Real.exp (((2 * γ) ^ 2 / 2) * (-Real.log η + 2 * Real.log 3))))) ^ (p / 2) *
          (m : ℝ≥0∞) ^ (-p) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hend : ((j : ℝ) / m) + 1 / (m : ℝ) = ((j : ℝ) + 1) / m := by ring
  have hrpow : (ENNReal.ofReal (1 / (m : ℝ))) ^ p = (m : ℝ≥0∞) ^ (-p) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hm0, ENNReal.ofReal_natCast,
      ENNReal.inv_rpow, ← ENNReal.rpow_neg]
  have hbound := lintegral_prod_brownian_annular_cell_rpow_le_of_scale_lower_bound
    hh x hη hηε hε γ α δ ((j : ℝ) / m) (1 / (m : ℝ)) (by linarith : 0 < p) hp2
  rwa [hend, hrpow] at hbound

end HarmonicBalls
