import HarmonicBalls.Proofs.Potential.LQGClockInnerUniformStartCore
import HarmonicBalls.Proofs.Potential.LQGClockEnvelopeAnnularIncrement

/-! # Field increments with bounded weights, uniformly over the Brownian start

For a bounded measurable weight supported in the disc `‖z‖ ≤ R - 1/2`, the expected dyadic
increments of the weighted circle-average densities normalized at radius `R`, integrated
against any measure below the unit-time occupation measure of a planar Brownian path, have one
summable bound for every start. The truncated second-moment estimate is applied to the weight
dominated by a singular weight of small exponent, with the weighted pair energy as envelope;
the expectations of the pair energy and of the singular occupation are bounded uniformly over
the start.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set Filter Topology
open scoped ENNReal NNReal
namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- For a bounded measurable weight supported in `‖z‖ ≤ R - 1/2`, the expected dyadic
increments of the weighted densities normalized at radius `R` against sub-occupation measures
of the unit-time Brownian occupation have a summable bound uniform over the start. -/
theorem exists_summable_uniform_bounded_weight_suboccupation_increment_bound
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {R : ℝ} (hR : 1 ≤ R) {g : ℂ → ℝ} (hg : Measurable g) {M : ℝ} (hM : 0 ≤ M)
    (hgM : ∀ z, |g z| ≤ M) (hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ R - 1/2) :
    ∃ c : ℕ → ℝ≥0∞, (∑' k, c k) ≠ ⊤ ∧ ∀ (k : ℕ) (y : ℂ) (μ : ContinuousPath ℂ → Measure ℂ),
      (∀ b, μ b ≤ Measure.map (fun t => b t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) →
      (∫⁻ p, ENNReal.ofReal |∫ z, g z *
          ((dyadicScale (k+2)) ^ (γ ^ 2 / 2) *
            Real.exp (γ * (hcirc p.1 (dyadicScale (k+2)) z - hcirc p.1 R 0)) -
          (dyadicScale (k+1)) ^ (γ ^ 2 / 2) *
            Real.exp (γ * (hcirc p.1 (dyadicScale (k+1)) z - hcirc p.1 R 0))) ∂(μ p.2)|
        ∂(P.prod (planarBrownianMotion y))) ≤ c k := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hγsq : γ ^ 2 / 2 < 2 := by nlinarith
  let q' : ℝ := (2 - γ ^ 2 / 2) / 3
  have hq'0 : 0 < q' := by dsimp [q']; linarith
  have hq'2 : q' < 2 := by dsimp [q']; nlinarith [sq_nonneg γ]
  let β : ℝ := γ ^ 2 / 2 + q'
  have hβl : γ ^ 2 / 2 < β := by dsimp [β]; linarith
  have hβ0 : 0 < β := by dsimp [β]; positivity
  have hqβ : q' + β < 2 := by dsimp [β, q']; linarith
  obtain ⟨θ, hγθ, hθ, hdecay⟩ := exists_annular_moment_exponent hγ hβl
  obtain ⟨CW, hCW, hCWle⟩ :=
    exists_planarBrownianMotion_unitSingularWeightedPairEnergy_le hq'0 hβ0 hqβ
  obtain ⟨Co, hCo, hCole⟩ := exists_planarBrownianMotion_unit_singular_occupation_le hq'0 hq'2
  let κ₁ : ℝ := (β - γ ^ 2 + (2 * γ - θ) ^ 2 / 2) / 2
  let κ₂ : ℝ := (θ - γ) ^ 2 / 2
  have hκ₁ : 0 < κ₁ := by dsimp [κ₁]; positivity
  have hκ₂ : 0 < κ₂ := by
    have : 0 < θ - γ := by linarith
    dsimp [κ₂]; positivity
  let L : ℝ := Real.exp (γ ^ 2 * Real.log 2) - 1
  have hL : 0 ≤ L := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hR0 : 0 < R := by linarith
  have hρ : 0 < R - 1/2 := by linarith
  let A₁ : ℝ := L * Real.exp (Real.log R * (2*γ^2-(2*γ-θ)^2/2)) * 2 ^ β / 2
  let A₂ : ℝ := 2 * Real.exp (Real.log R * (γ^2/2-(θ-γ)^2/2))
  have hA₁ : 0 ≤ A₁ := by positivity
  have hA₂ : 0 ≤ A₂ := by positivity
  let K : ℝ := (R - 1/2) ^ (-q') / (M + 1)
  have hK : 0 < K := div_pos (Real.rpow_pos_of_pos hρ _) (by linarith)
  have hK0 : K ≠ 0 := hK.ne'
  have hKi : 0 < K⁻¹ := inv_pos.mpr hK
  let ε : ℕ → ℝ := fun k => dyadicScale (k+1)
  have hεpos (k : ℕ) : 0 < ε k := dyadicScale_pos _
  have hεhalf (k : ℕ) : ε k ≤ 1/2 := by
    dsimp [ε, dyadicScale]
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hεstep (k : ℕ) : dyadicScale (k+2) = ε k / 2 := by
    dsimp [ε, dyadicScale]
    rw [show k + 2 = (k+1) + 1 by omega, pow_succ]
    ring
  let e₁ : ℕ → ℝ := fun k => Real.exp (Real.log (ε k) * κ₁)
  let e₂ : ℕ → ℝ := fun k => Real.exp (Real.log (ε k) * κ₂)
  have hsum (κ : ℝ) (hκ : 0 < κ) :
      Summable (fun k : ℕ => Real.exp (Real.log (ε k) * κ)) :=
    (summable_nat_add_iff 1).2 (LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hκ)
  have htsum (κ : ℝ) (hκ : 0 < κ) :
      (∑' k : ℕ, ENNReal.ofReal (Real.exp (Real.log (ε k) * κ))) ≠ ⊤ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => (Real.exp_pos _).le) (hsum κ hκ)]
    exact ENNReal.ofReal_ne_top
  let c : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal K⁻¹ *
    (ENNReal.ofReal A₁ * CW * ENNReal.ofReal (e₁ k) +
      ENNReal.ofReal (1/2) * ENNReal.ofReal (e₁ k) + ENNReal.ofReal A₂ * Co * ENNReal.ofReal (e₂ k))
  refine ⟨c, ?_, ?_⟩
  · simp only [c]
    rw [ENNReal.tsum_mul_left]
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
    rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
      ENNReal.tsum_mul_left]
    refine ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨?_, ?_⟩, ?_⟩
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCW.ne) (htsum κ₁ hκ₁)
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (htsum κ₁ hκ₁)
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCo.ne) (htsum κ₂ hκ₂)
  let g₀ : ℂ → ℝ := fun z => K * g z
  have hg₀m : Measurable g₀ := measurable_const.mul hg
  have hg₀q : ∀ z, ENNReal.ofReal |g₀ z| ≤ (ENNReal.ofReal ‖z - 0‖) ^ (-q') := by
    intro z
    rw [sub_zero]
    by_cases hz : g z = 0
    · simp [g₀, hz]
    · have hzs := hgs z hz
      by_cases hz0 : z = 0
      · rw [hz0, norm_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg (by linarith)]
        exact le_top
      · have hpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
        rw [ENNReal.ofReal_rpow_of_pos hpos]
        apply ENNReal.ofReal_le_ofReal
        have h1 : |g₀ z| ≤ (R - 1/2) ^ (-q') := by
          simp only [g₀, abs_mul, abs_of_pos hK]
          calc K * |g z| ≤ K * (M + 1) :=
                mul_le_mul_of_nonneg_left (by linarith [hgM z]) hK.le
            _ = (R - 1/2) ^ (-q') := by
              simp only [K]
              field_simp
        exact h1.trans (Real.rpow_le_rpow_of_nonpos hpos hzs (by linarith))
  have hg₀s : ∀ z, g₀ z ≠ 0 → ‖z‖ ≤ R - 1/2 := by
    intro z hz
    apply hgs z
    intro h
    apply hz
    simp [g₀, h]
  have hscale : ∀ r : ℝ, 0 < r → r ≤ 1/2 → ∀ (y : ℂ) (μ : ContinuousPath ℂ → Measure ℂ),
      (∀ b, μ b ≤ Measure.map (fun t => b t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) →
      (∫⁻ p, ENNReal.ofReal |∫ z, g z *
          ((r/2) ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc p.1 (r/2) z - hcirc p.1 R 0)) -
          r ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc p.1 r z - hcirc p.1 R 0))) ∂(μ p.2)|
        ∂(P.prod (planarBrownianMotion y))) ≤
      ENNReal.ofReal K⁻¹ *
        (ENNReal.ofReal A₁ * CW * ENNReal.ofReal (Real.exp (Real.log r * κ₁)) +
          ENNReal.ofReal (1/2) * ENNReal.ofReal (Real.exp (Real.log r * κ₁)) +
          ENNReal.ofReal A₂ * Co * ENNReal.ofReal (Real.exp (Real.log r * κ₂))) := by
    intro r hr hr2 y μ hμ
    have hfin (b : ContinuousPath ℂ) : IsFiniteMeasure (μ b) := by
      let : IsProbabilityMeasure (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))) :=
        ⟨by simp [Measure.map_apply continuous_real_toNNReal.measurable]⟩
      have : IsProbabilityMeasure (Measure.map (fun t => b t)
        (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) := inferInstance
      exact isFiniteMeasure_of_le _ (hμ b)
    let J : Ω → ContinuousPath ℂ → ℝ := fun ω b => ∫ z, g z *
      ((r/2) ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω (r/2) z - hcirc ω R 0)) -
        r ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω r z - hcirc ω R 0))) ∂(μ b)
    let J₀ : Ω → ContinuousPath ℂ → ℝ := fun ω b => ∫ z, g₀ z *
      ((r/2) ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω (r/2) z - hcirc ω R 0)) -
        r ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω r z - hcirc ω R 0))) ∂(μ b)
    have hJeq (ω : Ω) (b : ContinuousPath ℂ) : J ω b = K⁻¹ * J₀ ω b := by
      simp only [J, J₀, g₀]
      rw [← integral_const_mul]
      congr 1
      funext z
      rw [← mul_assoc, ← mul_assoc, inv_mul_cancel₀ hK0, one_mul]
    let W : ContinuousPath ℂ → ℝ≥0∞ := unitSingularWeightedPairEnergy 0 q' β
    have hWm : Measurable W := measurable_unitSingularWeightedPairEnergy 0 q' β
    have hWi : (∫⁻ b, W b ∂(planarBrownianMotion y)) ≠ ⊤ :=
      ((hCWle y 0).trans_lt hCW).ne
    obtain ⟨-, hHenv⟩ := integrable_toReal_pair_envelope_of_lintegral y 0 (q := q') (β := β) W
      hWm.aemeasurable hWi (Filter.Eventually.of_forall fun b r' hr' _ =>
        (unitSingularPairNear_le_rpow_mul_weightedPairEnergy 0 hβ0 hr' b).trans_eq
          (mul_comm _ _))
    have h4 := ae_brownian_singular_submeasure_field_increment_le_of_envelope hh y 0 hq'0 hq'2
      (fun b => (W b).toReal) hHenv
    let Rb : ContinuousPath ℂ → ℝ := fun b =>
      ((Real.exp (γ^2*Real.log 2)-1)*
        Real.exp (Real.log R * (2*γ^2-(2*γ-θ)^2/2))*
        (2^β * (W b).toReal)+1)/2 *
        Real.exp (Real.log r * ((β-γ^2+(2*γ-θ)^2/2)/2)) +
      2*unitSingularOccupationEnvelope 0 q' b *
        Real.exp (Real.log R * (γ^2/2-(θ-γ)^2/2))*
        Real.exp (Real.log r * ((θ-γ)^2/2))
    have hpath : ∀ᵐ b ∂(planarBrownianMotion y),
        (∫⁻ ω, ENNReal.ofReal |J ω b| ∂P) ≤ ENNReal.ofReal (K⁻¹ * Rb b) := by
      filter_upwards [h4] with b hb4
      have : IsFiniteMeasure (μ b) := hfin b
      have hgi : Integrable g (μ b) :=
        (integrable_const M).mono' hg.aestronglyMeasurable
          (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hgM z)
      have hJi : Integrable (fun ω => J ω b) P :=
        hh.integrable_integral_increment hr hR0 (μ b) hg hgi
          (fun z hz => by linarith [hgs z hz]) γ
      have h4b := hb4 g₀ hg₀m hg₀q (μ b) (hμ b) (R := R) (γ := γ) (θ := θ)
        hR0 hγθ.le hθ.le hg₀s r hr hr2
      rw [← ofReal_integral_eq_lintegral_ofReal hJi.abs
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      calc (∫ ω, |J ω b| ∂P) = ∫ ω, K⁻¹ * |J₀ ω b| ∂P := by
            congr 1
            funext ω
            rw [hJeq ω b, abs_mul, abs_of_pos hKi]
        _ = K⁻¹ * ∫ ω, |J₀ ω b| ∂P := integral_const_mul _ _
        _ ≤ K⁻¹ * Rb b := mul_le_mul_of_nonneg_left h4b hKi.le
    let e₁r : ℝ := Real.exp (Real.log r * κ₁)
    let e₂r : ℝ := Real.exp (Real.log r * κ₂)
    let occ : ContinuousPath ℂ → ℝ≥0∞ := fun b =>
      ∫⁻ t : ℝ≥0, (ENNReal.ofReal ‖b t - 0‖) ^ (-q') ∂(Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1)))
    have hoccm : Measurable occ := by
      have hf : Measurable (fun p : ContinuousPath ℂ × ℝ≥0 =>
          (ENNReal.ofReal ‖p.1 p.2 - 0‖) ^ (-q')) := by fun_prop
      exact Measurable.lintegral_prod_right hf
    have hRb (b : ContinuousPath ℂ) : Rb b = A₁ * (W b).toReal * e₁r +
        (1/2) * e₁r + A₂ * (occ b).toReal * e₂r := by
      simp only [Rb, unitSingularOccupationEnvelope, e₁r, e₂r, occ, L, κ₁, κ₂, A₁, A₂]
      ring
    have hR_le (b : ContinuousPath ℂ) : ENNReal.ofReal (K⁻¹ * Rb b) ≤
        ENNReal.ofReal K⁻¹ * (ENNReal.ofReal A₁ * W b * ENNReal.ofReal e₁r +
          ENNReal.ofReal (1/2) * ENNReal.ofReal e₁r + ENNReal.ofReal A₂ * occ b *
            ENNReal.ofReal e₂r) := by
      have he₁ : 0 ≤ e₁r := (Real.exp_pos _).le
      have he₂ : 0 ≤ e₂r := (Real.exp_pos _).le
      rw [ENNReal.ofReal_mul hKi.le]
      gcongr
      rw [hRb, ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hA₁,
        ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_mul hA₂]
      gcongr
      · exact ENNReal.ofReal_toReal_le
      · exact ENNReal.ofReal_toReal_le
    calc
      _ = ∫⁻ p, ENNReal.ofReal |J p.1 p.2| ∂(P.prod (planarBrownianMotion y)) := rfl
      _ ≤ ∫⁻ b, ∫⁻ ω, ENNReal.ofReal |J ω b| ∂P ∂(planarBrownianMotion y) := by
        rw [← lintegral_prod_swap]
        exact lintegral_prod_le _
      _ ≤ ∫⁻ b, ENNReal.ofReal (K⁻¹ * Rb b) ∂(planarBrownianMotion y) :=
        lintegral_mono_ae hpath
      _ ≤ ∫⁻ b, ENNReal.ofReal K⁻¹ * (ENNReal.ofReal A₁ * W b * ENNReal.ofReal e₁r +
          ENNReal.ofReal (1/2) * ENNReal.ofReal e₁r + ENNReal.ofReal A₂ * occ b *
            ENNReal.ofReal e₂r) ∂(planarBrownianMotion y) := lintegral_mono hR_le
      _ = ENNReal.ofReal K⁻¹ * (ENNReal.ofReal A₁ * (∫⁻ b, W b ∂(planarBrownianMotion y)) *
            ENNReal.ofReal e₁r + ENNReal.ofReal (1/2) * ENNReal.ofReal e₁r +
          ENNReal.ofReal A₂ * (∫⁻ b, occ b ∂(planarBrownianMotion y)) * ENNReal.ofReal e₂r) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop),
          lintegral_add_left (by fun_prop), lintegral_const, measure_univ, mul_one,
          lintegral_mul_const _ (by fun_prop), lintegral_const_mul _ hWm,
          lintegral_mul_const _ (by fun_prop), lintegral_const_mul _ hoccm]
      _ ≤ _ := by
        gcongr
        · exact hCWle y 0
        · exact hCole y 0
  intro k y μ hμ
  have h := hscale (ε k) (hεpos k) (hεhalf k) y μ hμ
  rw [hεstep k]
  exact h

end HarmonicBalls
