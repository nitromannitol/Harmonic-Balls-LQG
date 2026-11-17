import HarmonicBalls.Proofs.Potential.LQGClockInnerProduct
import HarmonicBalls.Proofs.Potential.LQGClockAnnularAnnealedIncrement

/-! # Fine-scale comparison for nonpositive insertions

Inner occupations for negative insertions are controlled by their zero-insertion counterparts.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- On a ball of radius `δ`, a nonpositive insertion contributes a factor at most
`δ ^ (-γ * α)` at every positive smoothing scale at most `δ`. -/
theorem inner_nonpositive_inserted_clock_le_zero
    (h : ℝ → ℂ → ℝ) (γ α δ ε a b : ℝ) (path : ContinuousPath ℂ)
    (hγ : 0 ≤ γ) (hα : α ≤ 0) (hε : 0 < ε) (hεδ : ε ≤ δ) :
    (∫⁻ s in Ioc a b, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α h ε z)) (path s.toNNReal))) ≤
      ENNReal.ofReal (δ ^ (-γ * α)) *
        (∫⁻ s in Ioc a b, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < δ}.indicator (fun z => ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 h ε z)) (path s.toNNReal))) := by
  have hδ : 0 < δ := lt_of_lt_of_le hε hεδ
  have hcoeff : 0 ≤ -γ * α := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr hγ) hα
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro s
  let z := path s.toNNReal
  change ENNReal.ofReal ({z : ℂ | ‖z‖ < δ}.indicator _ z) ≤
    ENNReal.ofReal (δ ^ (-γ * α)) * ENNReal.ofReal ({z : ℂ | ‖z‖ < δ}.indicator _ z)
  simp only [Set.indicator_apply]
  split_ifs with hz
  · have hm : 0 < max ε ‖z‖ := lt_max_of_lt_left hε
    have hmδ : max ε ‖z‖ ≤ δ := max_le hεδ (le_of_lt hz)
    have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z ε =
        Real.log (max ε ‖z‖) := by
      simpa using (LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 hε)
    have hpow : 0 ≤ ε ^ (γ ^ 2 / 2) := Real.rpow_nonneg hε.le _
    have hfactor : Real.exp ((-γ * α) * Real.log (max ε ‖z‖)) ≤ δ ^ (-γ * α) := by
      rw [Real.rpow_def_of_pos hδ]
      apply Real.exp_le_exp.mpr
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (Real.log_le_log hm hmδ) hcoeff
    have heq : γ * LatticeProb.Gauss.fieldCircleAverage α h ε z =
        γ * LatticeProb.Gauss.fieldCircleAverage 0 h ε z +
          (-γ * α) * Real.log (max ε ‖z‖) := by
      dsimp [LatticeProb.Gauss.fieldCircleAverage]
      rw [hlog]
      ring
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hδ.le _)]
    apply ENNReal.ofReal_le_ofReal
    rw [heq, Real.exp_add]
    have hmultip := mul_le_mul_of_nonneg_left hfactor
      (mul_nonneg hpow (Real.exp_pos (γ * LatticeProb.Gauss.fieldCircleAverage 0 h ε z)).le)
    nlinarith [hmultip]
  · simp

/-- The same comparison holds simultaneously for a countable family of fine scales. -/
theorem iSup_inner_nonpositive_inserted_clock_le_zero
    (h : ℝ → ℂ → ℝ) (γ α δ a b : ℝ) (path : ContinuousPath ℂ)
    (ε : ℕ → ℝ) (hγ : 0 ≤ γ) (hα : α ≤ 0)
    (hε : ∀ n, 0 < ε n) (hεδ : ∀ n, ε n ≤ δ) :
    (⨆ n, ∫⁻ s in Ioc a b, ENNReal.ofReal
      ({z : ℂ | ‖z‖ < δ}.indicator (fun z => (ε n) ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α h (ε n) z)) (path s.toNNReal))) ≤
      ENNReal.ofReal (δ ^ (-γ * α)) *
        (⨆ n, ∫⁻ s in Ioc a b, ENNReal.ofReal
          ({z : ℂ | ‖z‖ < δ}.indicator (fun z => (ε n) ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage 0 h (ε n) z)) (path s.toNNReal))) := by
  apply iSup_le
  intro n
  exact (inner_nonpositive_inserted_clock_le_zero h γ α δ (ε n) a b path hγ hα
    (hε n) (hεδ n)).trans (mul_le_mul_right (le_iSup (fun n =>
      ∫⁻ s in Ioc a b, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < δ}.indicator (fun z => (ε n) ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage 0 h (ε n) z)) (path s.toNNReal))) n) _)

private theorem exp_bound_algebra {u p d a q B C M I A : ℝ}
    (hB : 0 ≤ B)
    (hI : I ≤ C * Real.exp (u*d)) (hA : A ≤ M) :
    Real.exp (u*a) * ((B * Real.exp (-u*p) * I / Real.exp (u*((d-p)/2)) +
      Real.exp (u*((d-p)/2))) / 2 + 2*A*Real.exp (-u*q)) ≤
    (B*C+1)/2 * Real.exp (u*(a+(d-p)/2)) + 2*M*Real.exp (u*(a-q)) := by
  have h : B * Real.exp (-u*p) * I / Real.exp (u*((d-p)/2)) ≤
      B * Real.exp (-u*p) * (C * Real.exp (u*d)) / Real.exp (u*((d-p)/2)) := by
    gcongr
  have ha : 2*A*Real.exp (-u*q) ≤ 2*M*Real.exp (-u*q) := by gcongr
  calc
    _ ≤ Real.exp (u*a) * ((B * Real.exp (-u*p) * (C * Real.exp (u*d)) /
        Real.exp (u*((d-p)/2)) + Real.exp (u*((d-p)/2))) / 2 +
        2*M*Real.exp (-u*q)) := by gcongr
    _ = _ := by
      have h1 : Real.exp (u*a) * Real.exp (-u*p) * Real.exp (u*d) /
          Real.exp (u*((d-p)/2)) = Real.exp (u*(a+(d-p)/2)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub]
        congr 1
        ring
      have h2 : Real.exp (u*a) * Real.exp (u*((d-p)/2)) =
          Real.exp (u*(a+(d-p)/2)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h3 : Real.exp (u*a) * Real.exp (-u*q) = Real.exp (u*(a-q)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      linear_combination (B*C/2)*h1 + (1/2)*h2 + (2*M)*h3

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

private theorem field_increment_le_rate
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε γ θ d C M : ℝ}
    (hε : 0 < ε) (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ}
    (hgm : Measurable g) (hg : Integrable g ν)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ 1)
    (hγθ : γ ≤ θ) (hθ : θ ≤ 2 * γ)
    (hA : (∫ z, |g z| ∂ν) ≤ M)
    (hI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν)) ≤ C * Real.exp (Real.log ε * d)) :
    ∫ ω, |∫ z, g z * ((ε / 2) ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω (ε / 2) z - hcirc ω 1 0)) -
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω ε z - hcirc ω 1 0))) ∂ν| ∂P ≤
      ((Real.exp (γ ^ 2 * Real.log 2) - 1) * C + 1) / 2 *
        Real.exp (Real.log ε * ((d - γ ^ 2 + (2 * γ - θ) ^ 2 / 2) / 2)) +
      2 * M * Real.exp (Real.log ε * ((θ - γ) ^ 2 / 2)) := by
  let p : ℝ := 2 * γ ^ 2 - (2 * γ - θ) ^ 2 / 2
  let q : ℝ := γ ^ 2 / 2 - (θ - γ) ^ 2 / 2
  let u : ℝ := Real.log ε
  have hB : 0 ≤ Real.exp (γ ^ 2 * Real.log 2) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hraw := hh.integral_abs_integral_increment_le hε (R := 1) zero_lt_one ν hgm hg hgR hγθ hθ
    (t := Real.exp (u * ((d - p) / 2))) (Real.exp_pos _)
  have hlog : Real.log (1 / ε) = -u := by simp [u]
  conv at hraw =>
    rhs
    rw [hlog, Real.rpow_def_of_pos hε]
  have halg := exp_bound_algebra (u := u) (p := p) (d := d) (a := γ ^ 2 / 2)
    (q := q) (B := Real.exp (γ ^ 2 * Real.log 2) - 1) hB hI hA
  refine hraw.trans ?_
  convert halg using 1; dsimp [p, q, u]; ring_nf

open ProbabilityTheory MarkovProcess



/-- A single Brownian event controls field increments for every bounded measurable
weight supported in the closed half-ball and every unit-time occupation submeasure. -/
theorem ae_brownian_field_submeasure_weighted_increment_le_riesz_energy
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ)
    :
    ∃ θ d : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x),
        ∀ (g : ℂ → ℝ), Measurable g → ∀ M : ℝ, 0 ≤ M →
        (∀ z, |g z| ≤ M) → (∀ z, g z ≠ 0 → ‖z‖ ≤ 1 / 2) →
        ∀ μ : Measure ℂ, μ ≤ Measure.map (fun t => b t) ν →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
        (∫ ω, |∫ z, g z * ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*(M^2 * unitOccupationRieszEnergy d b * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, _⟩ := exists_clock_truncation_exponents hγ0 hγ2
  refine ⟨θ, d, hγθ, hθ, hd0, hd2, hp, ?_⟩
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [planarBrownianMotion_ae_unit_weighted_occupation_le_riesz_energy x hd0 hd2] with b hb
  intro g hg M hM hgM hgs μ hμ ε hε hεhalf
  let ρ : Measure ℂ := Measure.map (fun t => b t) ν
  let : IsProbabilityMeasure ρ := inferInstance
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le ρ hμ
  have hgρ : Integrable g ρ := by
    refine (integrable_const M).mono' hg.aestronglyMeasurable ?_
    filter_upwards with z
    simpa [Real.norm_eq_abs] using hgM z
  have hgi : Integrable g μ := hgρ.mono_measure hμ
  have hA : (∫ z, |g z| ∂μ) ≤ M := by
    calc
      _ ≤ ∫ z, |g z| ∂ρ := integral_mono_measure hμ (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) hgρ.abs
      _ ≤ ∫ _ : ℂ, M ∂ρ := integral_mono hgρ.abs (integrable_const M) (fun z => hgM z)
      _ = M := by simp
  have hpair0 := hb g hg M hM hgM (2*ε) (by positivity)
  have hpair : (∫ p : ℂ × ℂ, if ‖p.1-p.2‖ < 2*ε then |g p.1| * |g p.2| else 0
      ∂(μ.prod μ)) ≤ M^2*(unitOccupationRieszEnergy d b*(2*ε)^d) := by
    apply (integral_mono_measure (Measure.prod_mono hμ hμ) ?_ hpair0.1).trans hpair0.2.2
    filter_upwards with p
    split_ifs <;> positivity
  have hI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤
      (M^2*unitOccupationRieszEnergy d b*2^d)*Real.exp (Real.log ε*d) := by
    have hI' : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤ M^2*(unitOccupationRieszEnergy d b*(2*ε)^d) := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hpair
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le,
      Real.rpow_def_of_pos hε] at hI'
    convert hI' using 1; ring
  exact field_increment_le_rate hh hε μ hg hgi (fun z hz => by linarith [hgs z hz])
    hγθ.le hθ.le hA hI


/-- The field increment estimate holds on one Brownian event for every inner ball
of radius at most one half and every unit-time occupation submeasure. -/
theorem ae_brownian_inner_ball_increment_le_riesz_energy
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ) :
    ∃ θ d : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x),
        ∀ δ : ℝ, δ ≤ 1/2 → ∀ μ : Measure ℂ,
        μ ≤ Measure.map (fun t => b t) ν →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
        (∫ ω, |∫ z, ({z : ℂ | ‖z‖ < δ}.indicator (fun _ => (1 : ℝ)) z) *
          ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*(unitOccupationRieszEnergy d b * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, hbound⟩ :=
    ae_brownian_field_submeasure_weighted_increment_le_riesz_energy hh hγ0 hγ2 x
  refine ⟨θ, d, hγθ, hθ, hd0, hd2, hp, ?_⟩
  filter_upwards [hbound] with b hb
  intro δ hδ μ hμ ε hε hεhalf
  let g : ℂ → ℝ := {z : ℂ | ‖z‖ < δ}.indicator (fun _ => 1)
  have hg : Measurable g := measurable_const.indicator (measurableSet_lt measurable_norm measurable_const)
  have hgM : ∀ z, |g z| ≤ 1 := by
    intro z
    simp only [g, Set.indicator_apply]
    split_ifs <;> norm_num
  have hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ 1 / 2 := by
    intro z hz
    have hz' : ‖z‖ < δ := by
      by_contra h
      have hmem : z ∉ {z : ℂ | ‖z‖ < δ} := h
      exact hz (by simpa only [g] using Set.indicator_of_notMem hmem (fun _ : ℂ => (1 : ℝ)))
    exact (le_of_lt hz').trans hδ
  simpa only [one_pow, one_mul, mul_one] using
    (hb g hg 1 (by norm_num) hgM hgs μ hμ ε hε hεhalf)

end HarmonicBalls
