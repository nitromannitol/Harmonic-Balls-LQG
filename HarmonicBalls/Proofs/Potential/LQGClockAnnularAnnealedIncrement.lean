import HarmonicBalls.Proofs.Potential.BrownianOccupationWeightedMeasure
import HarmonicBalls.Proofs.Potential.LQGClockLocalizedIncrementBounds

/-! # Brownian energy for annular clock increments

The unit-time Riesz energy is a measurable, integrable Brownian-path envelope.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- The unit-time inverse-power energy of a continuous path. -/
noncomputable def unitOccupationRieszEnergy (β : ℝ) (b : ContinuousPath ℂ) : ℝ :=
  (∫⁻ p : ℝ≥0 × ℝ≥0,
    (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β) ∂((Measure.map Real.toNNReal
      (volume.restrict (Icc (0 : ℝ) 1))).prod (Measure.map Real.toNNReal
      (volume.restrict (Icc (0 : ℝ) 1))))).toReal

/-- The energy is measurable as a function of the path. -/
theorem measurable_unitOccupationRieszEnergy (β : ℝ) :
    Measurable (unitOccupationRieszEnergy β) := by
  have hf : Measurable (fun q : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) =>
      (ENNReal.ofReal ‖q.1 q.2.1 - q.1 q.2.2‖) ^ (-β)) := by fun_prop
  exact (Measurable.lintegral_prod_right hf).ennreal_toReal

/-- The unit-time energy has finite Brownian expectation for subcritical orders. -/
theorem integrable_unitOccupationRieszEnergy (x : ℂ) {β : ℝ}
    (hβ0 : 0 < β) (hβ2 : β < 2) :
    Integrable (unitOccupationRieszEnergy β) (planarBrownianMotion x) := by
  apply integrable_toReal_of_lintegral_ne_top
  · have hf : Measurable (fun q : ContinuousPath ℂ × (ℝ≥0 × ℝ≥0) =>
        (ENNReal.ofReal ‖q.1 q.2.1 - q.1 q.2.2‖) ^ (-β)) := by fun_prop
    exact (Measurable.lintegral_prod_right hf).aemeasurable
  · exact (planarBrownianMotion_unit_occupation_riesz_energy_lt_top x hβ0 hβ2).ne

/-- Finite path energy controls every near-diagonal occupation count. -/
theorem planarBrownianMotion_ae_unit_pair_le_riesz_energy (x : ℂ) {β : ℝ}
    (hβ0 : 0 < β) (hβ2 : β < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ r : ℝ, 0 < r →
      (∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)) ≤
          ENNReal.ofReal (unitOccupationRieszEnergy β b * r ^ β) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  filter_upwards [planarBrownianMotion_ae_unit_occupation_riesz_energy_lt_top x hβ0 hβ2] with b hb
  let E := ∫⁻ p : ℝ≥0 × ℝ≥0, (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β) ∂(ν.prod ν)
  have hE : E < ∞ := hb
  change ∀ r : ℝ, 0 < r → _ ≤ ENNReal.ofReal (E.toReal * r ^ β)
  intro r hr
  have hrpow : 0 < r ^ β := Real.rpow_pos_of_pos hr _
  have hR0 : ENNReal.ofReal (r ^ β) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hrpow)
  have hRtop : ENNReal.ofReal (r ^ β) ≠ ∞ := ENNReal.ofReal_ne_top
  calc
    (∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)) ≤
        ∫⁻ p : ℝ≥0 × ℝ≥0, ENNReal.ofReal (r ^ β) *
          (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ (-β) ∂(ν.prod ν) := by
      apply lintegral_mono
      intro p
      dsimp only
      split_ifs with hp
      · have hpow : (ENNReal.ofReal ‖b p.1 - b p.2‖) ^ β ≤ ENNReal.ofReal (r ^ β) := by
          rw [← ENNReal.ofReal_rpow_of_nonneg (le_of_lt hr) (le_of_lt hβ0)]
          exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (le_of_lt hp)) (le_of_lt hβ0)
        rw [ENNReal.rpow_neg]
        calc
          1 = ENNReal.ofReal (r ^ β) * (ENNReal.ofReal (r ^ β))⁻¹ :=
            (ENNReal.mul_inv_cancel hR0 hRtop).symm
          _ ≤ ENNReal.ofReal (r ^ β) * ((ENNReal.ofReal ‖b p.1 - b p.2‖) ^ β)⁻¹ :=
            by gcongr
      · exact bot_le
    _ = ENNReal.ofReal (r ^ β) * E := by rw [lintegral_const_mul' _ _ hRtop]
    _ ≤ ENNReal.ofReal (E.toReal * r ^ β) := by
      rw [ENNReal.ofReal_mul (by positivity)]
      have hE' : E ≤ ENNReal.ofReal E.toReal := by
        rw [ENNReal.ofReal_toReal hE.ne]
      calc
        ENNReal.ofReal (r ^ β) * E ≤ ENNReal.ofReal (r ^ β) * ENNReal.ofReal E.toReal := by gcongr
        _ = ENNReal.ofReal E.toReal * ENNReal.ofReal (r ^ β) := mul_comm _ _



/-- Almost every Brownian path has a simultaneous near-diagonal pair bound for every
bounded measurable nonnegative spatial weight. -/
theorem planarBrownianMotion_ae_unit_weighted_pair_le_riesz_energy (x : ℂ) {β : ℝ}
    (hβ0 : 0 < β) (hβ2 : β < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ (g : ℂ → ℝ≥0∞), Measurable g → ∀ M : ℝ≥0∞, M < ∞ →
      (∀ z, g z ≤ M) → ∀ r : ℝ, 0 < r →
        (∫⁻ p : ℝ≥0 × ℝ≥0,
          (if ‖b p.1 - b p.2‖ < r then g (b p.1) * g (b p.2) else 0)
            ∂(ν.prod ν)) ≤ M ^ 2 * ENNReal.ofReal (unitOccupationRieszEnergy β b * r ^ β) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  filter_upwards [planarBrownianMotion_ae_unit_pair_le_riesz_energy x hβ0 hβ2] with b hb
  intro g _hg M hM hg r hr
  calc
    (∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then g (b p.1) * g (b p.2) else 0)
          ∂(ν.prod ν)) ≤
        ∫⁻ p : ℝ≥0 × ℝ≥0, M ^ 2 *
          (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν) := by
      apply lintegral_mono
      intro p
      dsimp only
      split_ifs with hp
      · simpa [pow_two] using (mul_le_mul' (hg (b p.1)) (hg (b p.2)))
      · simp
    _ = M ^ 2 * (∫⁻ p : ℝ≥0 × ℝ≥0,
        (if ‖b p.1 - b p.2‖ < r then 1 else 0 : ℝ≥0∞) ∂(ν.prod ν)) := by
      rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hM.ne)]
    _ ≤ M ^ 2 * ENNReal.ofReal (unitOccupationRieszEnergy β b * r ^ β) := by gcongr; exact hb r hr


/-- The weighted spatial pair integral is bounded simultaneously for all bounded weights. -/
theorem planarBrownianMotion_ae_unit_weighted_occupation_le_riesz_energy (x : ℂ) {β : ℝ}
    (hβ0 : 0 < β) (hβ2 : β < 2) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ (g : ℂ → ℝ), Measurable g → ∀ M : ℝ, 0 ≤ M →
      (∀ z, |g z| ≤ M) → ∀ r : ℝ, 0 < r →
        let μ := Measure.map (fun t => b t) ν
        Integrable (fun p : ℂ × ℂ =>
          if ‖p.1 - p.2‖ < r then |g p.1| * |g p.2| else 0) (μ.prod μ) ∧
        (∫ p : ℂ × ℂ, if ‖p.1 - p.2‖ < r then |g p.1| * |g p.2| else 0
          ∂(μ.prod μ)) = (∫ p : ℝ≥0 × ℝ≥0,
            if ‖b p.1 - b p.2‖ < r then |g (b p.1)| * |g (b p.2)| else 0
              ∂(ν.prod ν)) ∧
        (∫ p : ℂ × ℂ, if ‖p.1 - p.2‖ < r then |g p.1| * |g p.2| else 0
          ∂(μ.prod μ)) ≤ M ^ 2 * (unitOccupationRieszEnergy β b * r ^ β) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [planarBrownianMotion_ae_unit_weighted_pair_le_riesz_energy x hβ0 hβ2] with b hb
  intro g hg M hM hgM r hr
  let μ : Measure ℂ := Measure.map (fun t => b t) ν
  have hbm : Measurable b := b.continuous.measurable
  let : IsProbabilityMeasure μ := inferInstance
  let f : ℂ × ℂ → ℝ := fun p =>
    if ‖p.1 - p.2‖ < r then |g p.1| * |g p.2| else 0
  have hs : MeasurableSet {p : ℂ × ℂ | ‖p.1 - p.2‖ < r} :=
    measurableSet_lt ((measurable_fst.sub measurable_snd).norm) measurable_const
  have hf : Measurable f := by
    exact ((hg.comp measurable_fst).abs.mul (hg.comp measurable_snd).abs).ite hs measurable_const
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    dsimp [f]
    split_ifs <;> positivity
  have hfbound : ∀ p, f p ≤ M ^ 2 := by
    intro p
    dsimp [f]
    split_ifs
    · calc
        |g p.1| * |g p.2| ≤ M * M := mul_le_mul (hgM _) (hgM _) (abs_nonneg _) hM
        _ = M ^ 2 := by ring
    · positivity
  have hfi : Integrable f (μ.prod μ) := by
    refine (integrable_const (M ^ 2)).mono' hf.aestronglyMeasurable ?_
    filter_upwards with p
    simpa [Real.norm_eq_abs, abs_of_nonneg (hf0 p)] using hfbound p
  have hmap : μ.prod μ = Measure.map (Prod.map b b) (ν.prod ν) :=
    Measure.map_prod_map ν ν hbm hbm
  refine ⟨hfi, ?_, ?_⟩
  · rw [hmap, integral_map (hbm.prodMap hbm).aemeasurable hf.aestronglyMeasurable]
    rfl
  have hle := hb (fun z => ENNReal.ofReal |g z|) hg.abs.ennreal_ofReal
    (ENNReal.ofReal M) ENNReal.ofReal_lt_top (fun z => ENNReal.ofReal_le_ofReal (hgM z)) r hr
  have hlin : (∫⁻ p, ENNReal.ofReal (f p) ∂(μ.prod μ)) ≤
      ENNReal.ofReal (M ^ 2 * (unitOccupationRieszEnergy β b * r ^ β)) := by
    rw [hmap, lintegral_map hf.ennreal_ofReal (hbm.prodMap hbm)]
    convert hle using 1
    · apply lintegral_congr
      intro p
      dsimp [f]
      split_ifs <;> simp [ENNReal.ofReal_mul]
    · rw [pow_two, ENNReal.ofReal_mul (mul_nonneg hM hM), ENNReal.ofReal_mul hM, pow_two]
  have henergy0 : 0 ≤ unitOccupationRieszEnergy β b := ENNReal.toReal_nonneg
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
  rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0),
    ENNReal.toReal_ofReal (integral_nonneg hf0), ENNReal.toReal_ofReal (by positivity)] at this
  exact this



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



private theorem brownian_field_submeasure_riesz_increment_rate
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ)
    {g : ℂ → ℝ} (hg : Measurable g) {M : ℝ} (hM : 0 ≤ M)
    (hgM : ∀ z, |g z| ≤ M) (hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ 1 / 2) :
    ∃ θ d : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x),
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
  intro μ hμ ε hε hεhalf
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

private theorem annular_weight_bound {δ γ α : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : ℂ,
      |({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => Real.exp (-γ*α*Real.log (max δ ‖z‖))) z)| ≤ M := by
  let f : ℂ → ℝ := fun z => Real.exp (-γ*α*Real.log (max δ ‖z‖))
  have hf : Continuous f := by
    exact Real.continuous_exp.comp (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hδ).ne')))
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.continuousOn
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  intro z
  by_cases hz : z ∈ {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  · have hzk : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
    have hle : f z ≤ K := hK ⟨z, hzk, rfl⟩
    rw [Set.indicator_of_mem hz, abs_of_pos (Real.exp_pos _)]
    exact hle.trans (le_max_left K 0)
  · rw [Set.indicator_of_notMem hz, abs_zero]
    exact le_max_right K 0



/-- Brownian occupation increments of the inserted field on an annulus obey a
geometric field-expectation bound uniformly over all stopping horizons up to time one. -/
theorem ae_brownian_stopped_annular_inserted_increment_le_riesz_energy
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x),
        ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        let μ := Measure.map (fun t => b t) (ν.restrict (Iic T))
        (∫ ω, |∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*(M^2 * unitOccupationRieszEnergy d b * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let g : ℂ → ℝ := A.indicator (fun z => Real.exp (-γ*α*Real.log (max δ ‖z‖)))
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hgm : Measurable g := by
    apply Measurable.indicator _ hA
    exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hδ).ne')))).measurable
  obtain ⟨M, hM, hgM⟩ := annular_weight_bound (γ := γ) (α := α) hδ
  have hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ 1/2 := by
    intro z hz
    by_contra h
    have hn : z ∉ A := fun hzA => h hzA.2
    exact hz (Set.indicator_of_notMem hn _)
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, hb⟩ :=
    brownian_field_submeasure_riesz_increment_rate hh hγ0 hγ2 x hgm hM hgM hgs
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  filter_upwards [hb] with b hb
  intro T ε hε hεhalf hεδ
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ := Measure.map (fun t => b t) (ν.restrict (Iic T))
  have hμ : μ ≤ Measure.map (fun t => b t) ν :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  have hbound := hb μ hμ ε hε hεhalf
  refine (le_of_eq ?_).trans hbound
  congr 1
  funext ω
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ A
  · have hδε : ε ≤ ‖z‖ := hεδ.trans hz.1
    have hhalf : ε/2 ≤ ‖z‖ := by linarith
    rw [show A.indicator _ z = _ from Set.indicator_of_mem hz _,
      show g z = _ from Set.indicator_of_mem hz _, max_eq_right hz.1,
      max_eq_right hδε, max_eq_right hhalf]
    have heq (r : ℝ) : γ * (hcirc ω r z - hcirc ω 1 0 - α * Real.log ‖z‖) =
        -γ*α*Real.log ‖z‖ + γ*(hcirc ω r z-hcirc ω 1 0) := by ring
    rw [heq (ε/2), heq ε, Real.exp_add, Real.exp_add]
    ring
  · rw [show A.indicator _ z = _ from Set.indicator_of_notMem hz _,
      show g z = _ from Set.indicator_of_notMem hz _, zero_mul]


/-- A measurable spatial field integrated along a measurable stopped path is jointly measurable. -/
theorem measurable_stopped_path_integral {Ω : Type*} [MeasurableSpace Ω]
    (F : Ω × ℂ → ℝ) (hF : Measurable F)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun q : ContinuousPath ℂ × Ω =>
      ∫ z, F (q.2, z) ∂(Measure.map (fun t => q.1 t)
        ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ q.1))))) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let G : (ContinuousPath ℂ × Ω) × ℝ≥0 → ℝ := fun q =>
    if q.2 ≤ τ q.1.1 then F (q.1.2, q.1.1 q.2) else 0
  have heval0 : Measurable (fun q : ContinuousPath ℂ × ℝ≥0 => q.1 q.2) := by fun_prop
  have heval : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ≥0 => q.1.1 q.2) :=
    heval0.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hset : MeasurableSet {q : (ContinuousPath ℂ × Ω) × ℝ≥0 | q.2 ≤ τ q.1.1} :=
    measurableSet_le measurable_snd (hτ.comp (measurable_fst.comp measurable_fst))
  have hG : Measurable G := by
    exact (hF.comp ((measurable_snd.comp measurable_fst).prodMk heval)).ite hset measurable_const
  have hmeas : Measurable (fun q : ContinuousPath ℂ × Ω => ∫ t, G (q, t) ∂ν) :=
    hG.stronglyMeasurable.integral_prod_right'.measurable
  convert hmeas using 1
  funext q
  rw [integral_map (f := fun z : ℂ => F (q.2, z)) q.1.continuous.measurable.aemeasurable
    (hF.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
  rw [← integral_indicator measurableSet_Iic]
  apply integral_congr_ae
  filter_upwards with t
  simp [G, Set.indicator_apply]

/-- A jointly measurable version gives a measurable field expectation for each stopped path. -/
theorem measurable_stopped_path_field_expectation {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P] (F : Ω × ℂ → ℝ) (hF : Measurable F)
    (F₀ : Ω → ℂ → ℝ) (hF₀ : ∀ᵐ ω ∂P, ∀ z, F (ω, z) = F₀ ω z)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun b : ContinuousPath ℂ => ∫ ω, |∫ z, F₀ ω z ∂(Measure.map (fun t => b t)
      ((Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ b))))| ∂P) := by
  have h := ((measurable_stopped_path_integral F hF τ hτ).abs.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  convert h using 1
  funext b
  apply integral_congr_ae
  filter_upwards [hF₀] with ω hω
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  exact (hω z).symm

/-- The field expectation of a stopped inserted-field annular increment is measurable in the path. -/
theorem measurable_stopped_annular_inserted_field_expectation
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α δ : ℝ) (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun b : ContinuousPath ℂ => ∫ ω, |∫ z,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z
      ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ b))))| ∂P) := by
  have := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let F : Ω × ℂ → ℝ := fun q => A.indicator (fun z =>
    (ε/2)^(γ^2/2) * Real.exp (γ*(H q.1 (ε/2) z-H q.1 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(H q.1 ε z-H q.1 1 0 - α*Real.log (max ε ‖z‖)))) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 (ε/2) q.2) :=
    (hHm (ε/2) (half_pos hε)).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) :=
    (hHm ε hε).comp measurable_swap
  have h3 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hF : Measurable F := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).sub
      (measurable_const.mul (measurable_const.mul ((h2.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp)
  apply measurable_stopped_path_field_expectation P F hF _ _ τ hτ
  filter_upwards [hHae] with ω hω z
  simp [F, A, hω]

/-- The field-averaged absolute annular increment along a stopped path. -/
noncomputable def stoppedAnnularIncrement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (hcirc : Ω → ℝ → ℂ → ℝ) (γ α δ ε : ℝ)
    (τ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) : ℝ :=
  ∫ ω, |∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
    (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z
    ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
      (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ b))))| ∂P

/-- The annealed annular increment has an explicit geometric-rate bound. -/
theorem brownian_stopped_annular_inserted_increment_annealed_le
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        Integrable (stoppedAnnularIncrement P hcirc γ α δ ε τ) (planarBrownianMotion x) ∧
        (∫ b, stoppedAnnularIncrement P hcirc γ α δ ε τ b ∂(planarBrownianMotion x)) ≤
          ((Real.exp (γ^2*Real.log 2)-1) *
            (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂(planarBrownianMotion x)) * 2^d)+1)/2 *
              Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
          2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    ae_brownian_stopped_annular_inserted_increment_le_riesz_energy hh hγ0 hγ2 α x hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro ε hε hεhalf hεδ
  let E : ContinuousPath ℂ → ℝ := unitOccupationRieszEnergy d
  let a : ℝ := Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2))
  let c : ℝ := Real.exp (Real.log ε * ((θ-γ)^2/2))
  let B : ℝ := Real.exp (γ^2*Real.log 2)-1
  let G : ContinuousPath ℂ → ℝ := fun b => ((B*(M^2 * E b * 2^d)+1)/2)*a + 2*M*c
  have hE : Integrable E (planarBrownianMotion x) := integrable_unitOccupationRieszEnergy x hd0 hd2
  have hG : Integrable G (planarBrownianMotion x) := by
    dsimp [G]
    fun_prop
  have hm : Measurable (stoppedAnnularIncrement P hcirc γ α δ ε τ) :=
    measurable_stopped_annular_inserted_field_expectation hh hε γ α δ τ hτ
  have hle : ∀ᵐ b ∂(planarBrownianMotion x), stoppedAnnularIncrement P hcirc γ α δ ε τ b ≤ G b := by
    filter_upwards [hb] with b hb
    exact hb (τ b) ε hε hεhalf hεδ
  have hnonneg : ∀ b, 0 ≤ stoppedAnnularIncrement P hcirc γ α δ ε τ b := by
    intro b
    apply integral_nonneg
    intro ω
    exact abs_nonneg _
  have hi : Integrable (stoppedAnnularIncrement P hcirc γ α δ ε τ) (planarBrownianMotion x) := by
    apply hG.mono' hm.aestronglyMeasurable
    filter_upwards [hle] with b hb
    simpa [Real.norm_eq_abs, abs_of_nonneg (hnonneg b)] using hb
  refine ⟨hi, (integral_mono_ae hi hG hle).trans ?_⟩
  change (∫ b, G b ∂(planarBrownianMotion x)) ≤
    ((B*(M^2 * (∫ b, E b ∂(planarBrownianMotion x)) * 2^d)+1)/2)*a + 2*M*c
  have hGeq : G = fun b => (B*M^2*2^d*a/2)*E b + (a/2 + 2*M*c) := by
    funext b
    dsimp [G]
    ring
  rw [hGeq, integral_add (hE.const_mul _) (integrable_const _), integral_const_mul]
  simp only [integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
  ring_nf
  exact le_rfl

/-- The recentered logarithmic expression is the actual inserted circle average. -/
theorem ae_recentered_inserted_circle_average
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (α : ℝ) :
    ∀ᵐ ω ∂P, ∀ (r : ℝ) (z : ℂ), 0 < r →
      hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) =
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z := by
  filter_upwards [hh.ae_circleAverage_one_zero] with ω hω r z hr
  have hlog : Real.circleAverage (fun y : ℂ => Real.log ‖y‖) z r =
      Real.log (max r ‖z‖) := by
    simpa using (LatticeProb.Gauss.circleAverage_log_norm_sub_eq z 0 hr)
  simp [LatticeProb.Gauss.fieldCircleAverage, hlog, hω]

/-- The annular increment is computed from the inserted field's circle averages. -/
theorem stoppedAnnularIncrement_eq_inserted_field
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε : ℝ} (hε : 0 < ε)
    (γ α δ : ℝ) (τ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) :
    stoppedAnnularIncrement P hcirc γ α δ ε τ b =
    ∫ ω, |∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
      (ε/2)^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (ε/2) z) -
      ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z
      ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ b))))| ∂P := by
  unfold stoppedAnnularIncrement
  apply integral_congr_ae
  filter_upwards [ae_recentered_inserted_circle_average hh α] with ω hω
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  simp only [Set.indicator_apply]
  split_ifs
  · rw [hω (ε/2) z (half_pos hε), hω ε z hε]
  · rfl

end HarmonicBalls
