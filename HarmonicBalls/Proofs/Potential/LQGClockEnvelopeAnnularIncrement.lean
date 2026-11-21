import HarmonicBalls.Proofs.Potential.LQGClockInsertedAnnealedIncrement
import HarmonicBalls.Proofs.Potential.LQGClockInsertedOccupationIncrement
import HarmonicBalls.Proofs.Potential.LQGClockUniformInnerExpectation

/-! # Annular clock increments under an integrable pair envelope

Suppose that the singularly weighted near-diagonal pair occupation of a planar Brownian path
at every radius `0 < r ≤ 1` is at most `H b * r ^ β`, where `H` is integrable and
`γ ^ 2 / 2 < β`. Then the truncated second-moment estimate for circle-average increments
applies along almost every path with the pair constant `2 ^ β * H b`, and the expected
inserted annular and cutoff clock increments at dyadic scales admit summable bounds that are
uniform in the outer cutoff, for every `0 < γ * α < 2`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
open scoped NNReal ENNReal

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- Above the threshold `γ ^ 2 / 2`, a pair exponent `β` admits a moment exponent `θ`
strictly between `γ` and `2 * γ` with a positive annular decay rate. -/
theorem exists_annular_moment_exponent {γ β : ℝ} (hγ : 0 < γ) (hβ : γ ^ 2 / 2 < β) :
    ∃ θ : ℝ, γ < θ ∧ θ < 2 * γ ∧ 0 < β - γ ^ 2 + (2 * γ - θ) ^ 2 / 2 := by
  have hκ : 0 < β - γ ^ 2 / 2 := by linarith
  obtain ⟨t, ht0, ht1, ht2⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ γ / 2 ∧ t * (2 * γ) ≤ β - γ ^ 2 / 2 :=
    ⟨min (γ / 2) ((β - γ ^ 2 / 2) / (2 * γ)), lt_min (by linarith) (div_pos hκ (by linarith)),
      min_le_left _ _, (le_div_iff₀ (by linarith)).1 (min_le_right _ _)⟩
  refine ⟨γ + t, by linarith, by linarith, ?_⟩
  nlinarith [sq_nonneg t]

/-- An extended-real pair envelope with finite expectation yields a real integrable
envelope with the same pair bound. -/
theorem integrable_toReal_pair_envelope_of_lintegral (x z : ℂ) {q β : ℝ}
    (W : ContinuousPath ℂ → ℝ≥0∞) (hWm : AEMeasurable W (planarBrownianMotion x))
    (hWi : (∫⁻ b, W b ∂(planarBrownianMotion x)) ≠ ∞)
    (hW : ∀ᵐ b ∂(planarBrownianMotion x), ∀ r : ℝ, 0 < r → r ≤ 1 →
      unitSingularPairNear z q r b ≤ W b * ENNReal.ofReal (r ^ β)) :
    Integrable (fun b => (W b).toReal) (planarBrownianMotion x) ∧
      ∀ᵐ b ∂(planarBrownianMotion x), 0 ≤ (W b).toReal ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
        unitSingularPairNear z q r b ≤ ENNReal.ofReal ((W b).toReal * r ^ β) := by
  refine ⟨integrable_toReal_of_lintegral_ne_top hWm hWi, ?_⟩
  filter_upwards [ae_lt_top' hWm hWi, hW] with b hb hbW
  refine ⟨ENNReal.toReal_nonneg, fun r hr hr1 => ?_⟩
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hb.ne]
  exact hbW r hr hr1

/-- A bound on the singular pair occupation of one path at radius `r` bounds the
near-diagonal pair integral of every singularly dominated weight against every submeasure
of the occupation measure of that path. -/
theorem singular_weighted_submeasure_pair_le_of_near_le (z : ℂ) {q r A : ℝ}
    (b : ContinuousPath ℂ) (hA : 0 ≤ A)
    (hb : unitSingularPairNear z q r b ≤ ENNReal.ofReal A)
    (g : ℂ → ℝ) (hg : Measurable g)
    (hgq : ∀ y, ENNReal.ofReal |g y| ≤ (ENNReal.ofReal ‖y-z‖) ^ (-q))
    (μ : Measure ℂ) (hμ : μ ≤ Measure.map (fun t => b t)
      (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1)))) :
    Integrable (fun p : ℂ × ℂ =>
        if ‖p.1-p.2‖ < r then |g p.1| * |g p.2| else 0) (μ.prod μ) ∧
      (∫ p : ℂ × ℂ, if ‖p.1-p.2‖ < r then |g p.1| * |g p.2| else 0 ∂(μ.prod μ)) ≤ A := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  let ρ : Measure ℂ := Measure.map (fun t => b t) ν
  let : IsProbabilityMeasure ρ := inferInstance
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le ρ hμ
  have hbm : Measurable b := b.continuous.measurable
  let f : ℂ × ℂ → ℝ := fun p =>
    if ‖p.1-p.2‖ < r then |g p.1| * |g p.2| else 0
  have hs : MeasurableSet {p : ℂ × ℂ | ‖p.1-p.2‖ < r} :=
    measurableSet_lt ((measurable_fst.sub measurable_snd).norm) measurable_const
  have hf : Measurable f :=
    ((hg.comp measurable_fst).abs.mul (hg.comp measurable_snd).abs).ite hs measurable_const
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    dsimp [f]
    split_ifs <;> positivity
  have hmap : ρ.prod ρ = Measure.map (Prod.map b b) (ν.prod ν) :=
    Measure.map_prod_map ν ν hbm hbm
  have hlin : (∫⁻ p, ENNReal.ofReal (f p) ∂(ρ.prod ρ)) ≤ ENNReal.ofReal A := by
    rw [hmap, lintegral_map hf.ennreal_ofReal (hbm.prodMap hbm)]
    calc
      _ ≤ unitSingularPairNear z q r b := by
        unfold unitSingularPairNear
        apply lintegral_mono
        intro p
        dsimp [f]
        split_ifs
        · rw [ENNReal.ofReal_mul (abs_nonneg _)]
          exact mul_le_mul' (hgq _) (hgq _)
        · simp
      _ ≤ ENNReal.ofReal A := hb
  have hfi : Integrable f (ρ.prod ρ) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have heq : (∫⁻ p, ‖f p‖ₑ ∂(ρ.prod ρ)) =
        (∫⁻ p, ENNReal.ofReal (f p) ∂(ρ.prod ρ)) := by
      apply lintegral_congr
      intro p
      rw [Real.enorm_of_nonneg (hf0 p)]
    rw [heq]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have hρ : (∫ p, f p ∂(ρ.prod ρ)) ≤ A := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0),
      ENNReal.toReal_ofReal (integral_nonneg hf0), ENNReal.toReal_ofReal hA] at h
    exact h
  refine ⟨hfi.mono_measure (Measure.prod_mono hμ hμ), ?_⟩
  refine (integral_mono_measure (Measure.prod_mono hμ hμ) ?_ hfi).trans hρ
  filter_upwards with p
  exact hf0 p

/-- Under an integrable pair envelope with exponent `β`, the truncated second-moment
field-increment estimate holds along almost every Brownian path for all singularly
dominated weights and all submeasures of the occupation measure. -/
theorem ae_brownian_singular_submeasure_field_increment_le_of_envelope
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x z : ℂ)
    {q β : ℝ} (hq : 0 < q) (hq₂ : q < 2) (H : ContinuousPath ℂ → ℝ)
    (hH : ∀ᵐ b ∂(planarBrownianMotion x), 0 ≤ H b ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      unitSingularPairNear z q r b ≤ ENNReal.ofReal (H b * r ^ β)) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ (g : ℂ → ℝ), Measurable g →
      (∀ y, ENNReal.ofReal |g y| ≤ (ENNReal.ofReal ‖y-z‖) ^ (-q)) →
      ∀ (μ : Measure ℂ), μ ≤ Measure.map (fun t => b t) ν →
      ∀ {R γ θ : ℝ}, 0 < R → γ ≤ θ → θ ≤ 2*γ →
      (∀ y, g y ≠ 0 → ‖y‖ ≤ R - 1/2) →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
      (∫ ω, |∫ y, g y * ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) y-hcirc ω R 0)) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε y-hcirc ω R 0))) ∂μ| ∂P) ≤
      ((Real.exp (γ^2*Real.log 2)-1)*
        Real.exp (Real.log R * (2*γ^2-(2*γ-θ)^2/2))*
        (2^β * H b)+1)/2 *
        Real.exp (Real.log ε * ((β-γ^2+(2*γ-θ)^2/2)/2)) +
      2*unitSingularOccupationEnvelope z q b *
        Real.exp (Real.log R * (γ^2/2-(θ-γ)^2/2))*
        Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [planarBrownianMotion_ae_unit_singular_weighted_submeasure_integrable
      x z hq hq₂, hH] with b hfirst hpair
  intro g hg hgq μ hμ R γ θ hR hγθ hθ hgs ε hε hεhalf
  let ρ : Measure ℂ := Measure.map (fun t => b t) ν
  let : IsProbabilityMeasure ρ := inferInstance
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le ρ hμ
  obtain ⟨hgi, hA⟩ := hfirst g hg hgq μ hμ
  have h2ε : 0 < 2*ε := by positivity
  have hr1 : 2*ε ≤ 1 := by linarith
  have hHr : 0 ≤ H b * (2*ε)^β := mul_nonneg hpair.1 (Real.rpow_nonneg h2ε.le _)
  obtain ⟨_, hI⟩ := singular_weighted_submeasure_pair_le_of_near_le z b hHr
    (hpair.2 (2*ε) h2ε hr1) g hg hgq μ hμ
  have hI' : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤
      (2^β * H b) * Real.exp (Real.log ε*β) := by
    have hhI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
        (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤ H b * (2*ε)^β := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hI
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le,
      Real.rpow_def_of_pos hε] at hhI
    convert hhI using 1; ring
  exact field_increment_le_rate_of_radius hh hε hR μ hg hgi
    (fun y hy => by linarith [hgs y hy]) hγθ hθ hA hI'

/-- Under an integrable pair envelope, moving annular inserted increments have a common
pathwise bound in terms of the envelope and the singular occupation. -/
theorem ae_inserted_moving_annulus_increment_le_of_envelope
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ α β θ : ℝ} (hq : 0 < γ*α) (hq₂ : γ*α < 2) (hγθ : γ ≤ θ) (hθ : θ ≤ 2*γ)
    (H : ContinuousPath ℂ → ℝ)
    (hH : ∀ᵐ b ∂(planarBrownianMotion x), 0 ≤ H b ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      unitSingularPairNear 0 (γ*α) r b ≤ ENNReal.ofReal (H b * r ^ β)) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ δ ε : ℝ, 0 < ε → ε ≤ 1/2 →
      let μ := Measure.map (fun t => b t) ν
      (∫ ω, |∫ w, {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) w-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε w-hcirc ω 1 0 - α*Real.log (max ε ‖w‖)))) w ∂μ| ∂P) ≤
      ((Real.exp (γ^2*Real.log 2)-1)*(2^β * H b)+1)/2 *
        Real.exp (Real.log ε * ((β-γ^2+(2*γ-θ)^2/2)/2)) +
      2*unitSingularOccupationEnvelope 0 (γ*α) b * Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  filter_upwards [ae_brownian_singular_submeasure_field_increment_le_of_envelope
    hh x 0 hq hq₂ H hH] with b hb
  intro δ ε hε hεhalf
  let μ := Measure.map (fun t => b t) ν
  let S : Set ℂ := {w | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}
  let g : ℂ → ℝ := S.indicator (fun w => Real.exp (-γ*α*Real.log (max ε ‖w‖)))
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const measurable_norm).inter
      ((measurableSet_le measurable_norm measurable_const).inter
        (measurableSet_le measurable_norm measurable_const))
  have hgm : Measurable g := by
    apply Measurable.indicator _ hS
    exact (Real.continuous_exp.comp (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hε).ne')))).measurable
  have hgM : ∀ w, ENNReal.ofReal |g w| ≤
      (ENNReal.ofReal ‖w-(0 : ℂ)‖)^(-(γ*α)) := by
    intro w
    by_cases hw : w ∈ S
    · have hw0 : 0 < ‖w‖ := hε.trans_le hw.1
      rw [show g w = _ from Set.indicator_of_mem hw _, max_eq_right hw.1,
        abs_of_pos (Real.exp_pos _), sub_zero]
      rw [ENNReal.ofReal_rpow_of_pos hw0, Real.rpow_def_of_pos hw0]
      apply le_of_eq
      congr 2
      ring
    · rw [show g w = _ from Set.indicator_of_notMem hw _, abs_zero, ENNReal.ofReal_zero]
      exact zero_le
  have hgs : ∀ w, g w ≠ 0 → ‖w‖ ≤ 1/2 := by
    intro w hw
    by_contra h
    have hn : w ∉ S := fun hwS => h hwS.2.2
    exact hw (Set.indicator_of_notMem hn _)
  have hgs1 : ∀ w, g w ≠ 0 → ‖w‖ ≤ 1 - 1/2 := by
    simpa only [show (1 : ℝ) - 1/2 = 1/2 by norm_num] using hgs
  have hbound := hb g hgm hgM μ le_rfl (R := 1) zero_lt_one hγθ hθ hgs1 ε hε hεhalf
  simp only [Real.log_one, zero_mul, Real.exp_zero, mul_one] at hbound
  refine (le_of_eq ?_).trans hbound
  congr 1
  funext ω
  congr 1
  apply integral_congr_ae
  filter_upwards with w
  by_cases hw : w ∈ S
  · have hhε : ε/2 ≤ ‖w‖ := by linarith [hw.1]
    rw [show S.indicator _ w = _ from Set.indicator_of_mem hw _,
      show g w = _ from Set.indicator_of_mem hw _, max_eq_right hw.1, max_eq_right hhε]
    have heq (r : ℝ) : γ * (hcirc ω r w - hcirc ω 1 0 - α * Real.log ‖w‖) =
        -γ*α*Real.log ‖w‖ + γ*(hcirc ω r w-hcirc ω 1 0) := by ring
    rw [heq (ε/2), heq ε, Real.exp_add, Real.exp_add]
    ring
  · rw [show S.indicator _ w = _ from Set.indicator_of_notMem hw _,
      show g w = _ from Set.indicator_of_notMem hw _, zero_mul]

/-- Under an integrable pair envelope, the expected absolute annular increment is bounded
by the Brownian mean of the pathwise envelope bound. -/
theorem inserted_annular_increment_annealed_bound_of_envelope
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ α β θ ε : ℝ} (hq : 0 < γ*α) (hq₂ : γ*α < 2) (hγθ : γ ≤ θ) (hθ : θ ≤ 2*γ)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (δ : ℝ) (H : ContinuousPath ℂ → ℝ)
    (hHi : Integrable H (planarBrownianMotion x))
    (hH : ∀ᵐ b ∂(planarBrownianMotion x), 0 ≤ H b ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      unitSingularPairNear 0 (γ*α) r b ≤ ENNReal.ofReal (H b * r ^ β)) :
    let I : ContinuousPath ℂ × Ω → ℝ := fun q => ∫ w,
      {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc q.2 (ε/2) w-hcirc q.2 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc q.2 ε w-hcirc q.2 1 0 - α*Real.log (max ε ‖w‖)))) w
      ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))))
    let R : ContinuousPath ℂ → ℝ := fun b =>
      ((Real.exp (γ^2*Real.log 2)-1)*(2^β * H b)+1)/2 *
        Real.exp (Real.log ε * ((β-γ^2+(2*γ-θ)^2/2)/2)) +
      2*unitSingularOccupationEnvelope 0 (γ*α) b * Real.exp (Real.log ε * ((θ-γ)^2/2))
    Integrable I ((planarBrownianMotion x).prod P) ∧
      (∫ q, |I q| ∂((planarBrownianMotion x).prod P)) ≤ ∫ b, R b ∂(planarBrownianMotion x) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  dsimp only
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_inserted_annular_increment hh hε γ α δ
  let R : ContinuousPath ℂ → ℝ := fun b =>
    ((Real.exp (γ^2*Real.log 2)-1)*(2^β * H b)+1)/2 *
      Real.exp (Real.log ε * ((β-γ^2+(2*γ-θ)^2/2)/2)) +
    2*unitSingularOccupationEnvelope 0 (γ*α) b * Real.exp (Real.log ε * ((θ-γ)^2/2))
  have hRi : Integrable R (planarBrownianMotion x) := by
    have ho := integrable_unitSingularOccupationEnvelope x 0 hq hq₂
    exact (((hHi.const_mul _).const_mul _).add (integrable_const 1) |>.div_const 2
      |>.mul_const _).add ((ho.const_mul 2).mul_const _)
  have hfield (b : ContinuousPath ℂ) : Integrable (fun ω => F (b,ω)) P := by
    apply (integrable_inserted_moving_annulus_increment_field hh hε hεhalf γ α δ b).congr
    filter_upwards [hFae] with ω hω
    exact (hω b).symm
  have hbound : ∀ᵐ b ∂(planarBrownianMotion x), (∫ ω, ‖F (b,ω)‖ ∂P) ≤ R b := by
    filter_upwards [ae_inserted_moving_annulus_increment_le_of_envelope
      hh x hq hq₂ hγθ hθ H hH] with b hb
    have heq : (∫ ω, ‖F (b,ω)‖ ∂P) = ∫ ω, |∫ w,
      {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) w-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε w-hcirc ω 1 0 - α*Real.log (max ε ‖w‖)))) w
      ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))))| ∂P := by
      apply integral_congr_ae
      filter_upwards [hFae] with ω hω
      rw [hω b, Real.norm_eq_abs]
    rw [heq]
    exact hb δ ε hε hεhalf
  have hsec : Integrable (fun b => ∫ ω, ‖F (b,ω)‖ ∂P) (planarBrownianMotion x) := by
    apply hRi.mono' (hFm.stronglyMeasurable.norm.integral_prod_right').aestronglyMeasurable
    filter_upwards [hbound] with b hb
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact hb
  have hFi : Integrable F ((planarBrownianMotion x).prod P) :=
    (integrable_prod_iff hFm.aestronglyMeasurable).2 ⟨Filter.Eventually.of_forall hfield, hsec⟩
  have hprod := (Measure.quasiMeasurePreserving_snd (μ := planarBrownianMotion x) (ν := P)).ae hFae
  refine ⟨hFi.congr ?_, ?_⟩
  · filter_upwards [hprod] with q hq
    exact hq q.1
  · calc
      _ = ∫ q, |F q| ∂((planarBrownianMotion x).prod P) := by
        apply integral_congr_ae
        filter_upwards [hprod] with q hq
        rw [hq q.1]
      _ = ∫ b, ∫ ω, ‖F (b,ω)‖ ∂P ∂(planarBrownianMotion x) := by
        simpa only [Real.norm_eq_abs] using integral_prod (fun q => |F q|) hFi.abs
      _ ≤ ∫ b, R b ∂(planarBrownianMotion x) := integral_mono_ae hsec hRi hbound

/-- Under an integrable pair envelope with exponent `β > γ ^ 2 / 2`, expected annular
increments at dyadic scales admit a summable bound independent of the outer radius, for
every `0 < γ * α < 2`. -/
theorem exists_summable_uniform_inserted_annular_increment_bound_of_envelope
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α β : ℝ}
    (hq0 : 0 < γ*α) (hq2 : γ*α < 2) (hγ : 0 < γ) (hβ : γ^2/2 < β)
    (H : ContinuousPath ℂ → ℝ) (hHi : Integrable H (planarBrownianMotion x))
    (hH : ∀ᵐ b ∂(planarBrownianMotion x), 0 ≤ H b ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      unitSingularPairNear 0 (γ*α) r b ≤ ENNReal.ofReal (H b * r ^ β)) :
    ∃ B : ℕ → ℝ, Summable B ∧ ∀ (n : ℕ) (δ : ℝ),
      let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
      ∫ q, |∫ w, {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc q.2 (ε/2) w-hcirc q.2 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc q.2 ε w-hcirc q.2 1 0 - α*Real.log (max ε ‖w‖)))) w
        ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))))| ∂((planarBrownianMotion x).prod P) ≤ B n := by
  obtain ⟨θ, hγθ, hθ, hdecay⟩ := exists_annular_moment_exponent hγ hβ
  let A : ContinuousPath ℂ → ℝ := fun b =>
    ((Real.exp (γ^2*Real.log 2)-1)*(2^β * H b)+1)/2
  let B : ContinuousPath ℂ → ℝ := fun b => 2*unitSingularOccupationEnvelope 0 (γ*α) b
  have hAi : Integrable A (planarBrownianMotion x) :=
    ((hHi.const_mul _).const_mul _ |>.add (integrable_const 1)).div_const 2
  have hBi : Integrable B (planarBrownianMotion x) :=
    (integrable_unitSingularOccupationEnvelope x 0 hq0 hq2).const_mul 2
  let c : ℝ := (β-γ^2+(2*γ-θ)^2/2)/2
  let e : ℝ := (θ-γ)^2/2
  have hc : 0 < c := half_pos hdecay
  have he : 0 < e := by
    have h : 0 < θ - γ := sub_pos.mpr hγθ
    dsimp [e]
    positivity
  have hs : Summable (fun n : ℕ =>
      (∫ b, A b ∂(planarBrownianMotion x)) * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1))*c) +
      (∫ b, B b ∂(planarBrownianMotion x)) * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1))*e)) := by
    have h1 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul hc
    have h2 := LatticeProb.Gauss.summable_exp_log_dyadicScale_mul he
    exact (summable_nat_add_iff 1).2 ((h1.mul_left _).add (h2.mul_left _))
  refine ⟨_, hs, ?_⟩
  intro n δ
  have hpos : 0 < (2 : ℝ)⁻¹ ^ (n+1) := by positivity
  have hhalf : (2 : ℝ)⁻¹ ^ (n+1) ≤ 1/2 := by
    rw [pow_succ]
    have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  have hb := (inserted_annular_increment_annealed_bound_of_envelope hh x hq0 hq2
    hγθ.le hθ.le hpos hhalf δ H hHi hH).2
  dsimp only at hb ⊢
  calc
    _ ≤ ∫ b, A b * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1))*c) +
        B b * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1))*e) ∂(planarBrownianMotion x) := hb
    _ = _ := by
      rw [integral_add (hAi.mul_const _) (hBi.mul_const _), integral_mul_const,
        integral_mul_const]

/-- Under an integrable pair envelope with exponent `β > γ ^ 2 / 2`, the expected absolute
increment of an inserted closed-cutoff occupation admits a summable bound independent of
the outer cutoff, for every `0 < γ * α < 2`. -/
theorem exists_summable_uniform_inserted_cutoff_increment_bound_of_envelope
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α β : ℝ}
    (hq0 : 0 < γ * α) (hq2 : γ * α < 2) (hγ : 0 < γ) (hβ : γ^2/2 < β)
    (H : ContinuousPath ℂ → ℝ) (hHi : Integrable H (planarBrownianMotion x))
    (hH : ∀ᵐ b ∂(planarBrownianMotion x), 0 ≤ H b ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      unitSingularPairNear 0 (γ*α) r b ≤ ENNReal.ofReal (H b * r ^ β)) :
    ∃ B : ℕ → ℝ≥0∞, (∑' n, B n) < ∞ ∧ ∀ (n : ℕ) (δ : ℝ),
      let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
      (∫⁻ q : ContinuousPath ℂ × Ω, ENNReal.ofReal |(∫ z,
        {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => (ε/2)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (ε/2) z)) z
          ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1))))) -
        ∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) ε z)) z
          ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1))))|
        ∂((planarBrownianMotion x).prod P)) ≤ B n := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨A, hAs, hA⟩ := exists_summable_uniform_inserted_annular_increment_bound_of_envelope
    hh x hq0 hq2 hγ hβ H hHi hH
  obtain ⟨C, hCs, hC⟩ := exists_summable_uniform_inner_inserted_expectation_bound hh x γ α
    ((γ*α+2)/2) hq0 (by linarith) (by linarith)
  obtain ⟨θ, hγθ, hθ, _⟩ := exists_annular_moment_exponent hγ hβ
  refine ⟨fun n => ENNReal.ofReal (A n) + C n + C n, ?_, ?_⟩
  · rw [ENNReal.tsum_add, ENNReal.tsum_add]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨hAs.tsum_ofReal_ne_top.lt_top, hCs⟩, hCs⟩
  · intro n δ
    let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hεhalf : ε ≤ 1/2 := by
      dsimp [ε]
      rw [pow_succ]
      have h : (2 : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    let I (q : ContinuousPath ℂ × Ω) : ℝ := ∫ z,
      {z : ℂ | ε ≤ ‖z‖ ∧ ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
        (fun z => (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc q.2 (ε/2) z - hcirc q.2 1 0 -
          α*Real.log (max (ε/2) ‖z‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc q.2 ε z - hcirc q.2 1 0 -
          α*Real.log (max ε ‖z‖)))) z
        ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))))
    let K (r : ℝ) (q : Ω × ContinuousPath ℂ) : ℝ≥0∞ :=
      ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal
        ({z : ℂ | ‖z‖ < ε}.indicator (fun z => r^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc q.1) r z)) (q.2 s.toNNReal))
    have hI : Integrable I ((planarBrownianMotion x).prod P) :=
      (inserted_annular_increment_annealed_bound_of_envelope hh x hq0 hq2
        hγθ.le hθ.le hε hεhalf δ H hHi hH).1
    have hK (r : ℝ) (hr : 0 < r) : AEMeasurable (K r) (P.prod (planarBrownianMotion x)) :=
      aemeasurable_inner_inserted_clock_cell hh (planarBrownianMotion x) hr γ α ε 0 1
    have hKa (r : ℝ) (hr : 0 < r) :
        AEMeasurable (fun q : ContinuousPath ℂ × Ω => K r (q.2,q.1))
          ((planarBrownianMotion x).prod P) := (hK r hr).prod_swap
    have hpoint : ∀ᵐ q : ContinuousPath ℂ × Ω ∂((planarBrownianMotion x).prod P),
        ENNReal.ofReal |(∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => (ε/2)^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) (ε/2) z)) z
          ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1))))) -
          ∫ z, {z : ℂ | ‖z‖ ≤ δ ∧ ‖z‖ ≤ 1/2}.indicator
          (fun z => ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc q.2) ε z)) z
          ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1))))| ≤
          ENNReal.ofReal |I q| + K (ε/2) (q.2,q.1) + K ε (q.2,q.1) := by
      filter_upwards [(Measure.quasiMeasurePreserving_snd
        (μ := planarBrownianMotion x) (ν := P)).ae
          (ae_inserted_closedBall_occupation_increment_le hh γ α)] with q hq
      exact hq q.1 ε δ hε hεhalf
    calc
      _ ≤ ∫⁻ q, (ENNReal.ofReal |I q| + K (ε/2) (q.2,q.1) + K ε (q.2,q.1))
          ∂((planarBrownianMotion x).prod P) := lintegral_mono_ae hpoint
      _ = (∫⁻ q, ENNReal.ofReal |I q| ∂((planarBrownianMotion x).prod P)) +
          (∫⁻ q, K (ε/2) (q.2,q.1) ∂((planarBrownianMotion x).prod P)) +
          ∫⁻ q, K ε (q.2,q.1) ∂((planarBrownianMotion x).prod P) := by
        change (∫⁻ q, ((fun q : ContinuousPath ℂ × Ω => ENNReal.ofReal |I q|) +
          (fun q : ContinuousPath ℂ × Ω => K (ε/2) (q.2,q.1))) q + K ε (q.2,q.1)
          ∂((planarBrownianMotion x).prod P)) = _
        rw [lintegral_add_left' (hI.abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal.add
          (hKa (ε/2) (half_pos hε)))]
        change (∫⁻ q, ENNReal.ofReal |I q| + K (ε/2) (q.2,q.1)
          ∂((planarBrownianMotion x).prod P)) + _ = _
        rw [lintegral_add_left' hI.abs.aestronglyMeasurable.aemeasurable.ennreal_ofReal]
      _ ≤ ENNReal.ofReal (A n) + C n + C n := by
        have hIA : (∫⁻ q, ENNReal.ofReal |I q| ∂((planarBrownianMotion x).prod P)) ≤
            ENNReal.ofReal (A n) := by
          rw [← ofReal_integral_eq_lintegral_ofReal hI.abs
            (Filter.Eventually.of_forall fun _ => abs_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (hA n δ)
        have hK1 : (∫⁻ q, K (ε/2) (q.2,q.1) ∂((planarBrownianMotion x).prod P)) ≤ C n := by
          change (∫⁻ q, K (ε/2) q.swap ∂((planarBrownianMotion x).prod P)) ≤ C n
          rw [lintegral_prod_swap]
          exact hC n (ε/2) (half_pos hε) (by linarith)
        have hK2 : (∫⁻ q, K ε (q.2,q.1) ∂((planarBrownianMotion x).prod P)) ≤ C n := by
          change (∫⁻ q, K ε q.swap ∂((planarBrownianMotion x).prod P)) ≤ C n
          rw [lintegral_prod_swap]
          exact hC n ε hε hεhalf
        exact add_le_add (add_le_add hIA hK1) hK2

end HarmonicBalls
