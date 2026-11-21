import HarmonicBalls.Proofs.Potential.LQGClockInsertedAnnealedSummability
import HarmonicBalls.Proofs.Potential.BrownianSingularShiftedRieszEnergy

/-! # Annular inserted clock increments from a pair envelope

The truncated second-moment estimate for inserted annular clock increments uses the Brownian
occupation measure only through the singular first moment and an integrable envelope for the
near-diagonal singular pair occupations at all radii. The weighted pair energy with a Riesz
kernel supplies such an envelope, which gives summable expected annular increments whenever
`γ ^ 2 / 2 < 2 - γ * α`.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
open scoped NNReal ENNReal
namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- An all-radius pair envelope controls singularly dominated weights on every submeasure
of the occupation measure. -/
theorem ae_unit_singular_weighted_submeasure_le_of_envelope (x z : ℂ) {q d : ℝ}
    (E : ContinuousPath ℂ → ℝ) (hE0 : ∀ b, 0 ≤ E b)
    (hE : ∀ᵐ b ∂(planarBrownianMotion x), ∀ r : ℝ, 0 < r →
      unitSingularPairNear z q r b ≤ ENNReal.ofReal (E b) * ENNReal.ofReal (r ^ d)) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ (g : ℂ → ℝ), Measurable g →
      (∀ y, ENNReal.ofReal |g y| ≤ (ENNReal.ofReal ‖y-z‖) ^ (-q)) →
      ∀ (μ : Measure ℂ), μ ≤ Measure.map (fun t => b t) ν → ∀ r : ℝ, 0 < r →
      Integrable (fun p : ℂ × ℂ =>
        if ‖p.1-p.2‖ < r then |g p.1| * |g p.2| else 0) (μ.prod μ) ∧
      (∫ p : ℂ × ℂ, if ‖p.1-p.2‖ < r then |g p.1| * |g p.2| else 0 ∂(μ.prod μ)) ≤
        E b * r ^ d := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [hE] with b hb
  intro g hg hgq μ hμ r hr
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
  have hEr : 0 ≤ E b * r ^ d := mul_nonneg (hE0 b) (Real.rpow_nonneg hr.le _)
  have hmap : ρ.prod ρ = Measure.map (Prod.map b b) (ν.prod ν) :=
    Measure.map_prod_map ν ν hbm hbm
  have hlin : (∫⁻ p, ENNReal.ofReal (f p) ∂(ρ.prod ρ)) ≤ ENNReal.ofReal (E b * r ^ d) := by
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
      _ ≤ ENNReal.ofReal (E b) * ENNReal.ofReal (r ^ d) := hb r hr
      _ = _ := (ENNReal.ofReal_mul (hE0 b)).symm
  have hfi : Integrable f (ρ.prod ρ) := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have heq : (∫⁻ p, ‖f p‖ₑ ∂(ρ.prod ρ)) = (∫⁻ p, ENNReal.ofReal (f p) ∂(ρ.prod ρ)) := by
      apply lintegral_congr
      intro p
      rw [Real.enorm_of_nonneg (hf0 p)]
    rw [heq]
    exact lt_of_le_of_lt hlin ENNReal.ofReal_lt_top
  have hfρ : (∫ p, f p ∂(ρ.prod ρ)) ≤ E b * r ^ d := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlin
    rw [← ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0),
      ENNReal.toReal_ofReal (integral_nonneg hf0), ENNReal.toReal_ofReal hEr] at h
    exact h
  refine ⟨hfi.mono_measure (Measure.prod_mono hμ hμ), ?_⟩
  refine (integral_mono_measure (Measure.prod_mono hμ hμ) ?_ hfi).trans hfρ
  filter_upwards with p
  exact hf0 p

/-- The field-increment estimate holds for all singularly dominated occupation weights,
given an all-radius pair envelope. -/
theorem ae_brownian_singular_submeasure_field_increment_le_of_envelope
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x z : ℂ)
    {q d : ℝ} (hq : 0 < q) (hq2 : q < 2)
    (E : ContinuousPath ℂ → ℝ) (hE0 : ∀ b, 0 ≤ E b)
    (hE : ∀ᵐ b ∂(planarBrownianMotion x), ∀ r : ℝ, 0 < r →
      unitSingularPairNear z q r b ≤ ENNReal.ofReal (E b) * ENNReal.ofReal (r ^ d)) :
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
        (2^d * E b)+1)/2 *
        Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
      2*unitSingularOccupationEnvelope z q b *
        Real.exp (Real.log R * (γ^2/2-(θ-γ)^2/2))*
        Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [planarBrownianMotion_ae_unit_singular_weighted_submeasure_integrable
      x z hq hq2,
    ae_unit_singular_weighted_submeasure_le_of_envelope x z E hE0 hE] with b hfirst hpair
  intro g hg hgq μ hμ R γ θ hR hγθ hθ hgs ε hε hεhalf
  let ρ : Measure ℂ := Measure.map (fun t => b t) ν
  let : IsProbabilityMeasure ρ := inferInstance
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le ρ hμ
  obtain ⟨hgi, hA⟩ := hfirst g hg hgq μ hμ
  obtain ⟨_, hI⟩ := hpair g hg hgq μ hμ (2*ε) (by positivity)
  have hI' : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤
      (2^d * E b) * Real.exp (Real.log ε*d) := by
    have hhI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
        (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤ E b * (2*ε)^d := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hI
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le,
      Real.rpow_def_of_pos hε] at hhI
    convert hhI using 1; ring
  exact field_increment_le_rate_of_radius hh hε hR μ hg hgi
    (fun y hy => by linarith [hgs y hy]) hγθ hθ hA hI'

/-- A moving annular inserted increment is bounded by integrable Brownian occupation
envelopes, given an all-radius pair envelope. -/
theorem ae_inserted_moving_annulus_le_of_envelope
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ α d θ : ℝ} (hq : 0 < γ*α) (hq2 : γ*α < 2)
    (E : ContinuousPath ℂ → ℝ) (hE0 : ∀ b, 0 ≤ E b)
    (hE : ∀ᵐ b ∂(planarBrownianMotion x), ∀ r : ℝ, 0 < r →
      unitSingularPairNear 0 (γ*α) r b ≤ ENNReal.ofReal (E b) * ENNReal.ofReal (r ^ d))
    (hγθ : γ ≤ θ) (hθ : θ ≤ 2*γ) :
    let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
    ∀ᵐ b ∂(planarBrownianMotion x), ∀ δ ε : ℝ, 0 < ε → ε ≤ 1/2 →
      let μ := Measure.map (fun t => b t) ν
      (∫ ω, |∫ w, {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) w-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε w-hcirc ω 1 0 - α*Real.log (max ε ‖w‖)))) w ∂μ| ∂P) ≤
      ((Real.exp (γ^2*Real.log 2)-1)*(2^d * E b)+1)/2 *
        Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
      2*unitSingularOccupationEnvelope 0 (γ*α) b * Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  filter_upwards [ae_brownian_singular_submeasure_field_increment_le_of_envelope hh x 0 hq hq2
    E hE0 hE] with b hb
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

/-- The expected absolute annular increment is bounded by the mean of the occupation
envelopes, given an integrable all-radius pair envelope. -/
theorem inserted_annular_increment_annealed_bound_of_envelope
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ α d θ ε : ℝ} (hq : 0 < γ*α) (hq2 : γ*α < 2)
    (E : ContinuousPath ℂ → ℝ) (hE0 : ∀ b, 0 ≤ E b)
    (hEi : Integrable E (planarBrownianMotion x))
    (hE : ∀ᵐ b ∂(planarBrownianMotion x), ∀ r : ℝ, 0 < r →
      unitSingularPairNear 0 (γ*α) r b ≤ ENNReal.ofReal (E b) * ENNReal.ofReal (r ^ d))
    (hγθ : γ ≤ θ) (hθ : θ ≤ 2*γ)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (δ : ℝ) :
    let I : ContinuousPath ℂ × Ω → ℝ := fun q => ∫ w,
      {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc q.2 (ε/2) w-hcirc q.2 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc q.2 ε w-hcirc q.2 1 0 - α*Real.log (max ε ‖w‖)))) w
      ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))))
    let R : ContinuousPath ℂ → ℝ := fun b =>
      ((Real.exp (γ^2*Real.log 2)-1)*(2^d * E b)+1)/2 *
        Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
      2*unitSingularOccupationEnvelope 0 (γ*α) b * Real.exp (Real.log ε * ((θ-γ)^2/2))
    Integrable I ((planarBrownianMotion x).prod P) ∧
      (∫ q, |I q| ∂((planarBrownianMotion x).prod P)) ≤ ∫ b, R b ∂(planarBrownianMotion x) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  dsimp only
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_inserted_annular_increment hh hε γ α δ
  let R : ContinuousPath ℂ → ℝ := fun b =>
    ((Real.exp (γ^2*Real.log 2)-1)*(2^d * E b)+1)/2 *
      Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
    2*unitSingularOccupationEnvelope 0 (γ*α) b * Real.exp (Real.log ε * ((θ-γ)^2/2))
  have hRi : Integrable R (planarBrownianMotion x) := by
    have ho := integrable_unitSingularOccupationEnvelope x 0 hq hq2
    exact (((hEi.const_mul _).const_mul _).add (integrable_const 1) |>.div_const 2 |>.mul_const _).add
      ((ho.const_mul 2).mul_const _)
  have hfield (b : ContinuousPath ℂ) : Integrable (fun ω => F (b,ω)) P := by
    apply (integrable_inserted_moving_annulus_increment_field hh hε hεhalf γ α δ b).congr
    filter_upwards [hFae] with ω hω
    exact (hω b).symm
  have hbound : ∀ᵐ b ∂(planarBrownianMotion x), (∫ ω, ‖F (b,ω)‖ ∂P) ≤ R b := by
    filter_upwards [ae_inserted_moving_annulus_le_of_envelope hh x hq hq2 E hE0 hE hγθ hθ]
      with b hb
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

/-- Exponents for the weighted pair route: a Riesz exponent `β` with `q + β < 2` and a
Gaussian truncation level `θ` with positive decay. -/
theorem exists_weighted_pair_clock_exponents {q γ : ℝ} (hγ : 0 < γ)
    (hsub : γ ^ 2 / 2 < 2 - q) :
    ∃ β θ : ℝ, 0 < β ∧ q + β < 2 ∧ γ < θ ∧ θ < 2*γ ∧ 0 < β-γ^2+(2*γ-θ)^2/2 := by
  obtain ⟨β, hβl, hβu⟩ := exists_between hsub
  have hβ0 : 0 < β := lt_of_le_of_lt (by positivity : 0 ≤ γ^2/2) hβl
  let e : ℝ := β-γ^2/2
  have he : 0 < e := by dsimp [e]; linarith
  have hv : γ < min (2*γ) (γ + e/(γ+1)) := by
    apply lt_min
    · linarith
    · have : 0 < e/(γ+1) := div_pos he (by linarith)
      linarith
  obtain ⟨θ, hθl, hθu⟩ := exists_between hv
  have hθ2 : θ < 2*γ := hθu.trans_le (min_le_left _ _)
  have hθe : θ-γ < e/(γ+1) := by
    have := hθu.trans_le (min_le_right (2*γ) (γ + e/(γ+1)))
    linarith
  have hmulθ : (θ-γ)*(γ+1) < e := (lt_div_iff₀ (by linarith : 0 < γ+1)).mp hθe
  have hsq : 0 ≤ (θ-γ)^2 := sq_nonneg _
  refine ⟨β, θ, hβ0, by linarith, hθl, hθ2, ?_⟩
  dsimp [e] at hmulθ
  nlinarith

/-- Expected annular increments admit a summable bound independent of the outer radius
whenever `γ ^ 2 / 2 < 2 - γ * α`. -/
theorem exists_summable_uniform_inserted_annular_increment_bound_of_lt_two_sub
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ α : ℝ}
    (hq0 : 0 < γ*α) (hγ : 0 < γ) (hsub : γ^2/2 < 2 - γ*α) :
    ∃ B : ℕ → ℝ, Summable B ∧ ∀ (n : ℕ) (δ : ℝ),
      let ε : ℝ := (2 : ℝ)⁻¹ ^ (n+1)
      Integrable (fun q : ContinuousPath ℂ × Ω => ∫ w,
        {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc q.2 (ε/2) w-hcirc q.2 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc q.2 ε w-hcirc q.2 1 0 - α*Real.log (max ε ‖w‖)))) w
        ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))))) ((planarBrownianMotion x).prod P) ∧
      ∫ q, |∫ w, {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc q.2 (ε/2) w-hcirc q.2 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc q.2 ε w-hcirc q.2 1 0 - α*Real.log (max ε ‖w‖)))) w
        ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))))| ∂((planarBrownianMotion x).prod P) ≤ B n := by
  have hγ2 : 0 ≤ γ^2/2 := by positivity
  have hq2 : γ*α < 2 := by linarith
  obtain ⟨β, θ, hβ, hqβ, hγθ, hθ, hdecay⟩ := exists_weighted_pair_clock_exponents hγ hsub
  let E : ContinuousPath ℂ → ℝ := unitSingularWeightedPairEnergyReal 0 (γ*α) β
  have hE0 : ∀ b, 0 ≤ E b := fun _ => ENNReal.toReal_nonneg
  have hEi : Integrable E (planarBrownianMotion x) :=
    integrable_unitSingularWeightedPairEnergyReal x 0 hq0 hβ hqβ
  have hE := planarBrownianMotion_ae_unitSingularPairNear_le_weightedPairEnergy x 0 hq0 hβ hqβ
  let A : ContinuousPath ℂ → ℝ := fun b =>
    ((Real.exp (γ^2*Real.log 2)-1)*(2^β * E b)+1)/2
  let B : ContinuousPath ℂ → ℝ := fun b => 2*unitSingularOccupationEnvelope 0 (γ*α) b
  have hAi : Integrable A (planarBrownianMotion x) :=
    ((hEi.const_mul _).const_mul _ |>.add (integrable_const 1)).div_const 2
  have hBi : Integrable B (planarBrownianMotion x) :=
    (integrable_unitSingularOccupationEnvelope x 0 hq0 hq2).const_mul 2
  let c : ℝ := (β-γ^2+(2*γ-θ)^2/2)/2
  let e : ℝ := (θ-γ)^2/2
  have hc : 0 < c := by dsimp [c]; positivity
  have he : 0 < e := by
    have : 0 < θ - γ := by linarith
    dsimp [e]; positivity
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
  have hb := inserted_annular_increment_annealed_bound_of_envelope hh x hq0 hq2 E hE0 hEi hE
    hγθ.le hθ.le hpos hhalf δ
  dsimp only at hb ⊢
  refine ⟨hb.1, ?_⟩
  calc
    _ ≤ ∫ b, A b * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1))*c) +
        B b * Real.exp (Real.log ((2 : ℝ)⁻¹ ^ (n+1))*e) ∂(planarBrownianMotion x) := hb.2
    _ = _ := by
      rw [integral_add (hAi.mul_const _) (hBi.mul_const _), integral_mul_const,
        integral_mul_const]

end HarmonicBalls
