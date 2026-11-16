import HarmonicBalls.Proofs.Potential.LQGClockExistenceProved
import HarmonicBalls.Proofs.Potential.BrownianOccupationWeightedMeasure
import LatticeProb.LQG.GMCL1Rate

/-! # Annular increments of Liouville clocks

Unit-time Brownian occupation of an annulus away from the logarithmic insertion
has a geometric bound on the field expectation of successive scale increments.
The same bound holds uniformly over earlier stopping horizons.
-/

open MeasureTheory Real Set
open scoped NNReal ENNReal
namespace HarmonicBalls

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

private theorem brownian_field_increment_rate
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ)
    {g : ℂ → ℝ} (hg : Measurable g) {M : ℝ} (hM : 0 ≤ M)
    (hgM : ∀ z, |g z| ≤ M) (hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ 1 / 2) :
    ∃ θ d : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 ≤ C ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
        let μ := Measure.map (fun t => b t) ν
        (∫ ω, |∫ z, g z * ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*C+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, _⟩ := exists_clock_truncation_exponents hγ0 hγ2
  refine ⟨θ, d, hγθ, hθ, hd0, hd2, hp, ?_⟩
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [planarBrownianMotion_ae_unit_weighted_occupation_measure_le x hd0 hd2] with b hb
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨M^2*C*2^d, by positivity, ?_⟩
  intro ε hε hεhalf
  let μ : Measure ℂ := Measure.map (fun t => b t) ν
  let : IsProbabilityMeasure μ := inferInstance
  have hgi : Integrable g μ := by
    refine (integrable_const M).mono' hg.aestronglyMeasurable ?_
    filter_upwards with z
    simpa [Real.norm_eq_abs] using hgM z
  have hA : (∫ z, |g z| ∂μ) ≤ M := by
    calc
      _ ≤ ∫ _ : ℂ, M ∂μ := integral_mono hgi.abs (integrable_const M) (fun z => hgM z)
      _ = M := by simp
  have hpair := (hb g hg M hM hgM (2*ε) (by positivity)).2.2
  have hI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤
      (M^2*C*2^d)*Real.exp (Real.log ε*d) := by
    have hI' : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤ M^2*(C*(2*ε)^d) := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using hpair
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hε.le,
      Real.rpow_def_of_pos hε] at hI'
    convert hI' using 1; ring
  exact field_increment_le_rate hh hε μ hg hgi (fun z hz => by linarith [hgs z hz])
    hγθ.le hθ.le hA hI

private theorem brownian_field_submeasure_increment_rate
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (x : ℂ)
    {g : ℂ → ℝ} (hg : Measurable g) {M : ℝ} (hM : 0 ≤ M)
    (hgM : ∀ z, |g z| ≤ M) (hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ 1 / 2) :
    ∃ θ d : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 ≤ C ∧
        ∀ μ : Measure ℂ, μ ≤ Measure.map (fun t => b t) ν →
        ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 →
        (∫ ω, |∫ z, g z * ((ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*C+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, _⟩ := exists_clock_truncation_exponents hγ0 hγ2
  refine ⟨θ, d, hγθ, hθ, hd0, hd2, hp, ?_⟩
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [planarBrownianMotion_ae_unit_weighted_occupation_measure_le x hd0 hd2] with b hb
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨M^2*C*2^d, by positivity, ?_⟩
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
      ∂(μ.prod μ)) ≤ M^2*(C*(2*ε)^d) := by
    apply (integral_mono_measure (Measure.prod_mono hμ hμ) ?_ hpair0.1).trans hpair0.2.2
    filter_upwards with p
    split_ifs <;> positivity
  have hI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤
      (M^2*C*2^d)*Real.exp (Real.log ε*d) := by
    have hI' : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1-p.2‖ < 2*ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(μ.prod μ)) ≤ M^2*(C*(2*ε)^d) := by
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

/-- Unit-time Brownian occupation increments of the inserted field on an annulus
obey a geometric field-expectation bound for almost every Brownian path. -/
theorem ae_brownian_annular_inserted_increment_le
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 ≤ C ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        let μ := Measure.map (fun t => b t) ν
        (∫ ω, |∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*C+1)/2 *
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
    brownian_field_increment_rate hh hγ0 hγ2 x hgm hM hgM hgs
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  filter_upwards [hb] with b hb
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨C, hC, ?_⟩
  intro ε hε hεhalf hεδ
  have hbound := hb ε hε hεhalf
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

/-- Brownian occupation increments of the inserted field on an annulus obey a
geometric field-expectation bound uniformly over all stopping horizons up to time one. -/
theorem ae_brownian_stopped_annular_inserted_increment_le
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x), ∃ C : ℝ, 0 ≤ C ∧
        ∀ T : ℝ≥0, ∀ ε : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        let μ := Measure.map (fun t => b t) (ν.restrict (Iic T))
        (∫ ω, |∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) z-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖z‖))) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*C+1)/2 *
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
    brownian_field_submeasure_increment_rate hh hγ0 hγ2 x hgm hM hgM hgs
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  filter_upwards [hb] with b hb
  obtain ⟨C, hC, hb⟩ := hb
  refine ⟨C, hC, ?_⟩
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

end HarmonicBalls
