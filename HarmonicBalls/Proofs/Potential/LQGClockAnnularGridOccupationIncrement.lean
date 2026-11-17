import HarmonicBalls.Proofs.Potential.LQGClockAnnularGridRadiusIncrement
import HarmonicBalls.Proofs.Potential.LQGClockAnnularExitUniformIntegrability
import HarmonicBalls.Proofs.Potential.LQGClockAnnularSupremum

/-! # Annular clock increments at nearby radii

Relative density estimates and annealed increment bounds transfer to stopped
Brownian occupation integrals at positive annular cutoffs.
-/

open MeasureTheory Set MarkovProcess Filter HarmonicBalls.Section6
open scoped Topology NNReal ENNReal

namespace HarmonicBalls

/-- A relative estimate on continuous annular densities transfers to their
occupation integrals over every bounded nonnegative time interval. -/
theorem abs_annular_occupation_sub_le (f g : ℂ → ℝ) (hf : Continuous f)
    (hg : Continuous g) (δ C : ℝ)
    (hfg : ∀ z, δ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → |f z - g z| ≤ C * g z)
    (b : ContinuousPath ℂ) {T : ℝ} (hT : 0 ≤ T) :
    |(∫ t in (0 : ℝ)..T, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b t.toNNReal)) -
      (∫ t in (0 : ℝ)..T, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator g (b t.toNNReal))| ≤
    C * (∫ t in (0 : ℝ)..T, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator g (b t.toNNReal)) := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let F : ℝ → ℝ := fun t => A.indicator f (b t.toNNReal)
  let G : ℝ → ℝ := fun t => A.indicator g (b t.toNNReal)
  have hF : IntervalIntegrable F volume 0 T := intervalIntegrable_annular_density f hf δ b 0 T
  have hG : IntervalIntegrable G volume 0 T := intervalIntegrable_annular_density g hg δ b 0 T
  have hp (t : ℝ) : |F t - G t| ≤ C * G t := by
    dsimp [F, G]
    by_cases hz : b t.toNNReal ∈ A
    · simp only [Set.indicator_of_mem hz]
      exact hfg _ hz.1 hz.2
    · simp [Set.indicator_of_notMem hz]
  change |(∫ t in (0 : ℝ)..T, F t) - ∫ t in (0 : ℝ)..T, G t| ≤ C * ∫ t in (0 : ℝ)..T, G t
  rw [← intervalIntegral.integral_sub hF hG]
  calc
    _ ≤ ∫ t in (0 : ℝ)..T, |F t - G t| := intervalIntegral.abs_integral_le_integral_abs hT
    _ ≤ ∫ t in (0 : ℝ)..T, C * G t := by
      apply intervalIntegral.integral_mono_on hT (hF.sub hG).abs (hG.const_mul C)
      exact fun t _ => hp t
    _ = _ := intervalIntegral.integral_const_mul C G

private theorem continuous_inserted_density_at_radius (hcirc : ℝ → ℂ → ℝ)
    (γ α r : ℝ) (hr : 0 < r) (hc : Continuous (hcirc r))
    (hrec : ∀ z, hcirc r z - hcirc 1 0 - α * Real.log (max r ‖z‖) =
      LatticeProb.Gauss.fieldCircleAverage α hcirc r z) :
    Continuous (fun z => r^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α hcirc r z)) := by
  have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α hcirc r z) =
      fun z => hcirc r z - hcirc 1 0 - α * Real.log (max r ‖z‖) := by
    funext z
    exact (hrec z).symm
  have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α hcirc r z) := by
    rw [heq]
    exact (hc.sub continuous_const).sub (continuous_const.mul
      ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
  exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))

/-- The nearby-radius density modulus controls actual stopped annular clocks
simultaneously for every path and finite time. -/
theorem ae_eventually_annular_stopped_occupation_radial_difference_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (α γ : ℝ)
    {δ a : ℝ} (hδ : 0 < δ) (ha : 0 < a) (D : Set ℂ) :
    ∃ β : ℝ, 0 < β ∧ ∀ᵐ ω ∂P, ∀ᶠ k in atTop,
      ∀ (b : ContinuousPath ℂ) (t : ℝ≥0) (s r : ℝ),
        dyadicScale k / 2 ≤ s → s ≤ dyadicScale k →
        dyadicScale k / 2 ≤ r → r ≤ dyadicScale k →
        |s - r| < dyadicScale k * dyadicScale k ^ a →
        let B := |γ| * dyadicScale k ^ β + γ ^ 2 * dyadicScale k ^ a
        |(∫ u in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            s ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) s z)) (b u.toNNReal)) -
         (∫ u in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            r ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)) (b u.toNNReal))| ≤
          B * Real.exp B * (∫ u in (0 : ℝ)..min (t : ℝ) (ContinuousPath.exitTime D b).toReal,
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            r ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)) (b u.toNNReal)) := by
  obtain ⟨β, hβ, hmod⟩ := ae_eventually_annular_density_radial_difference_le hh α γ hδ ha
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  refine ⟨β, hβ, ?_⟩
  filter_upwards [hmod, hHae, ae_recentered_inserted_circle_average hh α] with ω hω hc hrec
  have hcont : ∀ r, 0 < r → Continuous (hcirc ω r) := by
    intro r hr
    rw [← funext (hc r)]
    exact hHc ω r hr
  filter_upwards [hω] with k hk b t s r hs1 hs2 hr1 hr2 hsr
  have hs : 0 < s := (half_pos (dyadicScale_pos k)).trans_le hs1
  have hr : 0 < r := (half_pos (dyadicScale_pos k)).trans_le hr1
  apply abs_annular_occupation_sub_le _ _
    (continuous_inserted_density_at_radius _ γ α s hs (hcont s hs) (fun z => hrec s z hs))
    (continuous_inserted_density_at_radius _ γ α r hr (hcont r hr) (fun z => hrec r z hr))
  · exact fun z hz hz' => hk z hz hz' s r hs1 hs2 hr1 hr2 hsr
  · exact le_min t.coe_nonneg ENNReal.toReal_nonneg


private theorem radius_exp_bound_algebra {u p d a q B C M I A : ℝ}
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


/-- A same-shell field increment obeys a rate controlled by the weighted
pair integral and the total mass of the weight. -/
theorem field_radius_increment_le_rate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {s ε γ θ d C M : ℝ}
    (hs : 0 < s) (hsε : s ≤ ε) (hs2 : ε / 2 ≤ s)
    (ν : Measure ℂ) [SFinite ν] {g : ℂ → ℝ}
    (hgm : Measurable g) (hg : Integrable g ν)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ 1)
    (hγθ : γ ≤ θ) (hθ : θ ≤ 2 * γ)
    (hA : (∫ z, |g z| ∂ν) ≤ M)
    (hI : (∫ p : ℂ × ℂ, {p : ℂ × ℂ | ‖p.1 - p.2‖ < 2 * ε}.indicator
      (fun p => |g p.1| * |g p.2|) p ∂(ν.prod ν)) ≤ C * Real.exp (Real.log ε * d)) :
    ∫ ω, |∫ z, g z * (s ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω s z - hcirc ω 1 0)) -
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * (hcirc ω ε z - hcirc ω 1 0))) ∂ν| ∂P ≤
      ((Real.exp (γ ^ 2 * Real.log 2) - 1) * C + 1) / 2 *
        Real.exp (Real.log ε * ((d - γ ^ 2 + (2 * γ - θ) ^ 2 / 2) / 2)) +
      2 * M * Real.exp (Real.log ε * ((θ - γ) ^ 2 / 2)) := by
  have hε : 0 < ε := hs.trans_le hsε
  let p : ℝ := 2 * γ ^ 2 - (2 * γ - θ) ^ 2 / 2
  let q : ℝ := γ ^ 2 / 2 - (θ - γ) ^ 2 / 2
  let u : ℝ := Real.log ε
  let B : ℝ := Real.exp (γ ^ 2 * Real.log 2) - 1
  have hB : 0 ≤ B := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hratio : ε / s ≤ 2 := by rw [div_le_iff₀ hs]; linarith
  have hB' : Real.exp (γ ^ 2 * Real.log (ε / s)) - 1 ≤ B := by
    dsimp [B]
    have hlog := Real.log_le_log (div_pos hε hs) hratio
    have hh' := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hlog (sq_nonneg γ))
    linarith
  have hI0 : 0 ≤ ∫ x : ℂ × ℂ, {x : ℂ × ℂ | ‖x.1 - x.2‖ < 2 * ε}.indicator
      (fun x => |g x.1| * |g x.2|) x ∂(ν.prod ν) :=
    integral_nonneg fun x => Set.indicator_nonneg (fun _ _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)) x
  have hraw := hh.integral_abs_integral_increment_le_of_le hs hsε (R := 1) zero_lt_one ν hgm hg hgR hγθ hθ
    (t := Real.exp (u * ((d - p) / 2))) (Real.exp_pos _)
  have hlog : Real.log (1 / ε) = -u := by simp [u]
  conv at hraw =>
    rhs
    rw [hlog, Real.rpow_def_of_pos hε]
  have halg := radius_exp_bound_algebra (u := u) (p := p) (d := d) (a := γ ^ 2 / 2)
    (q := q) (B := B) hB hI hA
  have hfinal : (B * C + 1) / 2 * Real.exp (u * (γ ^ 2 / 2 + (d - p) / 2)) +
      2 * M * Real.exp (u * (γ ^ 2 / 2 - q)) =
      ((Real.exp (γ ^ 2 * Real.log 2) - 1) * C + 1) / 2 *
        Real.exp (Real.log ε * ((d - γ ^ 2 + (2 * γ - θ) ^ 2 / 2) / 2)) +
      2 * M * Real.exp (Real.log ε * ((θ - γ) ^ 2 / 2)) := by
    dsimp [p, q, u, B]
    ring_nf
  refine hraw.trans ?_
  rw [← hfinal]
  refine le_trans ?_ halg
  dsimp only [p, q] at *
  gcongr


/-- The same-shell field increment estimate holds uniformly over submeasures
of unit Brownian occupation. -/
theorem ae_brownian_field_submeasure_radius_increment_le_rate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (x : ℂ)
    {g : ℂ → ℝ} (hg : Measurable g) {M : ℝ} (hM : 0 ≤ M)
    (hgM : ∀ z, |g z| ≤ M) (hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ 1 / 2)
    (θ d : ℝ) (hγθ : γ < θ) (hθ : θ < 2*γ)
    (hd0 : 0 < d) (hd2 : d < 2) :
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x),
        ∀ μ : Measure ℂ, μ ≤ Measure.map (fun t => b t) ν →
        ∀ ε s : ℝ, 0 < ε → ε ≤ 1/2 → 0 < s → s ≤ ε → ε / 2 ≤ s →
        (∫ ω, |∫ z, g z * (s^(γ^2/2) * Real.exp (γ*(hcirc ω s z-hcirc ω 1 0)) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0))) ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*(M^2 * unitOccupationRieszEnergy d b * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  filter_upwards [planarBrownianMotion_ae_unit_weighted_occupation_le_riesz_energy x hd0 hd2] with b hb
  intro μ hμ ε s hε hεhalf hs hsε hs2
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
  exact field_radius_increment_le_rate hh hs hsε hs2 μ hg hgi (fun z hz => by linarith [hgs z hz])
    hγθ.le hθ.le hA hI


private theorem radius_annular_weight_bound {δ γ α : ℝ} (hδ : 0 < δ) :
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




/-- Same-shell estimates have constants uniform over Brownian starting points. -/
theorem ae_brownian_stopped_annular_inserted_radius_increment_le_riesz_energy_uniform_start
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ x : ℂ,
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x),
        ∀ T : ℝ≥0, ∀ ε s : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        0 < s → s ≤ ε → ε / 2 ≤ s →
        let μ := Measure.map (fun t => b t) (ν.restrict (Iic T))
        (∫ ω, |∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          s^(γ^2/2) * Real.exp (γ*(hcirc ω s z-hcirc ω 1 0 - α*Real.log (max s ‖z‖))) -
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
  obtain ⟨M, hM, hgM⟩ := radius_annular_weight_bound (γ := γ) (α := α) hδ
  have hgs : ∀ z, g z ≠ 0 → ‖z‖ ≤ 1/2 := by
    intro z hz
    by_contra h
    have hn : z ∉ A := fun hzA => h hzA.2
    exact hz (Set.indicator_of_notMem hn _)
  obtain ⟨θ, d, hγθ, hθ, hd0, hd2, hp, _⟩ := exists_clock_truncation_exponents hγ0 hγ2
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro x
  have hb := ae_brownian_field_submeasure_radius_increment_le_rate
    hh x hgm hM hgM hgs θ d hγθ hθ hd0 hd2
  filter_upwards [hb] with b hb
  intro T ε s hε hεhalf hεδ hs hsε hs2
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ := Measure.map (fun t => b t) (ν.restrict (Iic T))
  have hμ : μ ≤ Measure.map (fun t => b t) ν :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  have hbound := hb μ hμ ε s hε hεhalf hs hsε hs2
  refine (le_of_eq ?_).trans hbound
  congr 1
  funext ω
  congr 1
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ A
  · have hδε : ε ≤ ‖z‖ := hεδ.trans hz.1
    have hhalf : s ≤ ‖z‖ := hsε.trans hδε
    rw [show A.indicator _ z = _ from Set.indicator_of_mem hz _,
      show g z = _ from Set.indicator_of_mem hz _, max_eq_right hz.1,
      max_eq_right hδε, max_eq_right hhalf]
    have heq (r : ℝ) : γ * (hcirc ω r z - hcirc ω 1 0 - α * Real.log ‖z‖) =
        -γ*α*Real.log ‖z‖ + γ*(hcirc ω r z-hcirc ω 1 0) := by ring
    rw [heq s, heq ε, Real.exp_add, Real.exp_add]
    ring
  · rw [show A.indicator _ z = _ from Set.indicator_of_notMem hz _,
      show g z = _ from Set.indicator_of_notMem hz _, zero_mul]

/-- General same-shell annular increments admit a uniform field-averaged
rate for stopped unit Brownian occupation. -/
theorem ae_brownian_stopped_annular_inserted_radius_increment_le_riesz_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂(planarBrownianMotion x),
        ∀ T : ℝ≥0, ∀ ε s : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ →
        0 < s → s ≤ ε → ε / 2 ≤ s →
        let μ := Measure.map (fun t => b t) (ν.restrict (Iic T))
        (∫ ω, |∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          s^(γ^2/2) * Real.exp (γ*(hcirc ω s z-hcirc ω 1 0 - α*Real.log (max s ‖z‖))) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*(M^2 * unitOccupationRieszEnergy d b * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, h⟩ :=
    ae_brownian_stopped_annular_inserted_radius_increment_le_riesz_energy_uniform_start
      hh hγ0 hγ2 α hδ
  exact ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, h x⟩

/-- The field-averaged same-shell increment is measurable in the path. -/
theorem measurable_stopped_annular_inserted_radius_field_expectation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε s : ℝ} (hε : 0 < ε) (hs : 0 < s)
    (γ α δ : ℝ) (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun b : ContinuousPath ℂ => ∫ ω, |∫ z,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        s^(γ^2/2) * Real.exp (γ*(hcirc ω s z-hcirc ω 1 0 - α*Real.log (max s ‖z‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z
      ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ b))))| ∂P) := by
  have := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let F : Ω × ℂ → ℝ := fun q => A.indicator (fun z =>
    s^(γ^2/2) * Real.exp (γ*(H q.1 s z-H q.1 1 0 - α*Real.log (max s ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(H q.1 ε z-H q.1 1 0 - α*Real.log (max ε ‖z‖)))) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 s q.2) :=
    (hHm s hs).comp measurable_swap
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


/-- Shifted Brownian blocks satisfy the same-shell field increment estimate. -/
theorem ae_shift_stopped_annular_inserted_radius_increment_le_riesz_energy
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (x : ℂ) (u : ℝ≥0) (τ : ContinuousPath ℂ → ℝ≥0), Measurable τ →
      ∀ ε s : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ → 0 < s → s ≤ ε → ε / 2 ≤ s →
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      ∀ᵐ b ∂planarBrownianMotion x,
        let b := ContinuousPath.shift u b
        let μ := Measure.map (fun t => b t) (ν.restrict (Iic (τ b)))
        (∫ ω, |∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          s^(γ^2/2) * Real.exp (γ*(hcirc ω s z-hcirc ω 1 0 - α*Real.log (max s ‖z‖))) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z ∂μ| ∂P) ≤
        ((Real.exp (γ^2*Real.log 2)-1)*(M^2 * unitOccupationRieszEnergy d b * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    ae_brownian_stopped_annular_inserted_radius_increment_le_riesz_energy_uniform_start
      hh hγ0 hγ2 α hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro x u τ hτ ε s hε hεhalf hεδ hs hsε hs2
  let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let F : ContinuousPath ℂ → ℝ := fun b => ∫ ω, |∫ z,
    {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
      s^(γ^2/2) * Real.exp (γ*(hcirc ω s z-hcirc ω 1 0 - α*Real.log (max s ‖z‖))) -
      ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z
      ∂(Measure.map (fun t => b t) (ν.restrict (Iic (τ b))))| ∂P
  let G : ContinuousPath ℂ → ℝ := fun b =>
    ((Real.exp (γ^2*Real.log 2)-1)*(M^2 * unitOccupationRieszEnergy d b * 2^d)+1)/2 *
      Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
      2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))
  have hF : Measurable F :=
    measurable_stopped_annular_inserted_radius_field_expectation hh hε hs γ α δ τ hτ
  have hG : Measurable G := by
    dsimp [G]
    have hE := measurable_unitOccupationRieszEnergy d
    fun_prop
  have hS : MeasurableSet {b | F b ≤ G b} := measurableSet_le hF hG
  apply ae_planarBrownianMotion_shift_of_forall_ae x u _ hS
  intro y
  filter_upwards [hb y] with b hb1
  exact hb1 (τ b) ε s hε hεhalf hεδ hs hsε hs2


/-- Field-averaged absolute same-shell increment for stopped unit occupation. -/
noncomputable def stoppedAnnularRadiusIncrement {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (hcirc : Ω → ℝ → ℂ → ℝ) (γ α δ ε s : ℝ)
    (τ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) : ℝ :=
  ∫ ω, |∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
    s^(γ^2/2) * Real.exp (γ*(hcirc ω s z-hcirc ω 1 0 - α*Real.log (max s ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z
    ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
      (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ b))))| ∂P

/-- Shifted stopped same-shell increments admit a uniform annealed rate. -/
theorem brownian_shift_stopped_annular_radius_increment_annealed_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (x : ℂ) (u : ℝ≥0) (τ : ContinuousPath ℂ → ℝ≥0), Measurable τ →
      ∀ ε s : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ → 0 < s → s ≤ ε → ε / 2 ≤ s →
        Integrable (fun b => stoppedAnnularRadiusIncrement P hcirc γ α δ ε s τ
          (ContinuousPath.shift u b)) (planarBrownianMotion x) ∧
        (∫ b, stoppedAnnularRadiusIncrement P hcirc γ α δ ε s τ (ContinuousPath.shift u b)
          ∂planarBrownianMotion x) ≤
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    ae_shift_stopped_annular_inserted_radius_increment_le_riesz_energy hh hγ0 hγ2 α hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro x u τ hτ ε s hε hεhalf hεδ hs hsε hs2
  let E : ContinuousPath ℂ → ℝ := fun b => unitOccupationRieszEnergy d (ContinuousPath.shift u b)
  let a : ℝ := Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2))
  let c : ℝ := Real.exp (Real.log ε * ((θ-γ)^2/2))
  let B : ℝ := Real.exp (γ^2*Real.log 2)-1
  let G : ContinuousPath ℂ → ℝ := fun b => ((B*(M^2 * E b * 2^d)+1)/2)*a + 2*M*c
  have hE : Integrable E (planarBrownianMotion x) :=
    (integrable_shift_unitOccupationRieszEnergy x u hd0 hd2).1
  have hG : Integrable G (planarBrownianMotion x) := by
    dsimp [G]
    fun_prop
  have hm : Measurable (fun b => stoppedAnnularRadiusIncrement P hcirc γ α δ ε s τ
      (ContinuousPath.shift u b)) :=
    (measurable_stopped_annular_inserted_radius_field_expectation hh hε hs γ α δ τ hτ).comp
      (ContinuousPath.measurable_shift_fixed u)
  have hle : ∀ᵐ b ∂planarBrownianMotion x,
      stoppedAnnularRadiusIncrement P hcirc γ α δ ε s τ (ContinuousPath.shift u b) ≤ G b :=
    hb x u τ hτ ε s hε hεhalf hεδ hs hsε hs2
  have hn : ∀ b, 0 ≤ stoppedAnnularRadiusIncrement P hcirc γ α δ ε s τ b := by
    intro b
    apply integral_nonneg
    intro ω
    exact abs_nonneg _
  have hi : Integrable (fun b => stoppedAnnularRadiusIncrement P hcirc γ α δ ε s τ
      (ContinuousPath.shift u b)) (planarBrownianMotion x) := by
    apply hG.mono' hm.aestronglyMeasurable
    filter_upwards [hle] with b hb
    simpa [Real.norm_eq_abs, abs_of_nonneg (hn _)] using hb
  refine ⟨hi, (integral_mono_ae hi hG hle).trans ?_⟩
  change (∫ b, G b ∂planarBrownianMotion x) ≤
    ((B*(M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2)*a + 2*M*c
  have hGeq : G = fun b => (B*M^2*2^d*a/2)*E b + (a/2 + 2*M*c) := by
    funext b
    dsimp [G]
    ring
  rw [hGeq, integral_add (hE.const_mul _) (integrable_const _), integral_const_mul]
  have hEx : (∫ b, E b ∂planarBrownianMotion x) =
      ∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0 :=
    (integrable_shift_unitOccupationRieszEnergy x u hd0 hd2).2.trans
      (integral_unitOccupationRieszEnergy_eq x 0 hd0 hd2)
  rw [hEx]
  simp only [integral_const, smul_eq_mul, Measure.real, measure_univ, ENNReal.toReal_one, one_mul]
  ring_nf
  exact le_rfl


private theorem radius_stopped_occupation_integral_eq_time (b : ContinuousPath ℂ) (T : ℝ≥0)
    (f : ℂ → ℝ) (hf : Measurable f) :
    (∫ z, f z ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
      (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic T)))) =
    ∫ s in (0 : ℝ)..(min (1 : ℝ≥0) T : ℝ), f (b s.toNNReal) := by
  rw [integral_map b.continuous.measurable.aemeasurable hf.aestronglyMeasurable]
  rw [Measure.restrict_map continuous_real_toNNReal.measurable measurableSet_Iic]
  rw [Measure.restrict_restrict (continuous_real_toNNReal.measurable measurableSet_Iic)]
  rw [integral_map (f := fun t : ℝ≥0 => f (b t)) continuous_real_toNNReal.measurable.aemeasurable
    (hf.comp b.continuous.measurable).aestronglyMeasurable]
  simp only [NNReal.coe_one]
  rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ min (1 : ℝ) (T : ℝ) from le_min zero_le_one T.coe_nonneg), ← integral_Icc_eq_integral_Ioc]
  congr 1
  congr 1
  ext s
  simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Icc, le_min_iff]
  constructor
  · rintro ⟨hs, h0, h1⟩
    exact ⟨h0, h1, (Real.toNNReal_le_iff_le_coe).mp hs⟩
  · rintro ⟨h0, h1, hT⟩
    exact ⟨(Real.toNNReal_le_iff_le_coe).mpr hT, h0, h1⟩

/-- Almost surely, every path has the annular inserted clock density identity
at every bounded horizon. -/
theorem ae_annular_inserted_radius_occupation_eq_time_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (γ α δ : ℝ) :
    ∀ᵐ ω ∂P, ∀ (b : ContinuousPath ℂ) (T : ℝ≥0),
      (∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z
        ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
          (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic T)))) =
      ∫ s in (0 : ℝ)..(min (1 : ℝ≥0) T : ℝ),
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
            (b s.toNNReal) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
  intro b T
  let F : ℂ → ℝ := fun z => A.indicator (fun z =>
    r^(γ^2/2) * Real.exp (γ*(H ω r z-H ω 1 0 - α*Real.log (max r ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(H ω ε z-H ω 1 0 - α*Real.log (max ε ‖z‖)))) z
  have h1 : Measurable (fun z => H ω r z) :=
    (hHm r hr).comp (measurable_id.prodMk measurable_const)
  have h2 : Measurable (fun z => H ω ε z) :=
    (hHm ε hε).comp (measurable_id.prodMk measurable_const)
  have hF : Measurable F := by
    apply Measurable.indicator _ hA
    exact (measurable_const.mul (measurable_const.mul ((h1.sub measurable_const).sub
      (measurable_const.mul ((measurable_const.max measurable_norm).log)))).exp).sub
      (measurable_const.mul (measurable_const.mul ((h2.sub measurable_const).sub
      (measurable_const.mul ((measurable_const.max measurable_norm).log)))).exp)
  have heq : F = A.indicator (fun z =>
      r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
      ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) := by
    funext z
    simp only [F, Set.indicator_apply]
    split_ifs
    · rw [hω, hω, hω, hrec r z hr, hrec ε z hε]
    · rfl
  rw [← heq]
  exact radius_stopped_occupation_integral_eq_time b T F hF




/-- The general-radius occupation increment equals its time integral. -/
theorem stoppedAnnularRadiusIncrement_eq_time_integral
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (γ α δ : ℝ)
    (τ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) :
    stoppedAnnularRadiusIncrement P hcirc γ α δ ε r τ b =
    ∫ ω, |∫ t in (0 : ℝ)..(min (1 : ℝ≥0) (τ b) : ℝ),
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
          (b t.toNNReal)| ∂P := by
  unfold stoppedAnnularRadiusIncrement
  apply integral_congr_ae
  filter_upwards [ae_annular_inserted_radius_occupation_eq_time_integral hh hε hr γ α δ,
    ae_recentered_inserted_circle_average hh α] with ω htime hrec
  have hfun : (fun z : ℂ => {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
      r^(γ^2/2) * Real.exp (γ*(hcirc ω r z-hcirc ω 1 0 - α*Real.log (max r ‖z‖))) -
      ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z) =
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) := by
    funext z
    simp only [Set.indicator_apply]
    split_ifs
    · rw [hrec r z hr, hrec ε z hε]
    · rfl
  change |∫ z, (fun z : ℂ => {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
      r^(γ^2/2) * Real.exp (γ*(hcirc ω r z-hcirc ω 1 0 - α*Real.log (max r ‖z‖))) -
      ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z) z
      ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ b))))| = _
  rw [hfun, htime b (τ b)]


/-- Shifted annular increments stopped at the actual exit satisfy a uniform annealed rate. -/
theorem brownian_shift_exit_annular_radius_increment_annealed_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (x : ℂ) (u : ℝ≥0) (ε r : ℝ), 0 < ε → ε ≤ 1/2 → ε ≤ δ → 0 < r → r ≤ ε → ε / 2 ≤ r →
        Integrable (fun b => ∫ ω, |∫ t in (0 : ℝ)..
          (min (1 : ℝ≥0) (ContinuousPath.exitTime D (ContinuousPath.shift u b)).toNNReal : ℝ),
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
            ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
              ((ContinuousPath.shift u b) t.toNNReal)| ∂P) (planarBrownianMotion x) ∧
        (∫ b, ∫ ω, |∫ t in (0 : ℝ)..
          (min (1 : ℝ≥0) (ContinuousPath.exitTime D (ContinuousPath.shift u b)).toNNReal : ℝ),
          {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
            ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
              ((ContinuousPath.shift u b) t.toNNReal)| ∂P ∂planarBrownianMotion x) ≤
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_shift_stopped_annular_radius_increment_annealed_le hh hγ0 hγ2 α hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro x u ε r hε hεhalf hεδ hr hrε hr2
  let τ : ContinuousPath ℂ → ℝ≥0 := fun b => (ContinuousPath.exitTime D b).toNNReal
  have hτ : Measurable τ := (ContinuousPath.measurable_exitTime D hD).ennreal_toNNReal
  have h := hb x u τ hτ ε r hε hεhalf hεδ hr hrε hr2
  convert h using 1 <;>
    simp only [stoppedAnnularRadiusIncrement_eq_time_integral hh hε hr γ α δ τ, τ]



/-- The field-averaged absolute annular increment on a stopped unit block. -/
noncomputable def annularExitRadiusBlockIncrement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α δ ε r : ℝ) (D : Set ℂ) (s : ℝ≥0)
    (b : ContinuousPath ℂ) : ℝ :=
  ∫ ω, |∫ t in Ioc (s : ℝ) (min ((s : ℝ) + 1) (ContinuousPath.exitTime D b).toReal),
    {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
      r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
      ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
        (b t.toNNReal)| ∂P

/-- Stopped annular block increments obey a shared annealed rate bound. -/
theorem brownian_annular_exit_radius_block_increment_annealed_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (x : ℂ) (s : ℝ≥0) (ε r : ℝ), 0 < ε → ε ≤ 1/2 → ε ≤ δ → 0 < r → r ≤ ε → ε / 2 ≤ r →
        Integrable (annularExitRadiusBlockIncrement P hcirc γ α δ ε r D s) (planarBrownianMotion x) ∧
        (∫ b, annularExitRadiusBlockIncrement P hcirc γ α δ ε r D s b ∂planarBrownianMotion x) ≤
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2)) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_shift_stopped_annular_radius_increment_annealed_le hh hγ0 hγ2 α hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro x s ε r hε hεhalf hεδ hr hrε hr2
  let τ : ContinuousPath ℂ → ℝ≥0 := fun b => (ContinuousPath.exitTime D b).toNNReal
  have hτ : Measurable τ := (ContinuousPath.measurable_exitTime D hD).ennreal_toNNReal
  let F : ContinuousPath ℂ → ℝ := fun b =>
    stoppedAnnularRadiusIncrement P hcirc γ α δ ε r τ (ContinuousPath.shift s b)
  let S : Set (ContinuousPath ℂ) := {b | (s : ℝ≥0∞) < ContinuousPath.exitTime D b}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (ContinuousPath.measurable_exitTime D hD)
  have hF := hb x s τ hτ ε r hε hεhalf hεδ hr hrε hr2
  have heq : annularExitRadiusBlockIncrement P hcirc γ α δ ε r D s =ᵐ[planarBrownianMotion x] S.indicator F := by
    filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hDb] with b hfin
    by_cases hs : (s : ℝ≥0∞) < ContinuousPath.exitTime D b
    · rw [Set.indicator_of_mem (show b ∈ S from hs)]
      rw [show F b = _ from stoppedAnnularRadiusIncrement_eq_time_integral hh hε hr γ α δ τ _]
      apply integral_congr_ae
      filter_upwards with ω
      congr 1
      exact setIntegral_exit_stopped_block_eq D b s hfin.ne _ |>.trans (ite_eq_left hs)
    · rw [Set.indicator_of_notMem (show b ∉ S from hs)]
      dsimp [annularExitRadiusBlockIncrement]
      apply integral_eq_zero_of_ae
      filter_upwards with ω
      rw [setIntegral_exit_stopped_block_eq D b s hfin.ne _, ite_eq_right hs, abs_zero]
      rfl
  have hi := (hF.1.indicator hS).congr heq.symm
  refine ⟨hi, (integral_mono_ae hi hF.1 ?_).trans hF.2⟩
  filter_upwards [heq] with b heq
  rw [heq]
  by_cases hs : b ∈ S
  · rw [Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem hs]
    apply integral_nonneg
    intro ω
    exact abs_nonneg _




/-- At every positive smoothing radius, the annular clock is nondecreasing
and its increments are integrals of the nonnegative density. -/
theorem ae_stoppedAnnularClock_radius_monotone_and_cell
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α δ : ℝ) :
    ∀ᵐ ω ∂P, ∀ (r : ℝ), 0 < r → ∀ (b : ContinuousPath ℂ),
      let f : ℂ → ℝ := fun z => r^(γ^2/2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)
      MonotoneOn (fun t : ℝ => stoppedAnnularClock f δ (fun _ => t.toNNReal) b) (Icc 0 1) ∧
      ∀ {u v : ℝ}, 0 ≤ u → u ≤ v → v ≤ 1 →
        ENNReal.ofReal (stoppedAnnularClock f δ (fun _ => v.toNNReal) b -
          stoppedAnnularClock f δ (fun _ => u.toNNReal) b) =
        ∫⁻ s in Ioc u v, ENNReal.ofReal
          ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
  intro r hr b
  let f : ℂ → ℝ := fun z => r^(γ^2/2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)
  have hc : Continuous (hcirc ω r) := by
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hf : Continuous f := continuous_inserted_density_at_radius (hcirc ω) γ α r hr hc
    (fun z => hrec r z hr)
  have hf0 : ∀ z, 0 ≤ f z := by
    intro z
    dsimp [f]
    exact mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le
  refine ⟨monotoneOn_stoppedAnnularClock f hf hf0 δ b, ?_⟩
  intro u v hu huv hv
  exact (stoppedAnnularClock_sub_nonneg_and_ofReal_eq_lintegral f hf hf0 δ b hu huv hv).2

/-- A fixed-time annular clock is measurable under the field-path product
law at any positive smoothing radius. -/
theorem aemeasurable_stoppedAnnularClock_radius
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (ν : Measure (ContinuousPath ℂ)) [SFinite ν]
    {r : ℝ} (hr : 0 < r) (γ α δ : ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    AEMeasurable (fun p : Ω × ContinuousPath ℂ =>
      stoppedAnnularClock (fun z => r^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) δ
        (fun _ => t.toNNReal) p.2) (P.prod ν) := by
  let F : Ω × ContinuousPath ℂ → ℝ≥0∞ := fun p =>
    ∫⁻ s in Ioc (0 : ℝ) t, ENNReal.ofReal
      ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        r^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) (p.2 s.toNNReal))
  have hF : AEMeasurable F (P.prod ν) :=
    aemeasurable_annular_inserted_clock_cell hh ν hr γ α δ 0 t
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  apply hF.ennreal_toReal.congr
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae
    (ae_stoppedAnnularClock_radius_monotone_and_cell hh γ α δ),
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae hHae,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae
      (ae_recentered_inserted_circle_average hh α)] with p hp hω hrec
  let f : ℂ → ℝ := fun z => r^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)
  have hc : Continuous (hcirc p.1 r) := by
    rw [← funext (hω r)]
    exact hHc p.1 r hr
  have hf : Continuous f := continuous_inserted_density_at_radius (hcirc p.1) γ α r hr hc
    (fun z => hrec r z hr)
  have hz : stoppedAnnularClock f δ (fun _ => (0 : ℝ).toNNReal) p.2 = 0 := by
    rw [stoppedAnnularClock_eq_time_integral f hf.measurable]
    simp
  have hnonneg : 0 ≤ stoppedAnnularClock f δ (fun _ => t.toNNReal) p.2 := by
    have h := (hp r hr p.2).1 (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      ⟨ht0, ht1⟩ ht0
    change stoppedAnnularClock f δ (fun _ => (0 : ℝ).toNNReal) p.2 ≤
      stoppedAnnularClock f δ (fun _ => t.toNNReal) p.2 at h
    simpa only [hz] using h
  have heq := (hp r hr p.2).2 (u := 0) (v := t) le_rfl ht0 ht1
  change ENNReal.ofReal (stoppedAnnularClock f δ (fun _ => t.toNNReal) p.2 -
    stoppedAnnularClock f δ (fun _ => (0 : ℝ).toNNReal) p.2) = F p at heq
  rw [hz, sub_zero] at heq
  change (F p).toReal = stoppedAnnularClock f δ (fun _ => t.toNNReal) p.2
  rw [← heq, ENNReal.toReal_ofReal hnonneg]

/-- A fixed-time annular clock remains measurable at all nonnegative times. -/
theorem aemeasurable_stoppedAnnularClock_radius_of_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (ν : Measure (ContinuousPath ℂ)) [SFinite ν]
    {r : ℝ} (hr : 0 < r) (γ α δ : ℝ) {t : ℝ} (ht0 : 0 ≤ t) :
    AEMeasurable (fun p : Ω × ContinuousPath ℂ =>
      stoppedAnnularClock (fun z => r^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) δ
        (fun _ => t.toNNReal) p.2) (P.prod ν) := by
  by_cases ht1 : t ≤ 1
  · exact aemeasurable_stoppedAnnularClock_radius hh ν hr γ α δ ht0 ht1
  · have h1 := aemeasurable_stoppedAnnularClock_radius hh ν hr γ α δ
      (t := 1) (by norm_num) le_rfl
    obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
    apply h1.congr
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae hHae,
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := ν)).ae
        (ae_recentered_inserted_circle_average hh α)] with p hω hrec
    let f : ℂ → ℝ := fun z => r^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)
    have hc : Continuous (hcirc p.1 r) := by
      rw [← funext (hω r)]
      exact hHc p.1 r hr
    have hf : Continuous f := continuous_inserted_density_at_radius (hcirc p.1) γ α r hr hc
      (fun z => hrec r z hr)
    change stoppedAnnularClock f δ (fun _ => (1 : ℝ).toNNReal) p.2 =
      stoppedAnnularClock f δ (fun _ => t.toNNReal) p.2
    rw [stoppedAnnularClock_eq_time_integral f hf.measurable,
      stoppedAnnularClock_eq_time_integral f hf.measurable]
    simp only [NNReal.coe_one, Real.coe_toNNReal', max_eq_left ht0]
    rw [min_eq_left (le_of_lt (lt_of_not_ge ht1))]
    norm_num

/-- The time supremum of a same-shell clock difference is controlled by
its time-grid values and the largest cell mass at the upper radius. -/
theorem lintegral_prod_stoppedAnnularClock_radius_iSup_le_grid_and_mesh
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) (γ α δ : ℝ)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (m : ℕ) (hm : 0 < m) :
    let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
      stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
        (fun _ => t.toNNReal) p.2
    (∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F r p t - F ε p t|
      ∂(P.prod (planarBrownianMotion x))) ≤
      (∑ j ∈ Finset.range (m + 1), ∫⁻ p, ENNReal.ofReal
        |F r p (j / (m : ℝ)) - F ε p (j / (m : ℝ))|
        ∂(P.prod (planarBrownianMotion x))) +
      ∫⁻ p : Ω × ContinuousPath ℂ, (⨆ j : Fin m,
        ∫⁻ t in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m),
          ENNReal.ofReal ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z))
                (p.2 t.toNNReal))) ∂(P.prod (planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  dsimp only
  let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
    stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
        (fun _ => t.toNNReal) p.2
  have hmono : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)),
      MonotoneOn (F r p) (Icc 0 1) ∧ MonotoneOn (F ε p) (Icc 0 1) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_stoppedAnnularClock_radius_monotone_and_cell hh γ α δ)] with p hp
    exact ⟨(hp r hr p.2).1, (hp ε hε p.2).1⟩
  have hgrid (j : ℕ) : AEMeasurable (fun p => |F r p (j / (m : ℝ)) -
      F ε p (j / (m : ℝ))|) (P.prod (planarBrownianMotion x)) := by
    exact ((aemeasurable_stoppedAnnularClock_radius_of_nonneg hh (planarBrownianMotion x)
      hr γ α δ (by positivity)).sub
      (aemeasurable_stoppedAnnularClock_radius_of_nonneg hh (planarBrownianMotion x)
        hε γ α δ (by positivity))).abs
  have hcell : (fun p : Ω × ContinuousPath ℂ => ⨆ j : Fin m,
      ENNReal.ofReal (F ε p (((j : ℝ) + 1) / m) - F ε p ((j : ℝ) / m))) =ᵐ[
        P.prod (planarBrownianMotion x)] (fun p => ⨆ j : Fin m,
      ∫⁻ t in Ioc ((j : ℝ) / m) (((j : ℝ) + 1) / m), ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z))
              (p.2 t.toNNReal))) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_stoppedAnnularClock_radius_monotone_and_cell hh γ α δ)] with p hp
    apply iSup_congr
    intro j
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast j.isLt
    exact (hp ε hε p.2).2 (by positivity)
      (div_le_div_of_nonneg_right (by linarith) hm0.le) ((div_le_one hm0).2 hjm)
  have h := lintegral_iSup_abs_sub_le_grid_and_mesh (P.prod (planarBrownianMotion x))
    (F r) (F ε) hm hmono hgrid
  rw [lintegral_congr_ae hcell] at h
  exact h

/-- Below the second-moment threshold, the expected time supremum of an
annular clock difference is controlled by its grid values and a mesh power. -/
theorem exists_lintegral_prod_stoppedAnnularClock_radius_iSup_le_grid
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ^2 < 2) (α δ : ℝ) :
    ∃ (C : ℝ≥0∞) (β : ℝ), C < ∞ ∧ 0 < β ∧
      ∀ {r ε : ℝ}, 0 < r → 0 < ε → ε ≤ δ → ∀ (m : ℕ), 0 < m →
      let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
        stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
          (fun _ => t.toNNReal) p.2
      (∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F r p t - F ε p t|
        ∂(P.prod (planarBrownianMotion x))) ≤
        (∑ j ∈ Finset.range (m + 1), ∫⁻ p, ENNReal.ofReal
          |F r p (j / (m : ℝ)) - F ε p (j / (m : ℝ))|
          ∂(P.prod (planarBrownianMotion x))) + C * (m : ℝ≥0∞)^(-β) := by
  obtain ⟨C, β, hC, hβ, hmesh⟩ :=
    exists_lintegral_prod_annular_mesh_max_le hh x hγ hγ2 α δ
  refine ⟨C, β, hC, hβ, ?_⟩
  intro r ε hr hε hεδ m hm
  exact (lintegral_prod_stoppedAnnularClock_radius_iSup_le_grid_and_mesh
    hh x γ α δ hr hε m hm).trans (add_le_add le_rfl (hmesh hε hεδ m hm))

/-- A stopped annular increment at two positive radii is field-integrable. -/
theorem integrable_stopped_annular_radius_increment_field
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε r δ : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hrε : r ≤ ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (γ α : ℝ) (τ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) :
    Integrable (fun ω => ∫ z,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        r^(γ^2/2) * Real.exp (γ*(hcirc ω r z-hcirc ω 1 0 - α*Real.log (max r ‖z‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z
      ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ b))))) P := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let g : ℂ → ℝ := A.indicator (fun z => Real.exp (-γ*α*Real.log (max δ ‖z‖)))
  have hδ : 0 < δ := hε.trans_le hεδ
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let f : ℂ → ℝ := fun z => Real.exp (-γ*α*Real.log (max δ ‖z‖))
  have hf : Continuous f := Real.continuous_exp.comp (continuous_const.mul
    ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hδ).ne')))
  have hgm : Measurable g := hf.measurable.indicator hA
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.continuousOn
  have hgK : ∀ z, |g z| ≤ max K 0 := by
    intro z
    by_cases hz : z ∈ A
    · have hzk : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
      rw [show g z = f z from Set.indicator_of_mem hz _, abs_of_pos (Real.exp_pos _)]
      exact (hK ⟨z, hzk, rfl⟩).trans (le_max_left K 0)
    · rw [show g z = 0 from Set.indicator_of_notMem hz _, abs_zero]
      exact le_max_right K 0
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ : Measure ℂ := Measure.map (fun t => b t) (ν.restrict (Iic (τ b)))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  have hμ : μ ≤ Measure.map (fun t => b t) ν :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le (Measure.map (fun t => b t) ν) hμ
  have hgi : Integrable g μ := by
    apply (integrable_const (max K 0)).mono' hgm.aestronglyMeasurable
    filter_upwards with z
    simpa [Real.norm_eq_abs] using hgK z
  have hgs : ∀ z, g z ≠ 0 → ‖z‖ + ε ≤ 1 := by
    intro z hz
    have hzA : z ∈ A := by
      by_contra hn
      exact hz (Set.indicator_of_notMem hn _)
    linarith [hzA.2]
  have hgsr : ∀ z, g z ≠ 0 → ‖z‖ + r ≤ 1 := by
    intro z hz
    linarith [hgs z hz]
  have hi := hh.integrable_integral_increment_scales hr hε zero_lt_one μ hgm hgi hgsr hgs γ
  refine hi.congr (Filter.Eventually.of_forall fun ω => ?_)
  apply integral_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ A
  · have hδε : ε ≤ ‖z‖ := hεδ.trans hz.1
    have hhalf : r ≤ ‖z‖ := by linarith
    rw [show A.indicator _ z = _ from Set.indicator_of_mem hz _,
      show g z = _ from Set.indicator_of_mem hz _, max_eq_right hz.1,
      max_eq_right hδε, max_eq_right hhalf]
    have heq (r : ℝ) : γ * (hcirc ω r z - hcirc ω 1 0 - α * Real.log ‖z‖) =
        -γ*α*Real.log ‖z‖ + γ*(hcirc ω r z-hcirc ω 1 0) := by ring
    rw [heq r, heq ε, Real.exp_add, Real.exp_add]
    ring
  · rw [show A.indicator _ z = _ from Set.indicator_of_notMem hz _,
      show g z = _ from Set.indicator_of_notMem hz _, zero_mul]


/-- A same-shell annular increment on an exit-stopped block is integrable
with respect to the field law. -/
theorem integrable_annular_exit_radius_block_increment_field
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε r δ : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hrε : r ≤ ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (γ α : ℝ) (D : Set ℂ) (s : ℝ≥0) (b : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime D b ≠ ⊤) :
    Integrable (fun ω => ∫ t in Ioc (s : ℝ)
      (min ((s : ℝ) + 1) (ContinuousPath.exitTime D b).toReal),
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
            (b t.toNNReal)) P := by
  by_cases hs : (s : ℝ≥0∞) < ContinuousPath.exitTime D b
  · let τ : ContinuousPath ℂ → ℝ≥0 := fun p => (ContinuousPath.exitTime D p).toNNReal
    let q := ContinuousPath.shift s b
    have hi := integrable_stopped_annular_radius_increment_field hh hε hr hrε hεhalf hεδ γ α τ q
    apply hi.congr
    filter_upwards [ae_annular_inserted_radius_occupation_eq_time_integral hh hε hr γ α δ,
      ae_recentered_inserted_circle_average hh α] with ω htime hrec
    have hraw : (∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        r^(γ^2/2) * Real.exp (γ*(hcirc ω r z-hcirc ω 1 0 - α*Real.log (max r ‖z‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z
      ∂(Measure.map (fun t => q t) ((Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ q))))) =
      ∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) z
      ∂(Measure.map (fun t => q t) ((Measure.map Real.toNNReal
        (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ q)))) := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [Set.indicator_apply]
      split_ifs
      · rw [hrec r z hr, hrec ε z hε]
      · rfl
    rw [hraw, htime q (τ q)]
    exact (setIntegral_exit_stopped_block_eq D b s hfin _).trans (ite_eq_left hs) |>.symm
  · have hz : (fun ω => ∫ t in Ioc (s : ℝ)
        (min ((s : ℝ) + 1) (ContinuousPath.exitTime D b).toReal),
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
            (b t.toNNReal)) = 0 := by
      funext ω
      rw [setIntegral_exit_stopped_block_eq D b s hfin _, ite_eq_right hs]
      rfl
    rw [hz]
    exact integrable_zero _ _ _

/-- The field-averaged annular increment up to a stopped integer horizon. -/
noncomputable def annularExitRadiusHorizonIncrement {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α δ ε r : ℝ) (D : Set ℂ) (N : ℕ)
    (b : ContinuousPath ℂ) : ℝ :=
  ∫ ω, |∫ t in (0 : ℝ)..min (N : ℝ) (ContinuousPath.exitTime D b).toReal,
    {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
      r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
      ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
        (b t.toNNReal)| ∂P

/-- The field-averaged stopped increment is bounded by its unit-block increments. -/
theorem annular_exit_radius_horizon_increment_le_sum_blocks {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε r δ : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hrε : r ≤ ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (γ α : ℝ) (D : Set ℂ) (N : ℕ) (b : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime D b ≠ ⊤) :
    annularExitRadiusHorizonIncrement P hcirc γ α δ ε r D N b ≤
      ∑ k ∈ Finset.range N, annularExitRadiusBlockIncrement P hcirc γ α δ ε r D k b := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let G : Ω → ℂ → ℝ := fun ω z =>
    r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
    ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)
  let F : Ω → ℝ := fun ω => ∫ t in (0 : ℝ)..min (N : ℝ) (ContinuousPath.exitTime D b).toReal,
    A.indicator (G ω) (b t.toNNReal)
  let B : ℕ → Ω → ℝ := fun k ω => ∫ t in Ioc (k : ℝ)
      (min ((k : ℝ) + 1) (ContinuousPath.exitTime D b).toReal), A.indicator (G ω) (b t.toNNReal)
  have hB : ∀ k, Integrable (B k) P := by
    intro k
    exact integrable_annular_exit_radius_block_increment_field hh hε hr hrε hεhalf hεδ γ α D k b hfin
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hsum : F =ᵐ[P] fun ω => ∑ k ∈ Finset.range N, B k ω := by
    filter_upwards [hcont, ae_recentered_inserted_circle_average hh α] with ω hcont hrec
    have hc (r : ℝ) (hr : 0 < r) : Continuous (fun z =>
        r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)) := by
      have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) =
          fun z => hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) := by
        funext z
        exact (hrec r z hr).symm
      have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
        rw [heq]
        exact ((hcont r hr).sub continuous_const).sub (continuous_const.mul
          ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
      exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))
    have hG : Continuous (G ω) := (hc r hr).sub (hc ε hε)
    have hint := intervalIntegrable_annular_density (G ω) hG δ b 0
      (ContinuousPath.exitTime D b).toReal
    exact intervalIntegral_stopped_eq_sum_blocks _ _ ENNReal.toReal_nonneg N hint
  have hsumint : Integrable (fun ω => ∑ k ∈ Finset.range N, B k ω) P := by
    exact integrable_finsetSum _ (fun k hk => hB k)
  have hF : Integrable F P := hsumint.congr hsum.symm
  have hsumabs : Integrable (fun ω => ∑ k ∈ Finset.range N, |B k ω|) P := by
    exact integrable_finsetSum _ (fun k hk => (hB k).abs)
  change (∫ ω, |F ω| ∂P) ≤ ∑ k ∈ Finset.range N, ∫ ω, |B k ω| ∂P
  calc
    _ ≤ ∫ ω, ∑ k ∈ Finset.range N, |B k ω| ∂P := by
      apply integral_mono_ae hF.abs hsumabs
      filter_upwards [hsum] with ω hω
      rw [hω]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = _ := integral_finsetSum _ (fun k hk => (hB k).abs)

/-- The stopped annular increment has a jointly measurable field-path version. -/
theorem exists_measurable_annular_exit_radius_horizon_sample {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (γ α δ : ℝ) {D : Set ℂ} (hD : IsOpen D) (N : ℕ) :
    ∃ F : ContinuousPath ℂ × Ω → ℝ, Measurable F ∧ ∀ᵐ ω ∂P, ∀ b,
      F (b,ω) = ∫ t in (0 : ℝ)..min (N : ℝ) (ContinuousPath.exitTime D b).toReal,
        {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
          ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
            (b t.toNNReal) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let J : Ω × ℂ → ℝ := fun q => A.indicator (fun z =>
    r^(γ^2/2) * Real.exp (γ*(H q.1 r z-H q.1 1 0 - α*Real.log (max r ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(H q.1 ε z-H q.1 1 0 - α*Real.log (max ε ‖z‖)))) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 r q.2) :=
    (hHm r hr).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) := (hHm ε hε).comp measurable_swap
  have h3 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hJ : Measurable J := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).sub
      (measurable_const.mul (measurable_const.mul ((h2.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp)
  let U : ContinuousPath ℂ → ℝ := fun b => min (N : ℝ) (ContinuousPath.exitTime D b).toReal
  have hU : Measurable U := measurable_const.min ((ContinuousPath.measurable_exitTime D hD).ennreal_toReal)
  have heval : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ => q.1.1 q.2.toNNReal) := by
    exact (ContinuousEval.continuous_eval.comp continuous_swap).measurable.comp
      ((measurable_real_toNNReal.comp measurable_snd).prodMk (measurable_fst.comp measurable_fst))
  let S : Set ((ContinuousPath ℂ × Ω) × ℝ) := {q | 0 < q.2 ∧ q.2 ≤ U q.1.1}
  have hS : MeasurableSet S := (measurableSet_lt measurable_const measurable_snd).inter
    (measurableSet_le measurable_snd (hU.comp (measurable_fst.comp measurable_fst)))
  let Q : (ContinuousPath ℂ × Ω) × ℝ → ℝ := fun q =>
    S.indicator (fun q => J (q.1.2, q.1.1 q.2.toNNReal)) q
  have hQ : Measurable Q := by
    exact (hJ.comp ((measurable_snd.comp measurable_fst).prodMk heval)).indicator hS
  refine ⟨fun q => ∫ t, Q (q,t), hQ.stronglyMeasurable.integral_prod_right'.measurable, ?_⟩
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec b
  have hU0 : 0 ≤ U b := le_min (Nat.cast_nonneg N) ENNReal.toReal_nonneg
  rw [intervalIntegral.integral_of_le hU0, ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards with t
  simp only [Q, S, U, Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_Ioc, J, A]
  split_ifs with ht hz
  · rw [hω r (b t.toNNReal), hω ε (b t.toNNReal), hω 1 0,
      hrec r (b t.toNNReal) hr, hrec ε (b t.toNNReal) hε]
  · rfl
  · rfl

/-- The field-averaged stopped annular horizon increment is measurable. -/
theorem measurable_annular_exit_radius_horizon_increment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (γ α δ : ℝ) {D : Set ℂ} (hD : IsOpen D) (N : ℕ) :
    Measurable (annularExitRadiusHorizonIncrement P hcirc γ α δ ε r D N) := by
  have := hh.isProbabilityMeasure
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_annular_exit_radius_horizon_sample hh hε hr γ α δ hD N
  have hm : Measurable (fun b => ∫ ω, |F (b,ω)| ∂P) :=
    (hFm.abs.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  convert hm using 1
  funext b
  unfold annularExitRadiusHorizonIncrement
  apply integral_congr_ae
  filter_upwards [hFae] with ω hω
  rw [hω b]

/-- Finite-horizon annular increments satisfy a linear-in-horizon rate bound. -/
theorem brownian_annular_exit_radius_horizon_increment_annealed_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (x : ℂ) (N : ℕ) (ε r : ℝ), 0 < ε → ε ≤ 1/2 → ε ≤ δ → 0 < r → r ≤ ε → ε / 2 ≤ r →
        Integrable (annularExitRadiusHorizonIncrement P hcirc γ α δ ε r D N) (planarBrownianMotion x) ∧
        (∫ b, annularExitRadiusHorizonIncrement P hcirc γ α δ ε r D N b ∂planarBrownianMotion x) ≤
        (N : ℝ) * (((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_annular_exit_radius_block_increment_annealed_le hh hγ0 hγ2 α hδ hD hDb
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro x N ε r hε hεhalf hεδ hr hrε hr2
  let F := annularExitRadiusHorizonIncrement P hcirc γ α δ ε r D N
  let B : ℕ → ContinuousPath ℂ → ℝ := fun k => annularExitRadiusBlockIncrement P hcirc γ α δ ε r D k
  have hB : ∀ k, Integrable (B k) (planarBrownianMotion x) := fun k =>
    (hb x k ε r hε hεhalf hεδ hr hrε hr2).1
  have hS : Integrable (fun b => ∑ k ∈ Finset.range N, B k b) (planarBrownianMotion x) :=
    integrable_finsetSum _ (fun k hk => hB k)
  have hm : Measurable F := measurable_annular_exit_radius_horizon_increment hh hε hr γ α δ hD N
  have hF0 : ∀ b, 0 ≤ F b := by
    intro b
    apply integral_nonneg
    intro ω
    exact abs_nonneg _
  have hle : ∀ᵐ b ∂planarBrownianMotion x, F b ≤ ∑ k ∈ Finset.range N, B k b := by
    filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hDb] with b hfin
    exact annular_exit_radius_horizon_increment_le_sum_blocks hh hε hr hrε hεhalf hεδ γ α D N b hfin.ne
  have hi : Integrable F (planarBrownianMotion x) := by
    apply hS.mono' hm.aestronglyMeasurable
    filter_upwards [hle] with b h
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hF0 b)] using h
  refine ⟨hi, (integral_mono_ae hi hS hle).trans ?_⟩
  rw [integral_finsetSum _ (fun k hk => hB k)]
  calc
    _ ≤ ∑ k ∈ Finset.range N, (((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) := by
      apply Finset.sum_le_sum
      intro k hk
      exact (hb x k ε r hε hεhalf hεδ hr hrε hr2).2
    _ = _ := by simp [mul_add]

private theorem summable_nat_mul_exp_log_dyadicScale_radius {c : ℝ} (hc : 0 < c) :
    Summable (fun k : ℕ => (k : ℝ) * Real.exp (Real.log (dyadicScale k) * c)) := by
  change Summable (fun k : ℕ => (k : ℝ) * Real.exp (Real.log (LatticeProb.LQG.dyadicScale k) * c))
  simp_rw [LatticeProb.Gauss.exp_log_dyadicScale_mul]
  have hq : ‖Real.exp (Real.log 2⁻¹ * c)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (Real.exp_lt_exp.mpr (mul_neg_of_neg_of_pos (Real.log_neg (by norm_num) (by norm_num)) hc)).trans_eq Real.exp_zero
  simpa only [pow_one] using (summable_pow_mul_geometric_of_norm_lt_one 1 hq)

/-- Annealed annular horizon increments are summable for any choice of same-shell radii. -/
theorem summable_brownian_annular_exit_radius_horizon_increment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) (r : ℕ → ℝ)
    (hr0 : ∀ k, 0 < r k) (hr1 : ∀ k, r k ≤ dyadicScale k)
    (hr2 : ∀ k, dyadicScale k / 2 ≤ r k) :
    Summable (fun k : ℕ => ∫ b, annularExitRadiusHorizonIncrement P hcirc γ α δ
      (dyadicScale k) (r k) D k b ∂planarBrownianMotion x) := by
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_annular_exit_radius_horizon_increment_annealed_le hh hγ0 hγ2 α hδ hD hDb
  let A : ℝ := ((Real.exp (γ^2*Real.log 2)-1) *
    (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2
  let c : ℝ := (d-γ^2+(2*γ-θ)^2/2)/2
  let e : ℝ := (θ-γ)^2/2
  have hc : 0 < c := by dsimp [c]; positivity
  have he : 0 < e := by dsimp [e]; positivity
  have hsum : Summable (fun k : ℕ => (k : ℝ) *
      (A * Real.exp (Real.log (dyadicScale k) * c) +
      2*M*Real.exp (Real.log (dyadicScale k) * e))) := by
    have h1 := (summable_nat_mul_exp_log_dyadicScale_radius hc).mul_left A
    have h2 := (summable_nat_mul_exp_log_dyadicScale_radius he).mul_left (2*M)
    apply (h1.add h2).congr
    intro k
    ring
  have hlim : Tendsto dyadicScale atTop (𝓝 0) := by
    unfold dyadicScale
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hev : ∀ᶠ k in atTop, dyadicScale k < min (1/2) δ :=
    hlim.eventually (Iio_mem_nhds (lt_min (by norm_num) hδ))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  apply (summable_nat_add_iff N).1
  apply Summable.of_nonneg_of_le
    (fun k => integral_nonneg (fun b => integral_nonneg (fun ω => abs_nonneg _)))
    _ ((summable_nat_add_iff N).2 hsum)
  intro k
  have hk := hN (k + N) (by omega)
  exact (hb x (k+N) _ (r (k+N)) (dyadicScale_pos _)
    (le_of_lt (lt_of_lt_of_le hk (min_le_left _ _)))
    (le_of_lt (lt_of_lt_of_le hk (min_le_right _ _)))
    (hr0 _) (hr1 _) (hr2 _)).2

/-- A stopped finite-horizon annular increment is integrable over the field. -/
theorem integrable_annular_exit_radius_horizon_sample_field {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε r δ : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hrε : r ≤ ε) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (γ α : ℝ) (D : Set ℂ) (N : ℕ) (b : ContinuousPath ℂ)
    (hfin : ContinuousPath.exitTime D b ≠ ⊤) :
    Integrable (fun ω => ∫ t in (0 : ℝ)..min (N : ℝ) (ContinuousPath.exitTime D b).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))
          (b t.toNNReal)) P := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let G : Ω → ℂ → ℝ := fun ω z =>
    r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) -
    ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)
  let F : Ω → ℝ := fun ω => ∫ t in (0 : ℝ)..min (N : ℝ) (ContinuousPath.exitTime D b).toReal,
    A.indicator (G ω) (b t.toNNReal)
  let B : ℕ → Ω → ℝ := fun k ω => ∫ t in Ioc (k : ℝ)
      (min ((k : ℝ) + 1) (ContinuousPath.exitTime D b).toReal), A.indicator (G ω) (b t.toNNReal)
  have hB : ∀ k, Integrable (B k) P := by
    intro k
    exact integrable_annular_exit_radius_block_increment_field hh hε hr hrε hεhalf hεδ γ α D k b hfin
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hcont : ∀ᵐ ω ∂P, ∀ r, 0 < r → Continuous (hcirc ω r) := by
    filter_upwards [hHae] with ω hω r hr
    rw [← funext (hω r)]
    exact hHc ω r hr
  have hsum : F =ᵐ[P] fun ω => ∑ k ∈ Finset.range N, B k ω := by
    filter_upwards [hcont, ae_recentered_inserted_circle_average hh α] with ω hcont hrec
    have hc (r : ℝ) (hr : 0 < r) : Continuous (fun z =>
        r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)) := by
      have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) =
          fun z => hcirc ω r z - hcirc ω 1 0 - α * Real.log (max r ‖z‖) := by
        funext z
        exact (hrec r z hr).symm
      have hc' : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z) := by
        rw [heq]
        exact ((hcont r hr).sub continuous_const).sub (continuous_const.mul
          ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hr).ne')))
      exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc'))
    have hG : Continuous (G ω) := (hc r hr).sub (hc ε hε)
    have hint := intervalIntegrable_annular_density (G ω) hG δ b 0
      (ContinuousPath.exitTime D b).toReal
    exact intervalIntegral_stopped_eq_sum_blocks _ _ ENNReal.toReal_nonneg N hint
  have hsumint : Integrable (fun ω => ∑ k ∈ Finset.range N, B k ω) P := by
    exact integrable_finsetSum _ (fun k hk => hB k)
  have hF : Integrable F P := hsumint.congr hsum.symm
  exact hF


/-- The product-law expectation of a stopped same-shell horizon increment
agrees with its iterated field and Brownian expectation. -/
theorem lintegral_prod_annular_exit_radius_horizon_increment_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hrε : r ≤ ε) (hr2 : ε / 2 ≤ r)
    (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    {D : Set ℂ} (hD : IsOpen D) (hDb : Bornology.IsBounded D) (N : ℕ) :
    (∫⁻ p : Ω × ContinuousPath ℂ, ENNReal.ofReal |∫ t in (0 : ℝ)..
      min (N : ℝ) (ContinuousPath.exitTime D p.2).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z))
          (p.2 t.toNNReal)| ∂(P.prod (planarBrownianMotion x))) =
    ENNReal.ofReal (∫ b, annularExitRadiusHorizonIncrement P hcirc γ α δ ε r D N b
      ∂planarBrownianMotion x) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨F, hFm, hFae⟩ :=
    exists_measurable_annular_exit_radius_horizon_sample hh hε hr γ α δ hD N
  have heq : (fun p : Ω × ContinuousPath ℂ => ENNReal.ofReal |∫ t in (0 : ℝ)..
      min (N : ℝ) (ContinuousPath.exitTime D p.2).toReal,
      {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        r^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z) -
        ε^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z))
          (p.2 t.toNNReal)|) =ᵐ[P.prod (planarBrownianMotion x)]
      (fun p => ENNReal.ofReal |F (p.2,p.1)|) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae hFae] with p hp
    rw [hp p.2]
  rw [lintegral_congr_ae heq]
  have hmeas : Measurable (fun p : Ω × ContinuousPath ℂ => ENNReal.ofReal |F (p.2,p.1)|) :=
    ENNReal.measurable_ofReal.comp ((hFm.comp measurable_swap).abs)
  rw [lintegral_prod_symm _ hmeas.aemeasurable]
  obtain ⟨θ, d, M, h1, h2, h3, h4, h5, h6, hb⟩ :=
    brownian_annular_exit_radius_horizon_increment_annealed_le hh hγ0 hγ2 α
      (hε.trans_le hεδ) hD hDb
  rw [ofReal_integral_eq_lintegral_ofReal (hb x N ε r hε hεhalf hεδ hr hrε hr2).1]
  · apply lintegral_congr_ae
    filter_upwards [ae_planarBrownian_exitTime_bounded_lt_top x hDb] with b hfin
    have hi := integrable_annular_exit_radius_horizon_sample_field hh hε hr hrε hεhalf hεδ γ α D N b hfin.ne
    have hFi : Integrable (fun ω => F (b,ω)) P := hi.congr (by
      filter_upwards [hFae] with ω hω
      exact (hω b).symm)
    rw [show annularExitRadiusHorizonIncrement P hcirc γ α δ ε r D N b =
        ∫ ω, ‖F (b,ω)‖ ∂P from by
      unfold annularExitRadiusHorizonIncrement
      apply integral_congr_ae
      filter_upwards [hFae] with ω hω
      rw [hω b, Real.norm_eq_abs]]
    simp_rw [← Real.enorm_eq_ofReal_abs]
    exact (ofReal_integral_norm_eq_lintegral_enorm hFi).symm
  · filter_upwards with b
    apply integral_nonneg
    intro ω
    exact abs_nonneg _

/-- An annular increment before averaging over the field. -/
noncomputable def annularRadiusIncrementSample {Ω : Type*} [MeasurableSpace Ω]
    (hcirc : Ω → ℝ → ℂ → ℝ) (γ α δ ε r : ℝ)
    (τ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ) (ω : Ω) : ℝ :=
  ∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
    r^(γ^2/2) * Real.exp (γ*(hcirc ω r z-hcirc ω 1 0 - α*Real.log (max r ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε z-hcirc ω 1 0 - α*Real.log (max ε ‖z‖)))) z
    ∂(Measure.map (fun t => b t) ((Measure.map Real.toNNReal
      (volume.restrict (Icc (0 : ℝ) 1))).restrict (Iic (τ b))))

/-- The annular increment admits a jointly measurable modification. -/
theorem exists_measurable_annularRadiusIncrementSample
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (γ α δ : ℝ) (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    ∃ F : ContinuousPath ℂ × Ω → ℝ, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ b, F (b, ω) = annularRadiusIncrementSample hcirc γ α δ ε r τ b ω := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  let G : Ω × ℂ → ℝ := fun q => A.indicator (fun z =>
    r^(γ^2/2) * Real.exp (γ*(H q.1 r z-H q.1 1 0 - α*Real.log (max r ‖z‖))) -
    ε^(γ^2/2) * Real.exp (γ*(H q.1 ε z-H q.1 1 0 - α*Real.log (max ε ‖z‖)))) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 r q.2) :=
    (hHm r hr).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) :=
    (hHm ε hε).comp measurable_swap
  have h3 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hG : Measurable G := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).sub
      (measurable_const.mul (measurable_const.mul ((h2.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp)
  refine ⟨_, measurable_stopped_path_integral G hG τ hτ, ?_⟩
  filter_upwards [hHae] with ω hω b
  apply integral_congr_ae
  filter_upwards with z
  simp only [G, A, hω]

/-- The joint nonnegative integral of the annular increment is the annealed
expectation of its field-averaged absolute value. -/
theorem lintegral_prod_annularRadiusIncrementSample_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hrε : r ≤ ε) (hr2 : ε / 2 ≤ r) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    (∫⁻ p : Ω × ContinuousPath ℂ,
      ENNReal.ofReal |annularRadiusIncrementSample hcirc γ α δ ε r τ p.2 p.1|
      ∂(P.prod (planarBrownianMotion x))) =
      ENNReal.ofReal (∫ b, stoppedAnnularRadiusIncrement P hcirc γ α δ ε r τ b
        ∂(planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨F, hFm, hFae⟩ :=
    exists_measurable_annularRadiusIncrementSample hh hε hr γ α δ τ hτ
  have heq : (fun p : Ω × ContinuousPath ℂ =>
      ENNReal.ofReal |annularRadiusIncrementSample hcirc γ α δ ε r τ p.2 p.1|) =ᵐ[
        P.prod (planarBrownianMotion x)]
      (fun p => ENNReal.ofReal |F (p.2,p.1)|) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae hFae] with p hp
    rw [hp p.2]
  rw [lintegral_congr_ae heq]
  have hmeas : Measurable (fun p : Ω × ContinuousPath ℂ => ENNReal.ofReal |F (p.2,p.1)|) :=
    ENNReal.measurable_ofReal.comp ((hFm.comp measurable_swap).abs)
  rw [lintegral_prod_symm _ hmeas.aemeasurable]
  have hfield (b : ContinuousPath ℂ) : Integrable (fun ω => F (b, ω)) P := by
    apply (integrable_stopped_annular_radius_increment_field hh hε hr hrε hεhalf hεδ γ α τ b).congr
    filter_upwards [hFae] with ω hω
    exact (hω b).symm
  have hinner (b : ContinuousPath ℂ) :
      (∫⁻ ω, ENNReal.ofReal |F (b,ω)| ∂P) =
        ENNReal.ofReal (stoppedAnnularRadiusIncrement P hcirc γ α δ ε r τ b) := by
    simp_rw [← Real.norm_eq_abs]
    rw [← ofReal_integral_eq_lintegral_ofReal (hfield b).norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))]
    congr 1
    unfold stoppedAnnularRadiusIncrement
    apply integral_congr_ae
    filter_upwards [hFae] with ω hω
    rw [hω b]
    rfl
  simp_rw [hinner]
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_shift_stopped_annular_radius_increment_annealed_le hh hγ0 hγ2 α
      (hε.trans_le hεδ)
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · simpa only [ContinuousPath.shift_zero] using
      (hb x 0 τ hτ ε r hε hεhalf hεδ hr hrε hr2).1
  · exact Filter.Eventually.of_forall (fun b => integral_nonneg (fun ω => abs_nonneg _))

private theorem radius_integrable_annular_density (f : ℂ → ℝ) (hf : Continuous f) (δ : ℝ)
    (μ : Measure ℂ) [IsFiniteMeasure μ] :
    Integrable ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f) μ := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.norm.continuousOn
  apply (integrable_const (max K 0)).mono' (hf.measurable.indicator hA).aestronglyMeasurable
  filter_upwards with z
  by_cases hz : z ∈ A
  · have hzk : z ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hz.2
    rw [show A.indicator f z = f z from Set.indicator_of_mem hz _]
    exact (hK ⟨z, hzk, rfl⟩).trans (le_max_left K 0)
  · rw [show A.indicator f z = 0 from Set.indicator_of_notMem hz _, norm_zero]
    exact le_max_right K 0


/-- For almost every field, the difference of two positive-radius annular
clocks is their occupation increment at every path and horizon. -/
theorem ae_stoppedAnnularClock_sub_eq_annularRadiusIncrementSample
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α δ : ℝ) :
    ∀ᵐ ω ∂P, ∀ (ε r : ℝ), 0 < ε → 0 < r →
      ∀ (τ : ContinuousPath ℂ → ℝ≥0) (b : ContinuousPath ℂ),
      stoppedAnnularClock (fun z => r^(γ^2/2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) r z)) δ τ b -
      stoppedAnnularClock (fun z => ε^(γ^2/2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) δ τ b =
      annularRadiusIncrementSample hcirc γ α δ ε r τ b ω := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
  intro ε r hε hr τ b
  have hcont (v : ℝ) (hv : 0 < v) : Continuous (hcirc ω v) := by
    rw [← funext (hω v)]
    exact hHc ω v hv
  let D : ℝ → ℂ → ℝ := fun v z => v^(γ^2/2) *
    Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) v z)
  have hD (v : ℝ) (hv : 0 < v) : Continuous (D v) :=
    continuous_inserted_density_at_radius (hcirc ω) γ α v hv (hcont v hv)
      (fun z => hrec v z hv)
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  let μ : Measure ℂ := Measure.map (fun t => b t) (ν.restrict (Iic (τ b)))
  have hν : ν univ = 1 := by
    simp [ν, Measure.map_apply continuous_real_toNNReal.measurable]
  let : IsProbabilityMeasure ν := ⟨hν⟩
  have hμ : μ ≤ Measure.map (fun t => b t) ν :=
    Measure.map_mono Measure.restrict_le_self b.continuous.measurable
  let : IsFiniteMeasure μ := isFiniteMeasure_of_le (Measure.map (fun t => b t) ν) hμ
  change (∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (D r) z ∂μ) -
    (∫ z, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (D ε) z ∂μ) = _
  rw [← integral_sub (radius_integrable_annular_density _ (hD r hr) δ μ)
    (radius_integrable_annular_density _ (hD ε hε) δ μ)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [Set.indicator_apply]
  split_ifs
  · dsimp [D, annularRadiusIncrementSample]
    rw [← hrec r z hr, ← hrec ε z hε]
  · ring


/-- Same-shell annular clock differences satisfy a product-law rate bound
uniformly over measurable unit horizons. -/
theorem lintegral_prod_stoppedAnnularClock_radius_sub_le_uniform_horizon
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (τ : ContinuousPath ℂ → ℝ≥0), Measurable τ →
      ∀ ε r : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ → 0 < r → r ≤ ε → ε / 2 ≤ r →
        (∫⁻ p : Ω × ContinuousPath ℂ, ENNReal.ofReal |stoppedAnnularClock
          (fun z => r^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) δ τ p.2 -
          stoppedAnnularClock (fun z => ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) δ τ p.2|
          ∂(P.prod (planarBrownianMotion x))) ≤ ENNReal.ofReal (
          ((Real.exp (γ^2*Real.log 2)-1) *
            (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
            Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
          2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_shift_stopped_annular_radius_increment_annealed_le hh hγ0 hγ2 α hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro τ hτ ε r hε hεhalf hεδ hr hrε hr2
  have heq : (fun p : Ω × ContinuousPath ℂ => ENNReal.ofReal |stoppedAnnularClock
      (fun z => r^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) δ τ p.2 -
      stoppedAnnularClock (fun z => ε^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) δ τ p.2|) =ᵐ[
        P.prod (planarBrownianMotion x)]
      (fun p => ENNReal.ofReal |annularRadiusIncrementSample hcirc γ α δ ε r τ p.2 p.1|) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_stoppedAnnularClock_sub_eq_annularRadiusIncrementSample hh γ α δ)] with p hp
    rw [hp ε r hε hr τ p.2]
  rw [lintegral_congr_ae heq,
    lintegral_prod_annularRadiusIncrementSample_eq hh hγ0 hγ2 α x hε hr hrε hr2 hεhalf hεδ τ hτ]
  apply ENNReal.ofReal_le_ofReal
  simpa only [ContinuousPath.shift_zero] using
    (hb x 0 τ hτ ε r hε hεhalf hεδ hr hrε hr2).2

/-- Below the second-moment threshold, the product expectation of the
unit-time same-shell clock supremum has a time-mesh bound. -/
theorem exists_lintegral_prod_stoppedAnnularClock_radius_iSup_le_rate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (θ d M β : ℝ) (C : ℝ≥0∞), γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧ 0 < β ∧ C < ∞ ∧
      ∀ {r ε : ℝ}, 0 < r → 0 < ε → ε ≤ 1/2 → ε ≤ δ → r ≤ ε → ε / 2 ≤ r →
      ∀ (m : ℕ), 0 < m →
      let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
        stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
          (fun _ => t.toNNReal) p.2
      (∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F r p t - F ε p t|
        ∂(P.prod (planarBrownianMotion x))) ≤
      (m + 1 : ℝ≥0∞) * ENNReal.ofReal (
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) + C * (m : ℝ≥0∞)^(-β) := by
  have hγlt : γ < 2 := by nlinarith [sq_nonneg (γ - 1)]
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    lintegral_prod_stoppedAnnularClock_radius_sub_le_uniform_horizon hh hγ0 hγlt α x hδ
  obtain ⟨C, β, hC, hβ, hmesh⟩ :=
    exists_lintegral_prod_stoppedAnnularClock_radius_iSup_le_grid hh x (ne_of_gt hγ0) hγ2 α δ
  refine ⟨θ, d, M, β, C, hγθ, hθ, hd0, hd2, hp, hM, hβ, hC, ?_⟩
  intro r ε hr hε hεhalf hεδ hrε hr2 m hm
  dsimp only
  refine (hmesh hr hε hεδ m hm).trans (add_le_add ?_ le_rfl)
  calc
    _ ≤ ∑ _j ∈ Finset.range (m + 1), ENNReal.ofReal (
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hb (fun _ => ((j : ℝ) / m).toNNReal) measurable_const ε r
        hε hεhalf hεδ hr hrε hr2
    _ = _ := by simp

/-- Stopping both clocks at the same time can only reduce the supremum over
a unit interval. -/
theorem lintegral_prod_stoppedAnnularClock_radius_exit_iSup_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} (x : ℂ) (γ α δ r ε : ℝ) (D : Set ℂ) :
    let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
      stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
          (fun _ => t.toNNReal) p.2
    let G : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
      stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
          (fun b => min t.toNNReal (ContinuousPath.exitTime D b).toNNReal) p.2
    (∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |G r p t - G ε p t|
      ∂(P.prod (planarBrownianMotion x))) ≤
    ∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F r p t - F ε p t|
      ∂(P.prod (planarBrownianMotion x)) := by
  dsimp only
  apply lintegral_mono
  intro p
  apply iSup_le
  intro t
  let u : ℝ≥0 := min t.val.toNNReal (ContinuousPath.exitTime D p.2).toNNReal
  have hu : (u : ℝ) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨u.coe_nonneg, ?_⟩
    have h : u ≤ t.val.toNNReal := min_le_left _ _
    have h' : (u : ℝ) ≤ t.val := by
      simpa [Real.coe_toNNReal', max_eq_left t.property.1] using (NNReal.coe_le_coe.mpr h)
    exact h'.trans t.property.2
  have h := le_iSup (fun s : Icc (0 : ℝ) 1 => ENNReal.ofReal |stoppedAnnularClock
    (fun z => r^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) δ
        (fun _ => s.val.toNNReal) p.2 -
    stoppedAnnularClock (fun z => ε^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) δ
        (fun _ => s.val.toNNReal) p.2|) ⟨u, hu⟩
  simp only [Real.toNNReal_coe, u, stoppedAnnularClock] at h ⊢
  exact h

/-- The joint nonnegative integral of the annular increment is the annealed
expectation of its field-averaged absolute value. -/
theorem lintegral_prod_shift_annularRadiusIncrementSample_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) (u : ℝ≥0) {δ ε r : ℝ}
    (hε : 0 < ε) (hr : 0 < r) (hrε : r ≤ ε) (hr2 : ε / 2 ≤ r) (hεhalf : ε ≤ 1/2) (hεδ : ε ≤ δ)
    (τ : ContinuousPath ℂ → ℝ≥0) (hτ : Measurable τ) :
    (∫⁻ p : Ω × ContinuousPath ℂ,
      ENNReal.ofReal |annularRadiusIncrementSample hcirc γ α δ ε r τ (ContinuousPath.shift u p.2) p.1|
      ∂(P.prod (planarBrownianMotion x))) =
      ENNReal.ofReal (∫ b, stoppedAnnularRadiusIncrement P hcirc γ α δ ε r τ (ContinuousPath.shift u b)
        ∂(planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨F, hFm, hFae⟩ :=
    exists_measurable_annularRadiusIncrementSample hh hε hr γ α δ τ hτ
  have heq : (fun p : Ω × ContinuousPath ℂ =>
      ENNReal.ofReal |annularRadiusIncrementSample hcirc γ α δ ε r τ (ContinuousPath.shift u p.2) p.1|) =ᵐ[
        P.prod (planarBrownianMotion x)]
      (fun p => ENNReal.ofReal |F (ContinuousPath.shift u p.2,p.1)|) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae hFae] with p hp
    rw [hp (ContinuousPath.shift u p.2)]
  rw [lintegral_congr_ae heq]
  have hmeas : Measurable (fun p : Ω × ContinuousPath ℂ => ENNReal.ofReal |F (ContinuousPath.shift u p.2,p.1)|) :=
    ENNReal.measurable_ofReal.comp ((hFm.comp
      (((ContinuousPath.measurable_shift_fixed u).comp measurable_snd).prodMk measurable_fst)).abs)
  rw [lintegral_prod_symm _ hmeas.aemeasurable]
  have hfield (b : ContinuousPath ℂ) : Integrable (fun ω => F (ContinuousPath.shift u b, ω)) P := by
    apply (integrable_stopped_annular_radius_increment_field hh hε hr hrε hεhalf hεδ γ α τ (ContinuousPath.shift u b)).congr
    filter_upwards [hFae] with ω hω
    exact (hω (ContinuousPath.shift u b)).symm
  have hinner (b : ContinuousPath ℂ) :
      (∫⁻ ω, ENNReal.ofReal |F (ContinuousPath.shift u b,ω)| ∂P) =
        ENNReal.ofReal (stoppedAnnularRadiusIncrement P hcirc γ α δ ε r τ (ContinuousPath.shift u b)) := by
    simp_rw [← Real.norm_eq_abs]
    rw [← ofReal_integral_eq_lintegral_ofReal (hfield b).norm
      (Filter.Eventually.of_forall (fun _ => norm_nonneg _))]
    congr 1
    unfold stoppedAnnularRadiusIncrement
    apply integral_congr_ae
    filter_upwards [hFae] with ω hω
    rw [hω (ContinuousPath.shift u b)]
    rfl
  simp_rw [hinner]
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_shift_stopped_annular_radius_increment_annealed_le hh hγ0 hγ2 α
      (hε.trans_le hεδ)
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · exact (hb x u τ hτ ε r hε hεhalf hεδ hr hrε hr2).1
  · exact Filter.Eventually.of_forall (fun b => integral_nonneg (fun ω => abs_nonneg _))

/-- Same-shell annular clock differences satisfy a product-law rate bound
uniformly over measurable unit horizons. -/
theorem lintegral_prod_shift_stoppedAnnularClock_radius_sub_le_uniform_horizon
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) (u : ℝ≥0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (τ : ContinuousPath ℂ → ℝ≥0), Measurable τ →
      ∀ ε r : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ → 0 < r → r ≤ ε → ε / 2 ≤ r →
        (∫⁻ p : Ω × ContinuousPath ℂ, ENNReal.ofReal |stoppedAnnularClock
          (fun z => r^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) δ τ (ContinuousPath.shift u p.2) -
          stoppedAnnularClock (fun z => ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) δ τ (ContinuousPath.shift u p.2)|
          ∂(P.prod (planarBrownianMotion x))) ≤ ENNReal.ofReal (
          ((Real.exp (γ^2*Real.log 2)-1) *
            (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
            Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
          2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_shift_stopped_annular_radius_increment_annealed_le hh hγ0 hγ2 α hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro τ hτ ε r hε hεhalf hεδ hr hrε hr2
  have heq : (fun p : Ω × ContinuousPath ℂ => ENNReal.ofReal |stoppedAnnularClock
      (fun z => r^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) δ τ (ContinuousPath.shift u p.2) -
      stoppedAnnularClock (fun z => ε^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) δ τ (ContinuousPath.shift u p.2)|) =ᵐ[
        P.prod (planarBrownianMotion x)]
      (fun p => ENNReal.ofReal |annularRadiusIncrementSample hcirc γ α δ ε r τ (ContinuousPath.shift u p.2) p.1|) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_stoppedAnnularClock_sub_eq_annularRadiusIncrementSample hh γ α δ)] with p hp
    rw [hp ε r hε hr τ (ContinuousPath.shift u p.2)]
  rw [lintegral_congr_ae heq,
    lintegral_prod_shift_annularRadiusIncrementSample_eq hh hγ0 hγ2 α x u hε hr hrε hr2 hεhalf hεδ τ hτ]
  apply ENNReal.ofReal_le_ofReal
  exact (hb x u τ hτ ε r hε hεhalf hεδ hr hrε hr2).2

/-- Annular mesh-cell maxima have a uniform power bound on every interval
of unit length beginning at a nonnegative time. -/
theorem exists_lintegral_prod_annular_shifted_mesh_max_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ : γ ≠ 0) (hγ2 : γ ^ 2 < 2) (α δ : ℝ) :
    ∃ (C : ℝ≥0∞) (β : ℝ), C < ∞ ∧ 0 < β ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ δ →
      ∀ (u : ℝ), 0 ≤ u → ∀ (m : ℕ), 0 < m →
      (∫⁻ p : Ω × ContinuousPath ℂ, (⨆ j : Fin m,
        ∫⁻ s in Ioc (u + (j : ℝ) / m) (u + ((j : ℝ) + 1) / m),
          ENNReal.ofReal ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal)))
          ∂(P.prod (planarBrownianMotion x))) ≤ C * (m : ℝ≥0∞) ^ (-β) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨C, hC, hbound⟩ :=
    exists_lintegral_prod_brownian_annular_inserted_cell_sq_le hh x hγ hγ2 α δ
  let β : ℝ := (1 - γ ^ 2 / 2) / 2
  have hβ : 0 < β := by dsimp [β]; linarith
  refine ⟨C ^ (1 / 2 : ℝ), β, ENNReal.rpow_lt_top_of_nonneg (by norm_num) hC.ne, hβ, ?_⟩
  intro ε hε hεδ u hu m hm
  let X : Fin m → Ω × ContinuousPath ℂ → ℝ≥0∞ := fun j p =>
    ∫⁻ s in Ioc (u + (j : ℝ) / m) (u + ((j : ℝ) + 1) / m),
      ENNReal.ofReal ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1 / 2}.indicator (fun z =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) (p.2 s.toNNReal))
  have hX (j : Fin m) : AEMeasurable (X j) (P.prod (planarBrownianMotion x)) :=
    aemeasurable_annular_inserted_clock_cell hh (planarBrownianMotion x) hε γ α δ
      (u + (j : ℝ) / m) (u + ((j : ℝ) + 1) / m)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hrpow : (ENNReal.ofReal (1 / (m : ℝ))) ^ (2 - γ ^ 2 / 2) =
      (m : ℝ≥0∞) ^ (-(1 + 2 * β)) := by
    rw [one_div, ENNReal.ofReal_inv_of_pos hm0, ENNReal.ofReal_natCast,
      ENNReal.inv_rpow, ← ENNReal.rpow_neg]
    congr 1
    dsimp [β]
    ring
  have hcell (j : Fin m) :
      (∫⁻ p, (X j p) ^ (2 : ℝ) ∂(P.prod (planarBrownianMotion x))) ≤
        C * (m : ℝ≥0∞) ^ (-(1 + 2 * β)) := by
    have hend : (u + (j : ℝ) / m) + 1 / (m : ℝ) = u + ((j : ℝ) + 1) / m := by ring
    have hmain := hbound hε hεδ (u + (j : ℝ) / m) (1 / (m : ℝ))
      (by positivity) (one_div_pos.mpr hm0)
    rw [hend, hrpow] at hmain
    simpa only [ENNReal.rpow_ofNat, X] using hmain
  exact lintegral_iSup_le_mesh_rpow_of_aemeasurable (P.prod (planarBrownianMotion x)) hm X hX
    (by norm_num : (1 : ℝ) ≤ 2) C hcell

/-- A cell of a shifted annular clock is the corresponding cell on the
original path. -/
theorem stoppedAnnularClock_shift_sub_ofReal_eq_lintegral
    (f : ℂ → ℝ) (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (δ : ℝ)
    (b : ContinuousPath ℂ) (u : ℝ≥0) {a c : ℝ} (ha : 0 ≤ a) (hac : a ≤ c) (hc : c ≤ 1) :
    ENNReal.ofReal (stoppedAnnularClock f δ (fun _ => c.toNNReal) (ContinuousPath.shift u b) -
      stoppedAnnularClock f δ (fun _ => a.toNNReal) (ContinuousPath.shift u b)) =
    ∫⁻ s in Ioc ((u : ℝ) + a) ((u : ℝ) + c), ENNReal.ofReal
      ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b s.toNNReal)) := by
  let g : ℝ → ℝ := fun t =>
    {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f (b t.toNNReal)
  let q : ℝ → ℝ := fun t =>
    {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator f ((ContinuousPath.shift u b) t.toNNReal)
  have hq0 (t : ℝ) : 0 ≤ q t := by
    simp only [q, Set.indicator_apply]
    split_ifs <;> simp_all
  have hg0 (t : ℝ) : 0 ≤ g t := by
    simp only [g, Set.indicator_apply]
    split_ifs <;> simp_all
  have hqint : IntervalIntegrable q volume a c :=
    intervalIntegrable_annular_density f hf δ (ContinuousPath.shift u b) a c
  have hgint : IntervalIntegrable g volume ((u : ℝ) + a) ((u : ℝ) + c) :=
    intervalIntegrable_annular_density f hf δ b _ _
  rw [(stoppedAnnularClock_sub_nonneg_and_ofReal_eq_lintegral f hf hf0 δ
    (ContinuousPath.shift u b) ha hac hc).2]
  change (∫⁻ t in Ioc a c, ENNReal.ofReal (q t)) =
    ∫⁻ t in Ioc ((u : ℝ) + a) ((u : ℝ) + c), ENNReal.ofReal (g t)
  rw [← ofReal_integral_eq_lintegral_ofReal hqint.1 (Filter.Eventually.of_forall hq0),
    ← ofReal_integral_eq_lintegral_ofReal hgint.1 (Filter.Eventually.of_forall hg0)]
  congr 1
  rw [← intervalIntegral.integral_of_le hac,
    ← intervalIntegral.integral_of_le (show (u : ℝ) + a ≤ (u : ℝ) + c by linarith)]
  calc
    (∫ t in a..c, q t) = ∫ t in a..c, g ((u : ℝ) + t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [uIcc_of_le hac] at ht
      simp only [q, g, ContinuousPath.shift_apply,
        Real.toNNReal_add u.coe_nonneg (ha.trans ht.1), Real.toNNReal_coe]
    _ = _ := intervalIntegral.integral_comp_add_left g (u : ℝ)

/-- A shifted annular clock difference is controlled by its grid values and
by the maximum original-path mesh-cell mass. -/
theorem lintegral_prod_shift_stoppedAnnularClock_radius_iSup_le_grid_and_mesh
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) (u : ℝ≥0) (γ α δ : ℝ)
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) (m : ℕ) (hm : 0 < m) :
    let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
      stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
        (fun _ => t.toNNReal) (ContinuousPath.shift u p.2)
    (∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F r p t - F ε p t|
      ∂(P.prod (planarBrownianMotion x))) ≤
      (∑ j ∈ Finset.range (m + 1), ∫⁻ p, ENNReal.ofReal
        |F r p (j / (m : ℝ)) - F ε p (j / (m : ℝ))|
        ∂(P.prod (planarBrownianMotion x))) +
      ∫⁻ p : Ω × ContinuousPath ℂ, (⨆ j : Fin m,
        ∫⁻ t in Ioc ((u : ℝ) + (j : ℝ) / m) ((u : ℝ) + ((j : ℝ) + 1) / m),
          ENNReal.ofReal ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
            ε^(γ^2/2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z))
                (p.2 t.toNNReal))) ∂(P.prod (planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  dsimp only
  let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
    stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
        (fun _ => t.toNNReal) (ContinuousPath.shift u p.2)
  have hmono : ∀ᵐ p ∂(P.prod (planarBrownianMotion x)),
      MonotoneOn (F r p) (Icc 0 1) ∧ MonotoneOn (F ε p) (Icc 0 1) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_stoppedAnnularClock_radius_monotone_and_cell hh γ α δ)] with p hp
    exact ⟨(hp r hr (ContinuousPath.shift u p.2)).1, (hp ε hε (ContinuousPath.shift u p.2)).1⟩
  have hgrid (j : ℕ) : AEMeasurable (fun p => |F r p (j / (m : ℝ)) -
      F ε p (j / (m : ℝ))|) (P.prod (planarBrownianMotion x)) := by
    let τ : ContinuousPath ℂ → ℝ≥0 := fun _ => ((j : ℝ) / m).toNNReal
    obtain ⟨G, hGm, hGae⟩ := exists_measurable_annularRadiusIncrementSample hh hε hr γ α δ τ measurable_const
    have hmG : Measurable (fun p : Ω × ContinuousPath ℂ => |G (ContinuousPath.shift u p.2, p.1)|) :=
      (hGm.comp (((ContinuousPath.measurable_shift_fixed u).comp measurable_snd).prodMk measurable_fst)).abs
    apply hmG.aemeasurable.congr
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hGae,
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_stoppedAnnularClock_sub_eq_annularRadiusIncrementSample hh γ α δ)] with p hp hsub
    change |G (ContinuousPath.shift u p.2, p.1)| =
      |stoppedAnnularClock _ δ τ (ContinuousPath.shift u p.2) -
       stoppedAnnularClock _ δ τ (ContinuousPath.shift u p.2)|
    rw [hp, hsub ε r hε hr τ (ContinuousPath.shift u p.2)]
  have hcell : (fun p : Ω × ContinuousPath ℂ => ⨆ j : Fin m,
      ENNReal.ofReal (F ε p (((j : ℝ) + 1) / m) - F ε p ((j : ℝ) / m))) =ᵐ[
        P.prod (planarBrownianMotion x)] (fun p => ⨆ j : Fin m,
      ∫⁻ t in Ioc ((u : ℝ) + (j : ℝ) / m) ((u : ℝ) + ((j : ℝ) + 1) / m), ENNReal.ofReal
        ({z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z))
              (p.2 t.toNNReal))) := by
    obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hHae,
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_recentered_inserted_circle_average hh α)] with p hp hrec
    let f : ℂ → ℝ := fun z => ε^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)
    have hc : Continuous (hcirc p.1 ε) := by
      rw [← funext (hp ε)]
      exact hHc p.1 ε hε
    have hf : Continuous f := continuous_inserted_density_at_radius (hcirc p.1) γ α ε hε hc
      (fun z => hrec ε z hε)
    have hf0 (z : ℂ) : 0 ≤ f z := mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
    apply iSup_congr
    intro j
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hjm : (j : ℝ) + 1 ≤ m := by exact_mod_cast j.isLt
    exact stoppedAnnularClock_shift_sub_ofReal_eq_lintegral f hf hf0 δ p.2 u
      (by positivity) (div_le_div_of_nonneg_right (by linarith) hm0.le) ((div_le_one hm0).2 hjm)
  have h := lintegral_iSup_abs_sub_le_grid_and_mesh (P.prod (planarBrownianMotion x))
    (F r) (F ε) hm hmono hgrid
  rw [lintegral_congr_ae hcell] at h
  exact h

/-- Same-shell annular clock differences satisfy a product-law rate bound
uniformly over deterministic shifts and measurable unit horizons. -/
theorem lintegral_prod_shift_stoppedAnnularClock_radius_sub_le_uniform_shift_horizon
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (α : ℝ) (x : ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ d M : ℝ, γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧
      ∀ (u : ℝ≥0) (τ : ContinuousPath ℂ → ℝ≥0), Measurable τ →
      ∀ ε r : ℝ, 0 < ε → ε ≤ 1/2 → ε ≤ δ → 0 < r → r ≤ ε → ε / 2 ≤ r →
        (∫⁻ p : Ω × ContinuousPath ℂ, ENNReal.ofReal |stoppedAnnularClock
          (fun z => r^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) δ τ (ContinuousPath.shift u p.2) -
          stoppedAnnularClock (fun z => ε^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) δ τ (ContinuousPath.shift u p.2)|
          ∂(P.prod (planarBrownianMotion x))) ≤ ENNReal.ofReal (
          ((Real.exp (γ^2*Real.log 2)-1) *
            (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
            Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
          2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    brownian_shift_stopped_annular_radius_increment_annealed_le hh hγ0 hγ2 α hδ
  refine ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, ?_⟩
  intro u τ hτ ε r hε hεhalf hεδ hr hrε hr2
  have heq : (fun p : Ω × ContinuousPath ℂ => ENNReal.ofReal |stoppedAnnularClock
      (fun z => r^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) δ τ (ContinuousPath.shift u p.2) -
      stoppedAnnularClock (fun z => ε^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) δ τ (ContinuousPath.shift u p.2)|) =ᵐ[
        P.prod (planarBrownianMotion x)]
      (fun p => ENNReal.ofReal |annularRadiusIncrementSample hcirc γ α δ ε r τ (ContinuousPath.shift u p.2) p.1|) := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst
      (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_stoppedAnnularClock_sub_eq_annularRadiusIncrementSample hh γ α δ)] with p hp
    rw [hp ε r hε hr τ (ContinuousPath.shift u p.2)]
  rw [lintegral_congr_ae heq,
    lintegral_prod_shift_annularRadiusIncrementSample_eq hh hγ0 hγ2 α x u hε hr hrε hr2 hεhalf hεδ τ hτ]
  apply ENNReal.ofReal_le_ofReal
  exact (hb x u τ hτ ε r hε hεhalf hεδ hr hrε hr2).2

/-- The expected same-shell clock supremum on a deterministic shifted unit
interval has a time-mesh bound uniform in the shift. -/
theorem exists_lintegral_prod_shift_stoppedAnnularClock_radius_iSup_le_uniform_shift_rate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (θ d M β : ℝ) (C : ℝ≥0∞), γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧ 0 < β ∧ C < ∞ ∧
      ∀ (u : ℝ≥0) {r ε : ℝ}, 0 < r → 0 < ε → ε ≤ 1/2 → ε ≤ δ → r ≤ ε → ε / 2 ≤ r →
      ∀ (m : ℕ), 0 < m →
      let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
        stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
          (fun _ => t.toNNReal) (ContinuousPath.shift u p.2)
      (∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F r p t - F ε p t|
        ∂(P.prod (planarBrownianMotion x))) ≤
      (m + 1 : ℝ≥0∞) * ENNReal.ofReal (
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) + C * (m : ℝ≥0∞)^(-β) := by
  have hγlt : γ < 2 := by nlinarith [sq_nonneg (γ - 1)]
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    lintegral_prod_shift_stoppedAnnularClock_radius_sub_le_uniform_shift_horizon hh hγ0 hγlt α x hδ
  obtain ⟨C, β, hC, hβ, hmesh⟩ :=
    exists_lintegral_prod_annular_shifted_mesh_max_le hh x (ne_of_gt hγ0) hγ2 α δ
  refine ⟨θ, d, M, β, C, hγθ, hθ, hd0, hd2, hp, hM, hβ, hC, ?_⟩
  intro u r ε hr hε hεhalf hεδ hrε hr2 m hm
  dsimp only
  refine (lintegral_prod_shift_stoppedAnnularClock_radius_iSup_le_grid_and_mesh
    hh x u γ α δ hr hε m hm).trans ?_
  refine (add_le_add le_rfl (hmesh hε hεδ u u.coe_nonneg m hm)).trans (add_le_add ?_ le_rfl)
  calc
    _ ≤ ∑ _j ∈ Finset.range (m + 1), ENNReal.ofReal (
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hb u (fun _ => ((j : ℝ) / m).toNNReal) measurable_const ε r
        hε hεhalf hεδ hr hrε hr2
    _ = _ := by simp

/-- The expected same-shell clock supremum on a deterministic shifted unit
interval has a time-mesh bound. -/
theorem exists_lintegral_prod_shift_stoppedAnnularClock_radius_iSup_le_rate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) (u : ℝ≥0)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (θ d M β : ℝ) (C : ℝ≥0∞), γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧ 0 < β ∧ C < ∞ ∧
      ∀ {r ε : ℝ}, 0 < r → 0 < ε → ε ≤ 1/2 → ε ≤ δ → r ≤ ε → ε / 2 ≤ r →
      ∀ (m : ℕ), 0 < m →
      let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
        stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
          (fun _ => t.toNNReal) (ContinuousPath.shift u p.2)
      (∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F r p t - F ε p t|
        ∂(P.prod (planarBrownianMotion x))) ≤
      (m + 1 : ℝ≥0∞) * ENNReal.ofReal (
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) + C * (m : ℝ≥0∞)^(-β) := by
  have hγlt : γ < 2 := by nlinarith [sq_nonneg (γ - 1)]
  obtain ⟨θ, d, M, hγθ, hθ, hd0, hd2, hp, hM, hb⟩ :=
    lintegral_prod_shift_stoppedAnnularClock_radius_sub_le_uniform_horizon hh hγ0 hγlt α x u hδ
  obtain ⟨C, β, hC, hβ, hmesh⟩ :=
    exists_lintegral_prod_annular_shifted_mesh_max_le hh x (ne_of_gt hγ0) hγ2 α δ
  refine ⟨θ, d, M, β, C, hγθ, hθ, hd0, hd2, hp, hM, hβ, hC, ?_⟩
  intro r ε hr hε hεhalf hεδ hrε hr2 m hm
  dsimp only
  refine (lintegral_prod_shift_stoppedAnnularClock_radius_iSup_le_grid_and_mesh
    hh x u γ α δ hr hε m hm).trans ?_
  refine (add_le_add le_rfl (hmesh hε hεδ u u.coe_nonneg m hm)).trans (add_le_add ?_ le_rfl)
  calc
    _ ≤ ∑ _j ∈ Finset.range (m + 1), ENNReal.ofReal (
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) := by
      apply Finset.sum_le_sum
      intro j hj
      exact hb (fun _ => ((j : ℝ) / m).toNNReal) measurable_const ε r
        hε hεhalf hεδ hr hrε hr2
    _ = _ := by simp

/-- Stopping both shifted clocks at a common path-dependent time does not
increase their unit-time supremum difference. -/
theorem lintegral_prod_shift_stoppedAnnularClock_radius_iSup_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} (x : ℂ) (u : ℝ≥0) (γ α δ r ε : ℝ)
    (τ : ContinuousPath ℂ → ℝ≥0) :
    let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
      stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
          (fun _ => t.toNNReal) (ContinuousPath.shift u p.2)
    let G : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
      stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
          (fun _ => min t.toNNReal (τ p.2)) (ContinuousPath.shift u p.2)
    (∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |G r p t - G ε p t|
      ∂(P.prod (planarBrownianMotion x))) ≤
    ∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F r p t - F ε p t|
      ∂(P.prod (planarBrownianMotion x)) := by
  dsimp only
  apply lintegral_mono
  intro p
  apply iSup_le
  intro t
  let s : ℝ≥0 := min t.val.toNNReal (τ p.2)
  have hs : (s : ℝ) ∈ Icc (0 : ℝ) 1 := by
    refine ⟨s.coe_nonneg, ?_⟩
    have h : s ≤ t.val.toNNReal := min_le_left _ _
    have h' : (s : ℝ) ≤ t.val := by
      simpa [Real.coe_toNNReal', max_eq_left t.property.1] using (NNReal.coe_le_coe.mpr h)
    exact h'.trans t.property.2
  have h := le_iSup (fun v : Icc (0 : ℝ) 1 => ENNReal.ofReal |stoppedAnnularClock
    (fun z => r^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) r z)) δ
        (fun _ => v.val.toNNReal) (ContinuousPath.shift u p.2) -
    stoppedAnnularClock (fun z => ε^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) ε z)) δ
        (fun _ => v.val.toNNReal) (ContinuousPath.shift u p.2)|) ⟨s, hs⟩
  simpa only [Real.toNNReal_coe, s, stoppedAnnularClock] using h

/-- The expected same-shell clock supremum with a common path-dependent stop
has a time-mesh bound uniform in the deterministic shift and stop. -/
theorem exists_lintegral_prod_shift_stoppedAnnularClock_radius_stopped_iSup_le_uniform_shift_rate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (θ d M β : ℝ) (C : ℝ≥0∞), γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧ 0 < β ∧ C < ∞ ∧
      ∀ (u : ℝ≥0) {r ε : ℝ}, 0 < r → 0 < ε → ε ≤ 1/2 → ε ≤ δ → r ≤ ε → ε / 2 ≤ r →
      ∀ (τ : ContinuousPath ℂ → ℝ≥0) (m : ℕ), 0 < m →
      let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
        stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
          (fun _ => min t.toNNReal (τ p.2)) (ContinuousPath.shift u p.2)
      (∫⁻ p, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F r p t - F ε p t|
        ∂(P.prod (planarBrownianMotion x))) ≤
      (m + 1 : ℝ≥0∞) * ENNReal.ofReal (
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) + C * (m : ℝ≥0∞)^(-β) := by
  obtain ⟨θ, d, M, β, C, hγθ, hθ, hd0, hd2, hp, hM, hβ, hC, hb⟩ :=
    exists_lintegral_prod_shift_stoppedAnnularClock_radius_iSup_le_uniform_shift_rate
      hh x hγ0 hγ2 α hδ
  refine ⟨θ, d, M, β, C, hγθ, hθ, hd0, hd2, hp, hM, hβ, hC, ?_⟩
  intro u r ε hr hε hεhalf hεδ hrε hr2 τ m hm
  exact (lintegral_prod_shift_stoppedAnnularClock_radius_iSup_le x u γ α δ r ε τ).trans
    (hb u hr hε hεhalf hεδ hrε hr2 m hm)

private def unitRationalTime (q : ℚ) : Icc (0 : ℝ) 1 :=
  ⟨min 1 (max (q : ℝ) 0), ⟨le_min (by norm_num) (le_max_right _ _), min_le_left _ _⟩⟩

private theorem unit_iSup_eq_rational (f : ℝ → ℝ≥0∞) (hf : Continuous f) :
    (⨆ t : Icc (0 : ℝ) 1, f t) = ⨆ q : ℚ, f (unitRationalTime q) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    have hc : Continuous (fun x : ℝ => f (min 1 (max x 0))) :=
      hf.comp (continuous_const.min (continuous_id.max continuous_const))
    have hclosed : IsClosed {x : ℝ | f (min 1 (max x 0)) ≤ ⨆ q : ℚ, f (unitRationalTime q)} :=
      isClosed_le hc continuous_const
    have hall : ∀ x : ℝ, f (min 1 (max x 0)) ≤ ⨆ q : ℚ, f (unitRationalTime q) := by
      intro x
      refine Rat.denseRange_cast.induction_on x hclosed ?_
      intro q
      exact le_iSup (fun q : ℚ => f (unitRationalTime q)) q
    simpa only [max_eq_left t.property.1, min_eq_right t.property.2] using hall t
  · apply iSup_le
    intro q
    exact le_iSup (fun t : Icc (0 : ℝ) 1 => f t) (unitRationalTime q)

/-- The shifted unit-time supremum of a positive-radius annular clock difference
is measurable under the product law. -/
theorem aemeasurable_shift_annular_radius_iSup
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) (u : ℝ≥0)
    (γ α δ : ℝ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
      stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
        (fun _ => t.toNNReal) (ContinuousPath.shift u p.2)
    AEMeasurable (fun p => ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F r p t - F ε p t|)
      (P.prod (planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  dsimp only
  let F : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
    stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
      (fun _ => t.toNNReal) (ContinuousPath.shift u p.2)
  have hq (q : ℚ) : AEMeasurable (fun p : Ω × ContinuousPath ℂ =>
      ENNReal.ofReal |F r p (unitRationalTime q) - F ε p (unitRationalTime q)|)
      (P.prod (planarBrownianMotion x)) := by
    let τ : ContinuousPath ℂ → ℝ≥0 := fun _ => ((unitRationalTime q : Icc (0 : ℝ) 1) : ℝ).toNNReal
    obtain ⟨G, hGm, hGae⟩ := exists_measurable_annularRadiusIncrementSample hh hε hr γ α δ τ measurable_const
    have hmG : Measurable (fun p : Ω × ContinuousPath ℂ => ENNReal.ofReal |G (ContinuousPath.shift u p.2, p.1)|) :=
      ENNReal.measurable_ofReal.comp ((hGm.comp (((ContinuousPath.measurable_shift_fixed u).comp measurable_snd).prodMk measurable_fst)).abs)
    apply hmG.aemeasurable.congr
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hGae,
      (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
        (ae_stoppedAnnularClock_sub_eq_annularRadiusIncrementSample hh γ α δ)] with p hp hsub
    change ENNReal.ofReal |G (ContinuousPath.shift u p.2, p.1)| =
      ENNReal.ofReal |stoppedAnnularClock _ δ τ (ContinuousPath.shift u p.2) -
       stoppedAnnularClock _ δ τ (ContinuousPath.shift u p.2)|
    rw [hp, hsub ε r hε hr τ (ContinuousPath.shift u p.2)]
  apply (AEMeasurable.iSup hq).congr
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hHae,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
      (ae_recentered_inserted_circle_average hh α)] with p hω hrec
  have hf (v : ℝ) (hv : 0 < v) : Continuous (fun z : ℂ => v^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) := by
    have hc : Continuous (hcirc p.1 v) := by
      rw [← funext (hω v)]
      exact hHc p.1 v hv
    have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z) =
        fun z => hcirc p.1 v z - hcirc p.1 1 0 - α * Real.log (max v ‖z‖) := by
      funext z
      exact (hrec v z hv).symm
    have hci : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z) := by
      rw [heq]
      exact (hc.sub continuous_const).sub (continuous_const.mul
        ((continuous_const.max continuous_norm).log (fun _ => (lt_max_of_lt_left hv).ne')))
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))
  have htime (v : ℝ) (hv : 0 < v) : Continuous (F v p) :=
    continuous_stoppedAnnularClock_time _ (hf v hv) δ (ContinuousPath.shift u p.2)
  exact (unit_iSup_eq_rational _ (ENNReal.continuous_ofReal.comp ((htime r hr).sub (htime ε hε)).abs)).symm

private theorem ofReal_abs_le_sum_unit_bounds (D : ℝ → ℝ) (hD : D 0 = 0) (B : ℕ → ℝ≥0∞)
    (hB : ∀ (n : ℕ) (t : ℝ), 0 ≤ t → t ≤ 1 →
      ENNReal.ofReal |D ((n : ℝ) + t) - D n| ≤ B n) :
    ∀ (N : ℕ) (t : ℝ), 0 ≤ t → t ≤ N →
      ENNReal.ofReal |D t| ≤ ∑ n ∈ Finset.range N, B n := by
  intro N
  induction N with
  | zero =>
    intro t ht0 htN
    have htN' : t ≤ (0 : ℝ) := by simpa only [Nat.cast_zero] using htN
    have ht : t = 0 := le_antisymm htN' ht0
    simp only [ht, hD, abs_zero, ENNReal.ofReal_zero, Finset.range_zero, Finset.sum_empty, le_refl]
  | succ N ih =>
    intro t ht0 htN
    rw [Finset.sum_range_succ]
    by_cases htn : t ≤ N
    · exact (ih t ht0 htn).trans (le_add_right le_rfl)
    · have htN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      have htn' : (N : ℝ) < t := lt_of_not_ge htn
      have hsub0 : 0 ≤ t - N := by linarith
      have hsub1 : t - N ≤ 1 := by push_cast at htN; linarith
      have hprev := ih N htN0 le_rfl
      have hlast := hB N (t - N) hsub0 hsub1
      have hsum : (N : ℝ) + (t - N) = t := by ring
      rw [hsum] at hlast
      calc
        ENNReal.ofReal |D t| = ENNReal.ofReal |D N + (D t - D N)| := by congr 1; ring
        _ ≤ ENNReal.ofReal (|D N| + |D t - D N|) := ENNReal.ofReal_le_ofReal (abs_add_le _ _)
        _ = ENNReal.ofReal |D N| + ENNReal.ofReal |D t - D N| := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
        _ ≤ _ := add_le_add hprev hlast

/-- A stopped finite-horizon clock difference is bounded by the sum of the
unstopped shifted unit-block suprema. -/
theorem lintegral_prod_annular_clock_stopped_iSup_le_sum_shifted
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    (γ α δ : ℝ) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (τ : ContinuousPath ℂ → ℝ≥0) (N : ℕ) :
    let A : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
      ∫ s in (0 : ℝ)..t, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
        v^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) (p.2 s.toNNReal)
    let F : ℝ → (Ω × ContinuousPath ℂ) → ℕ → ℝ → ℝ := fun v p n t =>
      stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
        (fun _ => t.toNNReal) (ContinuousPath.shift n p.2)
    (∫⁻ p, ⨆ t : Icc (0 : ℝ) N, ENNReal.ofReal
      |A r p (min t (τ p.2)) - A ε p (min t (τ p.2))|
      ∂(P.prod (planarBrownianMotion x))) ≤
    ∑ n ∈ Finset.range N, ∫⁻ p, ⨆ t : Icc (0 : ℝ) 1,
      ENNReal.ofReal |F r p n t - F ε p n t| ∂(P.prod (planarBrownianMotion x)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  dsimp only
  let A : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
    ∫ s in (0 : ℝ)..t, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
      v^(γ^2/2) * Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z))
        (p.2 s.toNNReal)
  let F : ℝ → (Ω × ContinuousPath ℂ) → ℕ → ℝ → ℝ := fun v p n t =>
    stoppedAnnularClock (fun z => v^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) δ
      (fun _ => t.toNNReal) (ContinuousPath.shift n p.2)
  let B : ℕ → Ω × ContinuousPath ℂ → ℝ≥0∞ := fun n p =>
    ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F r p n t - F ε p n t|
  have hB (n : ℕ) : AEMeasurable (B n) (P.prod (planarBrownianMotion x)) :=
    aemeasurable_shift_annular_radius_iSup hh x n γ α δ hr hε
  rw [← lintegral_finsetSum' (Finset.range N) (fun n _ => hB n)]
  apply lintegral_mono_ae
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae hHae,
    (Measure.quasiMeasurePreserving_fst (μ := P) (ν := planarBrownianMotion x)).ae
      (ae_recentered_inserted_circle_average hh α)] with p hω hrec
  let f (v : ℝ) : ℂ → ℝ := fun z => v^(γ^2/2) * Real.exp (γ *
    LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)
  have hf (v : ℝ) (hv : 0 < v) : Continuous (f v) := by
    have hc : Continuous (hcirc p.1 v) := by
      rw [← funext (hω v)]
      exact hHc p.1 v hv
    exact continuous_inserted_density_at_radius (hcirc p.1) γ α v hv hc (fun z => hrec v z hv)
  let D : ℝ → ℝ := fun t => A r p t - A ε p t
  have hD : D 0 = 0 := by simp [D, A]
  have hblock (n : ℕ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
      ENNReal.ofReal |D ((n : ℝ) + t) - D n| ≤ B n p := by
    have h1 := stoppedAnnularClock_shift_eq_time_increment (f r) (hf r hr) δ p.2 n ⟨t, ht0, ht1⟩
    have h2 := stoppedAnnularClock_shift_eq_time_increment (f ε) (hf ε hε) δ p.2 n ⟨t, ht0, ht1⟩
    change F r p n t = A r p ((n : ℝ) + t) - A r p n at h1
    change F ε p n t = A ε p ((n : ℝ) + t) - A ε p n at h2
    have heq : D ((n : ℝ) + t) - D n = F r p n t - F ε p n t := by
      dsimp [D]
      rw [h1, h2]
      ring
    rw [heq]
    exact le_iSup (fun t : Icc (0 : ℝ) 1 => ENNReal.ofReal |F r p n t - F ε p n t|) ⟨t, ht0, ht1⟩
  apply iSup_le
  intro t
  have ht0 : 0 ≤ min (t : ℝ) (τ p.2 : ℝ) := le_min t.property.1 (τ p.2).coe_nonneg
  have htN : min (t : ℝ) (τ p.2 : ℝ) ≤ N := (min_le_left _ _).trans t.property.2
  exact ofReal_abs_le_sum_unit_bounds D hD (fun n => B n p) hblock N _ ht0 htN

/-- Finite-horizon stopped annular clock differences obey a mesh bound whose
constants are uniform over deterministic horizons and common stops. -/
theorem exists_lintegral_prod_annular_clock_stopped_iSup_le_rate
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (θ d M β : ℝ) (C : ℝ≥0∞), γ < θ ∧ θ < 2*γ ∧ 0 < d ∧ d < 2 ∧
      0 < d - γ^2 + (2*γ-θ)^2/2 ∧ 0 ≤ M ∧ 0 < β ∧ C < ∞ ∧
      ∀ {r ε : ℝ}, 0 < r → 0 < ε → ε ≤ 1/2 → ε ≤ δ → r ≤ ε → ε / 2 ≤ r →
      ∀ (τ : ContinuousPath ℂ → ℝ≥0) (N m : ℕ), 0 < m →
      let A : ℝ → (Ω × ContinuousPath ℂ) → ℝ → ℝ := fun v p t =>
        ∫ s in (0 : ℝ)..t, {z : ℂ | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}.indicator (fun z =>
          v^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) v z)) (p.2 s.toNNReal)
      (∫⁻ p, ⨆ t : Icc (0 : ℝ) N, ENNReal.ofReal
        |A r p (min t (τ p.2)) - A ε p (min t (τ p.2))|
        ∂(P.prod (planarBrownianMotion x))) ≤
      (N : ℝ≥0∞) * ((m + 1 : ℝ≥0∞) * ENNReal.ofReal (
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) + C * (m : ℝ≥0∞)^(-β)) := by
  obtain ⟨θ, d, M, β, C, hγθ, hθ, hd0, hd2, hp, hM, hβ, hC, hb⟩ :=
    exists_lintegral_prod_shift_stoppedAnnularClock_radius_iSup_le_uniform_shift_rate
      hh x hγ0 hγ2 α hδ
  refine ⟨θ, d, M, β, C, hγθ, hθ, hd0, hd2, hp, hM, hβ, hC, ?_⟩
  intro r ε hr hε hεhalf hεδ hrε hr2 τ N m hm
  dsimp only
  refine (lintegral_prod_annular_clock_stopped_iSup_le_sum_shifted hh x γ α δ hr hε τ N).trans ?_
  calc
    _ ≤ ∑ _n ∈ Finset.range N, ((m + 1 : ℝ≥0∞) * ENNReal.ofReal (
        ((Real.exp (γ^2*Real.log 2)-1) *
          (M^2 * (∫ b, unitOccupationRieszEnergy d b ∂planarBrownianMotion 0) * 2^d)+1)/2 *
          Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
        2*M*Real.exp (Real.log ε * ((θ-γ)^2/2))) + C * (m : ℝ≥0∞)^(-β)) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hb n hr hε hεhalf hεδ hrε hr2 m hm
    _ = _ := by simp [mul_add]

/-- Geometric time meshes and radius grids give a summable bound. -/
theorem summable_annular_grid_mesh {p q β b c A B D : ℝ}
    (hβ : 0 < β) (hb : 0 < b) (hc : 0 < c)
    (hcp : c ≤ p - b / 2) (hcq : c ≤ q - b / 2) (hcβ : c ≤ b * β / 2)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D) :
    Summable (fun k : ℕ => ((LatticeProb.LQG.GMCScaleGrid.gridCount c k : ℝ) + 1) *
      ((((LatticeProb.LQG.GMCScaleGrid.gridCount b k : ℝ) + 1) + 1) *
        (A * LatticeProb.LQG.dyadicScale k ^ p + B * LatticeProb.LQG.dyadicScale k ^ q) +
          D * (((LatticeProb.LQG.GMCScaleGrid.gridCount b k : ℝ) + 1) ^ (-β)))) := by
  have hs := LatticeProb.LQG.GMCScaleGrid.summable_gridCount (c := c) (θ := 0) (K := 3*A + 3*B + D)
    (by norm_num) (by linarith)
  simp only [Real.rpow_zero, div_one] at hs
  apply Summable.of_nonneg_of_le ?_ ?_ hs
  · intro k
    have hscale := dyadicScale_pos k
    positivity
  ·
    intro k
    let e : ℝ := LatticeProb.LQG.dyadicScale k
    let a : ℝ := e ^ (-(b / 2))
    let m : ℝ := (LatticeProb.LQG.GMCScaleGrid.gridCount b k : ℝ) + 1
    have he0 : 0 < e := dyadicScale_pos k
    have he1 : e ≤ 1 := by
      dsimp [e, LatticeProb.LQG.dyadicScale]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have ha0 : 0 < a := Real.rpow_pos_of_pos he0 _
    have ha1 : 1 ≤ a := Real.one_le_rpow_of_pos_of_le_one_of_nonpos he0 he1 (by linarith)
    have ham : a ≤ m := by
      dsimp [m, a, LatticeProb.LQG.GMCScaleGrid.gridCount]
      exact (Nat.lt_floor_add_one _).le
    have hmle : m + 1 ≤ 3 * a := by
      have hfloor : (LatticeProb.LQG.GMCScaleGrid.gridCount b k : ℝ) ≤ a := by
        dsimp [a, LatticeProb.LQG.GMCScaleGrid.gridCount]
        exact Nat.floor_le (Real.rpow_pos_of_pos he0 _).le
      dsimp [m]
      linarith
    have hmp : m ^ (-β) ≤ e ^ c := by
      calc
        m ^ (-β) ≤ a ^ (-β) := Real.rpow_le_rpow_of_nonpos ha0 ham (by linarith)
        _ = e ^ (b * β / 2) := by
          dsimp [a]
          rw [← Real.rpow_mul he0.le]
          congr 1
          ring
        _ ≤ e ^ c := Real.rpow_le_rpow_of_exponent_ge he0 he1 hcβ
    have hp : a * e ^ p ≤ e ^ c := by
      dsimp only [a]
      rw [← Real.rpow_add he0]
      apply Real.rpow_le_rpow_of_exponent_ge he0 he1
      linarith
    have hq : a * e ^ q ≤ e ^ c := by
      dsimp only [a]
      rw [← Real.rpow_add he0]
      apply Real.rpow_le_rpow_of_exponent_ge he0 he1
      linarith
    have hec : 0 ≤ e ^ c := (Real.rpow_pos_of_pos he0 c).le
    have hp0 : 0 ≤ e ^ p := (Real.rpow_pos_of_pos he0 p).le
    have hq0 : 0 ≤ e ^ q := (Real.rpow_pos_of_pos he0 q).le
    have hsum : (m + 1) * (A * e ^ p + B * e ^ q) + D * m ^ (-β) ≤
        (3*A + 3*B + D) * e ^ c := by
      calc
        _ ≤ (3*a) * (A * e ^ p + B * e ^ q) + D * e ^ c := by gcongr
        _ = 3*A * (a * e ^ p) + 3*B * (a * e ^ q) + D * e ^ c := by ring
        _ ≤ 3*A * e ^ c + 3*B * e ^ c + D * e ^ c := by gcongr
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
end HarmonicBalls
