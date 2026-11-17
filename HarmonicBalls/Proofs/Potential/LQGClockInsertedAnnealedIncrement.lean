import HarmonicBalls.Proofs.Potential.LQGClockInsertedIncrementEnvelope
import HarmonicBalls.Proofs.Potential.LQGClockSingularAnnularSummability

/-! # Annealed inserted annular increments

Field-increment estimates integrate over the Brownian and field product law.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Real Set
open scoped NNReal ENNReal
namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- A moving annular increment has a jointly measurable representative. -/
theorem exists_measurable_inserted_annular_increment
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    {ε : ℝ} (hε : 0 < ε) (γ α δ : ℝ) :
    ∃ F : ContinuousPath ℂ × Ω → ℝ, Measurable F ∧
      ∀ᵐ ω ∂P, ∀ b : ContinuousPath ℂ,
        F (b, ω) = ∫ w, {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
          (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc ω (ε/2) w-hcirc ω 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
          ε^(γ^2/2) * Real.exp (γ*(hcirc ω ε w-hcirc ω 1 0 - α*Real.log (max ε ‖w‖)))) w
          ∂(Measure.map (fun t => b t) (Measure.map Real.toNNReal
            (volume.restrict (Icc (0 : ℝ) 1)))) := by
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let S : Set ℂ := {w | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}
  have hS : MeasurableSet S := (measurableSet_le measurable_const measurable_norm).inter
    ((measurableSet_le measurable_norm measurable_const).inter
      (measurableSet_le measurable_norm measurable_const))
  let G : Ω × ℂ → ℝ := fun q => S.indicator (fun w =>
    (ε/2)^(γ^2/2) * Real.exp (γ*(H q.1 (ε/2) w-H q.1 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
    ε^(γ^2/2) * Real.exp (γ*(H q.1 ε w-H q.1 1 0 - α*Real.log (max ε ‖w‖)))) q.2
  have hG : Measurable G := by
    have h1 : Measurable (fun q : Ω × ℂ => H q.1 (ε/2) q.2) :=
      (hHm (ε/2) (half_pos hε)).comp measurable_swap
    have h2 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) :=
      (hHm ε hε).comp measurable_swap
    have h3 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
      (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
    apply Measurable.indicator _ (hS.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).sub
      (measurable_const.mul (measurable_const.mul ((h2.sub h3).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp)
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have heval0 : Measurable (fun q : ContinuousPath ℂ × ℝ≥0 => q.1 q.2) := by fun_prop
  have heval : Measurable (fun q : (ContinuousPath ℂ × Ω) × ℝ≥0 => q.1.1 q.2) :=
    heval0.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hpath : Measurable (fun q : ContinuousPath ℂ × Ω =>
      ∫ w, G (q.2,w) ∂(Measure.map (fun t => q.1 t) ν)) := by
    have h := (hG.comp ((measurable_snd.comp measurable_fst).prodMk heval)).stronglyMeasurable.integral_prod_right' (ν := ν)
    convert h.measurable using 1
    funext q
    exact integral_map q.1.continuous.measurable.aemeasurable
      (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  refine ⟨_, hpath, ?_⟩
  filter_upwards [hHae] with ω hω b
  apply integral_congr_ae
  filter_upwards with w
  simp only [G, Set.indicator_apply]
  split_ifs
  · rw [hω, hω, hω]
  · rfl

/-- The expected absolute annular increment is bounded by the mean occupation envelope. -/
theorem inserted_annular_increment_annealed_bound
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ)
    {γ α q₂ β d θ ε : ℝ} (hq : 0 < γ*α) (hqq : γ*α < q₂) (hq₂ : q₂ < 1)
    (hβ : 0 < β) (hβ₂ : β < 2) (hd0 : 0 < d)
    (hd : d < β * (1 - (γ*α)/q₂)) (hγθ : γ ≤ θ) (hθ : θ ≤ 2*γ)
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (δ : ℝ) :
    let I : ContinuousPath ℂ × Ω → ℝ := fun q => ∫ w,
      {w : ℂ | ε ≤ ‖w‖ ∧ ‖w‖ ≤ δ ∧ ‖w‖ ≤ 1/2}.indicator (fun w =>
        (ε/2)^(γ^2/2) * Real.exp (γ*(hcirc q.2 (ε/2) w-hcirc q.2 1 0 - α*Real.log (max (ε/2) ‖w‖))) -
        ε^(γ^2/2) * Real.exp (γ*(hcirc q.2 ε w-hcirc q.2 1 0 - α*Real.log (max ε ‖w‖)))) w
      ∂(Measure.map (fun t => q.1 t) (Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))))
    let R : ContinuousPath ℂ → ℝ := fun b =>
      ((Real.exp (γ^2*Real.log 2)-1)*(2^d * unitSingularPairAllRadiusEnvelope 0 (γ*α) d b)+1)/2 *
        Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
      2*unitSingularOccupationEnvelope 0 (γ*α) b * Real.exp (Real.log ε * ((θ-γ)^2/2))
    Integrable I ((planarBrownianMotion x).prod P) ∧
      (∫ q, |I q| ∂((planarBrownianMotion x).prod P)) ≤ ∫ b, R b ∂(planarBrownianMotion x) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  dsimp only
  obtain ⟨F, hFm, hFae⟩ := exists_measurable_inserted_annular_increment hh hε γ α δ
  let R : ContinuousPath ℂ → ℝ := fun b =>
    ((Real.exp (γ^2*Real.log 2)-1)*(2^d * unitSingularPairAllRadiusEnvelope 0 (γ*α) d b)+1)/2 *
      Real.exp (Real.log ε * ((d-γ^2+(2*γ-θ)^2/2)/2)) +
    2*unitSingularOccupationEnvelope 0 (γ*α) b * Real.exp (Real.log ε * ((θ-γ)^2/2))
  have hRi : Integrable R (planarBrownianMotion x) :=
    integrable_inserted_increment_envelope x hq hqq hq₂ hβ hβ₂ hd ε
  have hfield (b : ContinuousPath ℂ) : Integrable (fun ω => F (b,ω)) P := by
    apply (integrable_inserted_moving_annulus_increment_field hh hε hεhalf γ α δ b).congr
    filter_upwards [hFae] with ω hω
    exact (hω b).symm
  have hbound : ∀ᵐ b ∂(planarBrownianMotion x), (∫ ω, ‖F (b,ω)‖ ∂P) ≤ R b := by
    filter_upwards [ae_inserted_moving_annulus_integrable_envelope hh x hq hqq hq₂ hβ hβ₂ hd0 hd hγθ hθ] with b hb
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

end HarmonicBalls
