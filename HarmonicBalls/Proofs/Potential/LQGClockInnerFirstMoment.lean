import HarmonicBalls.Proofs.Potential.LQGClockAnnularExitUniformIntegrability
import HarmonicBalls.Proofs.Potential.BrownianSingularOccupationTail

/-! # Clock density near the insertion

First-moment estimates for the inserted circle-average density near the origin.
-/

open MeasureTheory ProbabilityTheory MarkovProcess Set
open scoped NNReal ENNReal

namespace HarmonicBalls

/-- Field-averaged occupation near the insertion equals the regularized insertion weight. -/
theorem lintegral_inner_inserted_density_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε δ : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hδhalf : δ ≤ 1/2)
    (γ α : ℝ) (ν : Measure ℂ) [SFinite ν] :
    (∫⁻ ω, ∫⁻ z, {z : ℂ | ‖z‖ < δ}.indicator
      (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z ∂ν ∂P) =
    ∫⁻ z, {z : ℂ | ‖z‖ < δ}.indicator
      (fun z => ENNReal.ofReal (Real.exp (-(γ * α) * Real.log (max ε ‖z‖)))) z ∂ν := by
  have := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {z | ‖z‖ < δ}
  have hA : MeasurableSet A := measurableSet_lt measurable_norm measurable_const
  let F : Ω × ℂ → ℝ≥0∞ := fun q => A.indicator (fun z =>
    ENNReal.ofReal (ε ^ (γ^2/2) * Real.exp (γ*(H q.1 ε z - H q.1 1 0 -
      α*Real.log (max ε ‖z‖))))) q.2
  have h1 : Measurable (fun q : Ω × ℂ => H q.1 ε q.2) :=
    (hHm ε hε).comp measurable_swap
  have h2 : Measurable (fun q : Ω × ℂ => H q.1 1 0) :=
    (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_fst)
  have hF : Measurable F := by
    apply Measurable.indicator _ (hA.preimage measurable_snd)
    exact (measurable_const.mul (measurable_const.mul ((h1.sub h2).sub
      (measurable_const.mul ((measurable_const.max measurable_snd.norm).log)))).exp).ennreal_ofReal
  have heq : ∀ᵐ ω ∂P, ∀ z, F (ω,z) = A.indicator (fun z =>
      ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec z
    dsimp [F]
    simp only [Set.indicator_apply]
    split_ifs with hz
    · rw [hω ε z, hω 1 0, hrec ε z hε]
    · rfl
  calc
    _ = ∫⁻ ω, ∫⁻ z, F (ω,z) ∂ν ∂P := by
      apply lintegral_congr_ae
      filter_upwards [heq] with ω hω
      apply lintegral_congr
      intro z
      exact (hω z).symm
    _ = ∫⁻ z, ∫⁻ ω, F (ω,z) ∂P ∂ν := lintegral_lintegral_swap hF.aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ A
      · have hz1 : ‖z‖ + ε ≤ 1 := by dsimp [A] at hz; linarith
        rw [Set.indicator_of_mem hz]
        calc
          (∫⁻ ω, F (ω,z) ∂P) = ∫⁻ ω, ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z)) ∂P := by
              apply lintegral_congr_ae
              filter_upwards [heq] with ω hω
              rw [hω z, Set.indicator_of_mem hz]
          _ = _ := by rw [lintegral_inserted_clock_density_eq hh hε γ α hz1]
      · rw [Set.indicator_of_notMem hz]
        simp [F, Set.indicator_of_notMem hz]

/-- The regularized insertion weight is dominated by the singular inverse power. -/
theorem inserted_weight_le_singular {ε q : ℝ} (hε : 0 < ε) (hq : 0 < q) (z : ℂ) :
    ENNReal.ofReal (Real.exp (-q * Real.log (max ε ‖z‖))) ≤
      (ENNReal.ofReal ‖z‖) ^ (-q) := by
  by_cases hz : ‖z‖ = 0
  · simp [hz, ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr hq)]
  · have hzpos : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz)
    have hmpos : 0 < max ε ‖z‖ := lt_max_of_lt_left hε
    have hle : (max ε ‖z‖) ^ (-q) ≤ ‖z‖ ^ (-q) :=
      Real.rpow_le_rpow_of_nonpos hzpos (le_max_right _ _) (by linarith)
    have heq : Real.exp (-q * Real.log (max ε ‖z‖)) = (max ε ‖z‖) ^ (-q) := by
      rw [Real.rpow_def_of_pos hmpos]
      congr 1
      ring
    rw [heq, ENNReal.ofReal_rpow_of_pos hzpos]
    exact ENNReal.ofReal_le_ofReal hle

/-- Field-averaged inner occupation is bounded by singular spatial occupation. -/
theorem lintegral_inner_inserted_density_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {ε δ : ℝ}
    (hε : 0 < ε) (hεhalf : ε ≤ 1/2) (hδhalf : δ ≤ 1/2)
    (γ α : ℝ) (hq : 0 < γ * α) (ν : Measure ℂ) [SFinite ν] :
    (∫⁻ ω, ∫⁻ z, {z : ℂ | ‖z‖ < δ}.indicator
      (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z ∂ν ∂P) ≤
    ∫⁻ z, if ‖z‖ < δ then (ENNReal.ofReal ‖z‖) ^ (-(γ * α)) else 0 ∂ν := by
  rw [lintegral_inner_inserted_density_eq hh hε hεhalf hδhalf γ α ν]
  apply lintegral_mono
  intro z
  by_cases hz : ‖z‖ < δ
  · simpa [Set.indicator, hz] using inserted_weight_le_singular hε hq z
  · simp [Set.indicator, hz]

/-- The expected inserted clock occupation near the origin has a uniform power bound. -/
theorem planarBrownianMotion_inner_inserted_density_le {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) (γ α p : ℝ)
    (hq : 0 < γ * α) (hqp : γ * α < p) (hp : p < 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ {ε δ : ℝ}, 0 < ε → ε ≤ 1/2 →
      0 < δ → δ ≤ 1/2 →
      let ν := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
      (∫⁻ b, ∫⁻ ω, ∫⁻ z, {z : ℂ | ‖z‖ < δ}.indicator
        (fun z => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε z))) z ∂(ν.map b) ∂P
            ∂(planarBrownianMotion x)) ≤ (ENNReal.ofReal δ) ^ (p - γ * α) * C := by
  obtain ⟨C, hC, hbound⟩ :=
    planarBrownianMotion_unit_singular_occupation_tail_le x 0 hq hqp hp
  refine ⟨C, hC, ?_⟩
  intro ε δ hε hεhalf hδ hδhalf
  let ν : Measure ℝ≥0 := Measure.map Real.toNNReal (volume.restrict (Icc (0 : ℝ) 1))
  have hmeas : Measurable (fun z : ℂ =>
      if ‖z‖ < δ then (ENNReal.ofReal ‖z‖) ^ (-(γ * α)) else 0) := by
    exact Measurable.ite (measurableSet_lt measurable_norm measurable_const) (by fun_prop) measurable_const
  calc
    _ ≤ ∫⁻ b, ∫⁻ z, (if ‖z‖ < δ then (ENNReal.ofReal ‖z‖) ^ (-(γ * α)) else 0)
          ∂(ν.map b) ∂(planarBrownianMotion x) := by
      apply lintegral_mono
      intro b
      exact lintegral_inner_inserted_density_le hh hε hεhalf hδhalf γ α hq (ν.map b)
    _ = ∫⁻ b, ∫⁻ t : ℝ≥0,
        (if ‖b t - (0 : ℂ)‖ < δ then (ENNReal.ofReal ‖b t - (0 : ℂ)‖) ^ (-(γ * α)) else 0)
          ∂ν ∂(planarBrownianMotion x) := by
      apply lintegral_congr
      intro b
      rw [lintegral_map hmeas b.continuous.measurable]
      simp only [sub_zero]
    _ ≤ _ := hbound δ hδ

end HarmonicBalls
