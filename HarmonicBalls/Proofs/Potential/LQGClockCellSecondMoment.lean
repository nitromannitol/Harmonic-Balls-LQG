import HarmonicBalls.Proofs.Potential.LQGClockAnnularPairKernel
import HarmonicBalls.Proofs.Potential.BrownianTimeRieszEnergy

/-! # Second moments of time-integrated densities

Tonelli's theorem transfers a two-point bound to the second moment of an
integrated nonnegative density.
-/

open MeasureTheory
open scoped ENNReal

namespace HarmonicBalls

/-- A pointwise two-point bound controls the second moment of the integral. -/
theorem lintegral_sq_lintegral_le_pair {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    {P : Measure Ω} [SFinite P] {ν : Measure T} [SFinite ν]
    {f : T → Ω → ℝ≥0∞} (hf : Measurable (Function.uncurry f))
    (K : T → T → ℝ≥0∞)
    (hK : ∀ s t, (∫⁻ ω, f s ω * f t ω ∂P) ≤ K s t) :
    (∫⁻ ω, (∫⁻ t, f t ω ∂ν) ^ 2 ∂P) ≤ ∫⁻ s, ∫⁻ t, K s t ∂ν ∂ν := by
  have hs (ω : Ω) : Measurable (fun t => f t ω) := hf.of_uncurry_right
  have he (ω : Ω) : (∫⁻ t, f t ω ∂ν) ^ 2 =
      ∫⁻ s, ∫⁻ t, f s ω * f t ω ∂ν ∂ν := by
    rw [pow_two, ← lintegral_mul_const _ (hs ω)]
    exact lintegral_congr fun s => (lintegral_const_mul _ (hs ω)).symm
  have hm : Measurable (fun p : (Ω × T) × T => f p.1.2 p.1.1 * f p.2 p.1.1) :=
    (hf.comp (by fun_prop : Measurable fun p : (Ω × T) × T => (p.1.2, p.1.1))).mul
      (hf.comp (by fun_prop : Measurable fun p : (Ω × T) × T => (p.2, p.1.1)))
  have hm1 : Measurable (fun p : Ω × T => ∫⁻ t, f p.2 p.1 * f t p.1 ∂ν) :=
    hm.lintegral_prod_right'
  simp_rw [he]
  rw [lintegral_lintegral_swap hm1.aemeasurable]
  have hs' (s : T) :
      (∫⁻ ω, ∫⁻ t, f s ω * f t ω ∂ν ∂P) =
        ∫⁻ t, ∫⁻ ω, f s ω * f t ω ∂P ∂ν := by
    apply lintegral_lintegral_swap
    exact ((hf.comp (by fun_prop : Measurable fun p : Ω × T => (s, p.1))).mul
      (hf.comp (by fun_prop : Measurable fun p : Ω × T => (p.2, p.1)))).aemeasurable
  simp_rw [hs']
  exact lintegral_mono fun s => lintegral_mono fun t => hK s t

/-- The second moment of the inserted annular mass of an s-finite measure is
bounded by its inverse-power energy. -/
theorem lintegral_annular_inserted_mass_sq_le_riesz
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc)
    (ν : Measure ℂ) [SFinite ν] {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε ≤ δ)
    {γ : ℝ} (hγ : γ ≠ 0) (α : ℝ) :
    (∫⁻ ω, (∫⁻ z, ENNReal.ofReal
        ({u : ℂ | δ ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / 2}.indicator (fun u =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z) ∂ν) ^ 2 ∂P) ≤
      ENNReal.ofReal (Real.exp (|γ * α| * |Real.log δ|) ^ 2 * 2 ^ (γ ^ 2)) *
        ∫⁻ p : ℂ × ℂ, (ENNReal.ofReal ‖p.1 - p.2‖) ^ (-(γ ^ 2)) ∂(ν.prod ν) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨H, _, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let A : Set ℂ := {u : ℂ | δ ≤ ‖u‖ ∧ ‖u‖ ≤ 1 / 2}
  let f : ℂ → Ω → ℝ≥0∞ := fun z ω =>
    ENNReal.ofReal (A.indicator (fun u =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H ω ε u - H ω 1 0 -
        α * Real.log (max ε ‖u‖)))) z)
  have hA : MeasurableSet A :=
    (measurableSet_le measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const)
  have hf : Measurable (Function.uncurry f) := by
    apply ENNReal.measurable_ofReal.comp
    have he : Measurable (fun p : ℂ × Ω => H p.2 ε p.1) := hHm ε hε
    have h1 : Measurable (fun p : ℂ × Ω => H p.2 1 0) :=
      (hHm 1 zero_lt_one).comp (measurable_const.prodMk measurable_snd)
    have hm : Measurable (fun p : ℂ × Ω =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ * (H p.2 ε p.1 - H p.2 1 0 -
          α * Real.log (max ε ‖p.1‖)))) :=
      measurable_const.mul (measurable_const.mul ((he.sub h1).sub
        (measurable_const.mul ((measurable_const.max measurable_fst.norm).log)))).exp
    convert hm.indicator (measurable_fst hA) using 1
    ext p
    rfl
  have hae : ∀ᵐ ω ∂P, ∀ z, f z ω = ENNReal.ofReal (A.indicator (fun u =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ *
        LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z) := by
    filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
    intro z
    dsimp [f]
    simp only [Set.indicator_apply]
    split_ifs
    · rw [hω, hω, hrec ε z hε]
    · rfl
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp (|γ * α| * |Real.log δ|) ^ 2 * 2 ^ (γ ^ 2))
  let K : ℂ → ℂ → ℝ≥0∞ := fun z w => C * (ENNReal.ofReal ‖z - w‖) ^ (-(γ ^ 2))
  have hK (z w : ℂ) : (∫⁻ ω, f z ω * f w ω ∂P) ≤ K z w := by
    have heq : (∫⁻ ω, f z ω * f w ω ∂P) =
        ∫⁻ ω, ENNReal.ofReal (A.indicator (fun u =>
          ε ^ (γ ^ 2 / 2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z) *
          ENNReal.ofReal (A.indicator (fun u =>
            ε ^ (γ ^ 2 / 2) * Real.exp (γ *
              LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) w) ∂P := by
      apply lintegral_congr_ae
      filter_upwards [hae] with ω hω
      rw [hω z, hω w]
    rw [heq]
    exact lintegral_annular_inserted_clock_density_mul_le hh hε hεδ hγ α z w
  have hmain := lintegral_sq_lintegral_le_pair (P := P) (ν := ν) hf K hK
  have heq : (∫⁻ ω, (∫⁻ z, f z ω ∂ν) ^ 2 ∂P) =
      ∫⁻ ω, (∫⁻ z, ENNReal.ofReal (A.indicator (fun u =>
        ε ^ (γ ^ 2 / 2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) ε u)) z) ∂ν) ^ 2 ∂P := by
    apply lintegral_congr_ae
    filter_upwards [hae] with ω hω
    congr 1
    exact lintegral_congr fun z => hω z
  rw [heq] at hmain
  refine hmain.trans_eq ?_
  dsimp [K]
  have hk : Measurable (fun p : ℂ × ℂ => (ENNReal.ofReal ‖p.1 - p.2‖) ^ (-(γ ^ 2))) := by
    fun_prop
  rw [lintegral_prod _ hk.aemeasurable]
  have hk1 (z : ℂ) : Measurable (fun w : ℂ =>
      (ENNReal.ofReal ‖z - w‖) ^ (-(γ ^ 2))) := by fun_prop
  calc
    (∫⁻ z, ∫⁻ w, C * (ENNReal.ofReal ‖z - w‖) ^ (-(γ ^ 2)) ∂ν ∂ν) =
        ∫⁻ z, C * (∫⁻ w, (ENNReal.ofReal ‖z - w‖) ^ (-(γ ^ 2)) ∂ν) ∂ν := by
          apply lintegral_congr
          intro z
          exact lintegral_const_mul C (hk1 z)
    _ = _ := lintegral_const_mul C hk.lintegral_prod_right'


end HarmonicBalls
