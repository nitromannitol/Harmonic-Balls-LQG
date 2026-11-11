import HarmonicBalls.Proofs.Sec11.MassDiameterFullSupport
import HarmonicBalls.Proofs.Sec11.MassDiameterMassIncrease

/-! # Mass amplification from full support -/

namespace HarmonicBalls
open MeasureTheory Set Filter
open scoped ENNReal

/-- Full support and a positive-probability event give a deterministic
    smooth shift for which the mass of a compact set exceeds any prescribed
    finite threshold on a positive-probability subevent. -/
theorem exists_mass_increasing_shift_of_ae_full_support
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (A : Set Ω) {S U O : Set ℂ} (hAp : 0 < P A)
    (hScompact : IsCompact S) (hS : MeasurableSet S)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUS : U ⊆ S)
    (hO : IsOpen O) (hSO : S ⊆ O)
    (hfull : ∀ᵐ ω ∂P, ∀ V : Set ℂ, IsOpen V → V.Nonempty → 0 < μ ω V)
    {γ M : ℝ} (hγ : 0 < γ) (hM : 0 ≤ M) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ z, 0 ≤ f z) ∧
      (∀ z ∉ O, f z = 0) ∧
      0 < P {ω | ENNReal.ofReal M <
        (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z))) S} := by
  obtain ⟨c, hc, hp⟩ :=
    exists_positive_mass_threshold_of_ae_full_support P μ A S U hAp hU hUne hUS hfull
  obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hc.ne'
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    simp only [Nat.cast_zero, ENNReal.inv_zero] at hn
    exact (not_lt_of_ge le_top) hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  let B : Set Ω := {ω | ω ∈ A ∧ (8 : ℝ≥0∞) * c < μ ω S}
  apply exists_smooth_shift_increasing_mass P μ hScompact hS hO hSO hγ
    (inv_pos.mpr hnR) hM B hp
  intro ω hω
  have hc8 : c ≤ (8 : ℝ≥0∞) * c := by
    calc
      c = 1 * c := by simp
      _ ≤ 8 * c := by gcongr; norm_num
  have hle : ((n : ℝ≥0∞)⁻¹) ≤ μ ω S :=
    (hn.trans_le (hc8.trans hω.2.le)).le
  simpa [ENNReal.ofReal_inv_of_pos hnR] using hle

/-- Volume growth supplies the full support needed for the mass-increasing
    shift. -/
theorem exists_mass_increasing_shift_of_lqg_growth
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{0})
    {γ α M : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hα : α < lqgQ γ) (hM : 0 ≤ M)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (hgff : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (A : Set Ω) {S U O : Set ℂ} (hAp : 0 < P A)
    (hScompact : IsCompact S) (hS : MeasurableSet S)
    (hU : IsOpen U) (hUne : U.Nonempty) (hUS : U ⊆ S)
    (hO : IsOpen O) (hSO : S ⊆ O) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ z, 0 ≤ f z) ∧
      (∀ z ∉ O, f z = 0) ∧
      0 < P {ω | ENNReal.ofReal M <
        (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z))) S} := by
  exact exists_mass_increasing_shift_of_ae_full_support P μ A hAp hScompact hS hU hUne hUS hO hSO
    (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ α hγ hγ₂ hα
      Ω P hC hcirc μ hgff hμ) hγ hM

end HarmonicBalls
