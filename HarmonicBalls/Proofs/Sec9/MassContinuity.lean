import HarmonicBalls.Proofs.Sec9.MassSymmetricDifference

/-! # Continuity in measure of mass-parametrized balls

The symmetric-difference distance is the absolute mass gap. Consequently,
any mass-parametrized family of same-centre subharmonic balls is continuous
in measure at interior positive times.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped symmDiff

/-- A finite pair satisfying the symmetric-difference mass identity has real
symmetric-difference mass equal to the absolute mass difference. -/
theorem measureReal_symmDiff_of_mass_identity {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {A B : Set X} (hAfin : μ A ≠ ⊤) (hBfin : μ B ≠ ⊤)
    (h : μ (A ∆ B) = (μ A - μ B) + (μ B - μ A)) :
    (μ (A ∆ B)).toReal = |(μ A).toReal - (μ B).toReal| := by
  rcases le_total (μ A) (μ B) with hAB | hBA
  · rw [h, tsub_eq_zero_of_le hAB, zero_add, ENNReal.toReal_sub_of_le hAB hBfin]
    rw [abs_of_nonpos (sub_nonpos.mpr (ENNReal.toReal_mono hBfin hAB))]
    ring
  · rw [h, tsub_eq_zero_of_le hBA, add_zero, ENNReal.toReal_sub_of_le hBA hAfin]
    rw [abs_of_nonneg (sub_nonneg.mpr (ENNReal.toReal_mono hAfin hBA))]

universe u

/-- Simultaneously for all same-centre subharmonic balls compactly contained
in the unit disc, real symmetric-difference mass equals the absolute gap
between their real masses. -/
theorem ae_subharmonicBall_measureReal_symmDiff_inside_unit_disc
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A B : Set ℂ) (z : ℂ),
      closure A ⊆ ball 0 1 → closure B ⊆ ball 0 1 →
      IsSubharmonicBall (μ ω) A z → IsSubharmonicBall (μ ω) B z →
      ((μ ω) (A ∆ B)).toReal = |((μ ω) A).toReal - ((μ ω) B).toReal| := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_symmDiff_mass_inside_unit_disc hI2 h82
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro A B z hAcl hBcl hA hB
  exact measureReal_symmDiff_of_mass_identity (μ ω) (ne_of_lt hA.2.2.2.1)
    (ne_of_lt hB.2.2.2.1) (hω A B z hAcl hBcl hA hB)

/-- Any mass-parametrized same-centre family in the unit disc varies
continuously in measure at positive interior times. Family existence and
joint measurability are not assumed or asserted. -/
theorem ae_massParametrized_subharmonicBall_continuous_in_measure
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : ℝ → Set ℂ) (z : ℂ) (a b t : ℝ), t ∈ Ioo a b → 0 < t →
      (∀ s ∈ Ioo a b, 0 < s → closure (A s) ⊆ ball 0 1 ∧
        IsSubharmonicBall (μ ω) (A s) z ∧ μ ω (A s) = ENNReal.ofReal s) →
      Tendsto (fun s : ℝ => ((μ ω) (A s ∆ A t)).toReal) (𝓝 t) (𝓝 0) ∧
      Tendsto (fun s : ℝ => (μ ω) (A s ∆ A t)) (𝓝 t) (𝓝 0) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_measureReal_symmDiff_inside_unit_disc hI2 h82
    γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hω
  intro A z a b t ht htpos hA
  have hAt := hA t ht htpos
  have hevent : (fun s : ℝ => ((μ ω) (A s ∆ A t)).toReal) =ᶠ[𝓝 t]
      (fun s : ℝ => |s - t|) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht, Ioi_mem_nhds htpos] with s hs hspos
    obtain ⟨hscl, hsb, hsm⟩ := hA s hs hspos
    rw [hω (A s) (A t) z hscl hAt.1 hsb hAt.2.1, hsm, hAt.2.2,
      ENNReal.toReal_ofReal hspos.le, ENNReal.toReal_ofReal htpos.le]
  have hlim : Tendsto (fun s : ℝ => |s - t|) (𝓝 t) (𝓝 0) := by
    have hc : ContinuousAt (fun s : ℝ => |s - t|) t :=
      (continuousAt_id.sub continuousAt_const).abs
    simpa using hc.tendsto
  have hreal := hlim.congr' hevent.symm
  refine ⟨hreal, ?_⟩
  have hfinite : (fun s : ℝ => ENNReal.ofReal (((μ ω) (A s ∆ A t)).toReal)) =ᶠ[𝓝 t]
      (fun s : ℝ => (μ ω) (A s ∆ A t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht, Ioi_mem_nhds htpos] with s hs hspos
    have hsfin : (μ ω) (A s) ≠ ⊤ := ne_of_lt (hA s hs hspos).2.1.2.2.2.1
    have htfin : (μ ω) (A t) ≠ ⊤ := ne_of_lt hAt.2.1.2.2.2.1
    exact ENNReal.ofReal_toReal (measure_symmDiff_ne_top hsfin htfin)
  have hm := ENNReal.tendsto_ofReal hreal
  simpa only [ENNReal.ofReal_zero] using hm.congr' hfinite

end HarmonicBalls
