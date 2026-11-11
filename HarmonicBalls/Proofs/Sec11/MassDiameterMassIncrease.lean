import HarmonicBalls.Proofs.Sec11.MassDiameterCoreWeight
import HarmonicBalls.Proofs.Sec11.LocalConstantWeylShift
import HarmonicBalls.Steps.Sec11.ConeBumpInclusion

/-! # Mass-increasing smooth shift for the mass-diameter argument -/

namespace HarmonicBalls
open MeasureTheory Set
open scoped ENNReal

/-- A positive lower mass bound can be amplified past any finite prescribed
    threshold by a deterministic smooth shift on a compact plateau. -/
theorem exists_smooth_shift_increasing_mass
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    {S O : Set ℂ} (hScompact : IsCompact S) (hS : MeasurableSet S)
    (hO : IsOpen O) (hSO : S ⊆ O) {γ a M : ℝ}
    (hγ : 0 < γ) (ha : 0 < a) (hM : 0 ≤ M)
    (A : Set Ω) (hAp : 0 < P A)
    (hA : ∀ ω ∈ A, ENNReal.ofReal a ≤ μ ω S) :
    ∃ f : ℂ → ℝ, IsTestFunction univ f ∧ (∀ z, 0 ≤ f z) ∧
      (∀ z ∉ O, f z = 0) ∧
      0 < P {ω | ENNReal.ofReal M <
        (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z))) S} := by
  obtain ⟨c, hc, hheight⟩ := exists_cone_bump_height hγ ha (show 0 ≤ M + 1 by linarith)
  obtain ⟨φ, hφsmooth, hφcompact, hφrange, hφone, hφzero⟩ :=
    exists_smooth_compact_cutoff hScompact hO hSO
  let f : ℂ → ℝ := fun z => c * φ z
  have hf : IsTestFunction univ f :=
    ⟨contDiff_const.mul hφsmooth, hφcompact.mul_left, subset_univ _⟩
  refine ⟨f, hf, (fun z => mul_nonneg hc (hφrange z).1), ?_, ?_⟩
  · intro z hz
    simp [f, hφzero z hz]
  · apply hAp.trans_le (measure_mono ?_)
    intro ω hω
    change ENNReal.ofReal M < (μ ω).withDensity
      (fun z => ENNReal.ofReal (Real.exp (γ * f z))) S
    rw [withDensity_apply_of_constantOn (a := ENNReal.ofReal (Real.exp (γ * c))) hS (subset_refl S)
      (fun z hz => by simp [f, hφone z hz])]
    have hm : ENNReal.ofReal (M + 1) ≤
        ENNReal.ofReal (Real.exp (γ * c)) * ENNReal.ofReal a := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      exact ENNReal.ofReal_le_ofReal hheight
    have hlt : ENNReal.ofReal M < ENNReal.ofReal (M + 1) := by
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hM).2 (by linarith)
    exact hlt.trans_le (hm.trans (by gcongr; exact hA ω hω))

end HarmonicBalls
