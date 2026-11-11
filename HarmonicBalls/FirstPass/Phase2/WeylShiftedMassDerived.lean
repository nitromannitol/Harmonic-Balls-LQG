import HarmonicBalls.FirstPass.Frozen.S11c
import LatticeProb.Prob.WeylMassMeasurable

/-!
# The Weyl-shifted LQG mass is AE-measurable (derived, no hypothesis)

Derives the frozen Prop `WeylShiftedMassMeasurableFrozen` (`HarmonicBalls/FirstPass/Frozen/S11c.lean`): for a closed
dyadic square `S`, the map `ω ↦ (weylShiftPair γ ξ f (μ ω, D ω)).1 S = (μ ω).withDensity (exp (γ f)) S` is AE-measurable.
The derivation uses only the definitions `IsWholePlaneGFF` (circle averages measurable in `ω` and a.s. continuous on
`(0, ∞) × ℂ`) and `IsLQGMeasureOfField` (a.s. `μ ω` Radon and the vague limit of `lqgApprox γ h_ε (2^{-k})`, Duplantier-
Sheffield 2011, Prop. 1.1, as used in Bou-Rabee-Gwynne eq. (2.6)). No literature input is used.

Route. `IsLQGMeasure` does not contain measurability of `ω ↦ μ ω A`; its docstring says it follows from the vague
convergence and the a.s. continuity of the circle averages. Concretely: let `N` be a measurable `P`-null set off which
the circle averages are continuous and the vague limit holds. Off `N`, the density of `lqgApprox` at scale `ε` is
`ε^{γ²/2} exp(γ H_ε(ω, z))`, where `H_ε` is the modified circle average (`modifiedFieldCircleAverage`), which equals
`fieldCircleAverage α₀ (hcirc ω) ε z` off `N` (`fieldCircleAverage_eq`). `H_ε` is jointly measurable, so
`ω ↦ ∫⁻ ofReal (ψ z) * density` is measurable (`LatticeProb.Prob.measurable_lintegral_of_caratheodory`). Its
`toReal` is `ω ↦ ∫ ψ d(lqgApprox)`, which converges to `ω ↦ ∫ ψ dμ_ω` off `N`, so the latter is AE-measurable. The mass
`(μ ω).withDensity (exp (γ f)) S` is the a.e. limit of `∫⁻ ofReal (ψ n) dμ_ω` for the approximations `ψ n` of
`S.indicator (exp (γ f))` (`LatticeProb.Prob.exists_approx_indicator_of_compact`,
`LatticeProb.Prob.tendsto_lintegral_approx_withDensity`).

The weight satisfies `0 ≤ exp (γ f) ≤ 1` because `f ≤ 0` and `γ > 0`.
-/

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- The circle averages of the whole-plane GFF with the exceptional set `N` set to zero, for the field
`h = h^ℂ - α₀ log |·|`: `ω ↦ 1_{ω ∉ N} h^ℂ_ε(z) - α₀ log max(ε, |z|)`. Off `N` this is
`fieldCircleAverage α₀ (hcirc ω) ε z` (`modifiedFieldCircleAverage_eq`). -/
noncomputable def modifiedFieldCircleAverage {Ω : Type*} (α₀ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (N : Set Ω)
    (ε : ℝ) (ω : Ω) (z : ℂ) : ℝ :=
  Nᶜ.indicator (fun ω => hcirc ω ε z) ω - α₀ * Real.log (max ε ‖z‖)

theorem modifiedFieldCircleAverage_eq {Ω : Type*} (α₀ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) {N : Set Ω} {ω : Ω}
    (hω : ω ∉ N) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    modifiedFieldCircleAverage α₀ hcirc N ε ω z = fieldCircleAverage α₀ (hcirc ω) ε z := by
  rw [fieldCircleAverage_eq α₀ (hcirc ω) hε z, modifiedFieldCircleAverage,
    Set.indicator_of_mem (Set.mem_compl hω)]

theorem modifiedFieldCircleAverage_continuous {Ω : Type*} (α₀ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) {N : Set Ω}
    (hcont : ∀ ω, ω ∉ N → ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) {ε : ℝ}
    (hε : 0 < ε) (ω : Ω) : Continuous fun z => modifiedFieldCircleAverage α₀ hcirc N ε ω z := by
  have hlog : Continuous fun z : ℂ => α₀ * Real.log (max ε ‖z‖) :=
    continuous_const.mul ((continuous_const.max continuous_norm).log fun z =>
      (lt_of_lt_of_le hε (le_max_left _ _)).ne')
  by_cases hω : ω ∈ N
  · have hnot : ω ∉ Nᶜ := fun h => h hω
    have h0 : ∀ z, Nᶜ.indicator (fun ω => hcirc ω ε z) ω = 0 := fun z =>
      Set.indicator_of_notMem hnot _
    simp only [modifiedFieldCircleAverage, h0, zero_sub]
    exact hlog.neg
  · have h1 : ∀ z, Nᶜ.indicator (fun ω => hcirc ω ε z) ω = hcirc ω ε z := fun z =>
      Set.indicator_of_mem (Set.mem_compl hω) _
    have hc : Continuous fun z => hcirc ω ε z :=
      (hcont ω hω).comp_continuous (continuous_const.prodMk continuous_id) fun z => ⟨hε, mem_univ z⟩
    simp only [modifiedFieldCircleAverage, h1]
    exact hc.sub hlog

theorem measurable_modifiedFieldCircleAverage {Ω : Type*} [MeasurableSpace Ω] (α₀ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (hmeas : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) {N : Set Ω}
    (hN : MeasurableSet N) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Measurable fun ω => modifiedFieldCircleAverage α₀ hcirc N ε ω z :=
  ((hmeas ε z hε).indicator hN.compl).sub measurable_const

/-- Joint measurability of the approximating integrals `ω ↦ ∫⁻ z, φ z * ofReal (ε^{γ²/2} exp (γ H_ε(ω, z)))`. -/
theorem measurable_modifiedDensityIntegral {Ω : Type*} [MeasurableSpace Ω] (γ α₀ : ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (hmeas : ∀ r z, 0 < r → Measurable fun ω => hcirc ω r z) {N : Set Ω}
    (hN : MeasurableSet N)
    (hcont : ∀ ω, ω ∉ N → ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ)) {ε : ℝ}
    (hε : 0 < ε) {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable fun ω => ∫⁻ z, φ z * ENNReal.ofReal
      (ε ^ (γ ^ 2 / 2) * Real.exp (γ * modifiedFieldCircleAverage α₀ hcirc N ε ω z)) := by
  refine LatticeProb.Prob.measurable_lintegral_of_caratheodory
    (fun ω z => modifiedFieldCircleAverage α₀ hcirc N ε ω z)
    (fun z => measurable_modifiedFieldCircleAverage α₀ hcirc hmeas hN hε z)
    (fun ω => modifiedFieldCircleAverage_continuous α₀ hcirc hcont hε ω) hφ
    (G := fun t : ℝ => ENNReal.ofReal (ε ^ (γ ^ 2 / 2) * Real.exp (γ * t))) ?_
  exact ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))

theorem weylMass_closedDyadicSquare_nonempty (n j k : ℤ) : (closedDyadicSquare n j k).Nonempty := by
  have hs : (0 : ℝ) ≤ (2 : ℝ) ^ (-n) := by positivity
  unfold closedDyadicSquare
  refine ⟨⟨(j : ℝ) * (2 : ℝ) ^ (-n), (k : ℝ) * (2 : ℝ) ^ (-n)⟩, ⟨⟨le_refl _, ?_⟩, ⟨le_refl _, ?_⟩⟩⟩
  · nlinarith
  · nlinarith

/-- The Weyl-shifted LQG mass is AE-measurable on closed dyadic squares, with no hypothesis: this derives the frozen
Prop `WeylShiftedMassMeasurableFrozen` (`HarmonicBalls/FirstPass/Frozen/S11c.lean`) in every universe. -/
theorem weylShiftedMassMeasurable_derived : WeylShiftedMassMeasurableFrozen.{u} := by
  intro γ α₀ ξ hγ0 hγ2 hα₀ Ω _ P hC hcirc μ D hGFF hμ _hD f hf hfc hf0 S hS
  obtain ⟨nS, j, k, rfl⟩ := hS
  have hSc : IsCompact (closedDyadicSquare nS j k) := isCompact_closedDyadicSquare nS j k
  have hSne : (closedDyadicSquare nS j k).Nonempty := weylMass_closedDyadicSquare_nonempty nS j k
  have hwc : Continuous fun z => Real.exp (γ * f z) := by fun_prop
  have hw1 : ∀ z, Real.exp (γ * f z) ≤ 1 := fun z =>
    Real.exp_le_one_iff.2 (by nlinarith [hf0 z])
  obtain ⟨ψ, hψc, hψcs, hψ0, hψ1, hψK, hψlim⟩ :=
    LatticeProb.Prob.exists_approx_indicator_of_compact hSc hSne hwc (fun z => (Real.exp_pos _).le) hw1
  -- the a.s. good event: continuity of the circle averages and the vague limit
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  have hgood : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
      IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) :=
    hGFF.ae_continuousOn_circle.and hμ'
  obtain ⟨N, hNm, hN0, hNgood⟩ : ∃ N : Set Ω, MeasurableSet N ∧ P N = 0 ∧
      ∀ ω, ω ∉ N → ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
        IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := by
    refine ⟨toMeasurable P {ω | ¬ (ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2) (Ioi 0 ×ˢ univ) ∧
        IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω))}, measurableSet_toMeasurable _ _, ?_, ?_⟩
    · rw [measure_toMeasurable]
      exact ae_iff.1 hgood
    · intro ω hω
      by_contra h
      exact hω (subset_toMeasurable P _ h)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    rw [ae_iff]
    simpa using hN0
  -- measurability of the approximating integrals, for each `n` and dyadic scale `k`
  have hmeasDens : ∀ n k : ℕ, Measurable fun ω => ∫⁻ z, ENNReal.ofReal (ψ n z) * ENNReal.ofReal
      (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * modifiedFieldCircleAverage α₀ hcirc N (dyadicScale k) ω z)) :=
    fun n k => measurable_modifiedDensityIntegral γ α₀ hcirc hGFF.measurable_circle hNm
      (fun ω hω => (hNgood ω hω).1) (dyadicScale_pos k) (ENNReal.measurable_ofReal.comp (hψc n).measurable)
  -- the approximating integral is the Bochner integral off `N`
  have hident : ∀ n k : ℕ, ∀ ω, ω ∉ N → ∫ z, ψ n z ∂(lqgApprox γ (fieldCircleAverage α₀ (hcirc ω))
      (dyadicScale k)) = (∫⁻ z, ENNReal.ofReal (ψ n z) * ENNReal.ofReal
        (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * modifiedFieldCircleAverage α₀ hcirc N (dyadicScale k) ω z))).toReal := by
    intro n k ω hω
    have hε := dyadicScale_pos k
    have hHc := modifiedFieldCircleAverage_continuous α₀ hcirc (fun ω hω => (hNgood ω hω).1) hε ω
    have hdens : Measurable fun z => ENNReal.ofReal
        (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * modifiedFieldCircleAverage α₀ hcirc N (dyadicScale k) ω z)) :=
      ENNReal.measurable_ofReal.comp (Continuous.measurable (by fun_prop))
    have hg : Measurable fun z => ENNReal.ofReal (ψ n z) := ENNReal.measurable_ofReal.comp (hψc n).measurable
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hψ0 n)) (hψc n).aestronglyMeasurable]
    congr 1
    unfold lqgApprox
    have hfun : (fun z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldCircleAverage α₀ (hcirc ω) (dyadicScale k) z))) =
        fun z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
          Real.exp (γ * modifiedFieldCircleAverage α₀ hcirc N (dyadicScale k) ω z)) := by
      funext z
      rw [modifiedFieldCircleAverage_eq α₀ hcirc hω hε z]
    rw [hfun, lintegral_withDensity_eq_lintegral_mul _ hdens hg]
    exact lintegral_congr fun z => by simp only [Pi.mul_apply]; exact mul_comm _ _
  -- real-valued measurability of `ω ↦ ∫ ψ n dμ_ω` as an a.e. limit
  have hreal : ∀ n : ℕ, AEMeasurable (fun ω => ∫ z, ψ n z ∂(μ ω)) P := by
    intro n
    refine aemeasurable_of_tendsto_metrizable_ae atTop
      (f := fun k ω => (∫⁻ z, ENNReal.ofReal (ψ n z) * ENNReal.ofReal
        (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * modifiedFieldCircleAverage α₀ hcirc N (dyadicScale k) ω z))).toReal)
      (fun k => (hmeasDens n k).ennreal_toReal.aemeasurable) ?_
    filter_upwards [hNae] with ω hω
    exact ((hNgood ω hω).2.tendsto_integral (ψ n) (hψc n) (hψcs n)).congr fun k => hident n k ω hω
  -- ENNReal-valued measurability of `ω ↦ ∫⁻ ofReal (ψ n) dμ_ω`
  have hlin : ∀ n : ℕ, AEMeasurable (fun ω => ∫⁻ z, ENNReal.ofReal (ψ n z) ∂(μ ω)) P := by
    intro n
    refine (ENNReal.measurable_ofReal.comp_aemeasurable (hreal n)).congr ?_
    filter_upwards [hNae] with ω hω
    have := (hNgood ω hω).2.isLocallyFiniteMeasure
    have hint : Integrable (ψ n) (μ ω) := (hψc n).integrable_of_hasCompactSupport (hψcs n)
    exact ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ (hψ0 n))
  -- the mass of the Weyl-shifted measure is the a.e. limit of these
  show AEMeasurable (fun ω => (μ ω).withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z)))
    (closedDyadicSquare nS j k)) P
  refine aemeasurable_of_tendsto_metrizable_ae atTop hlin ?_
  filter_upwards [hNae] with ω hω
  have := (hNgood ω hω).2.isLocallyFiniteMeasure
  exact LatticeProb.Prob.tendsto_lintegral_approx_withDensity hSc hψc hψ1 hψK hψlim

end HarmonicBalls
