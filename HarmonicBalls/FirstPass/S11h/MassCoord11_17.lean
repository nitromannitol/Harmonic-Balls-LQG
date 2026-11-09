import HarmonicBalls.FirstPass.S11h.CertScalars11_17
import HarmonicBalls.FirstPass.Frozen.S11d

/-!
# First pass, Lemma 11.17: the mass coordinate of the pinch certificate (fp-S11h, owner n2)

Coordinate 7 of `pinchScalars` is the LQG mass `μ U` of the open set `U` (paper line 3238, open disks). The shift
`f` of Step 17.5 vanishes on `U`, so the shifted measure `μ.withDensity (e^{γ f})` has the same mass on `U`
(`withDensity_exp_mass_eq`). Field level: `U` is an increasing union of closed sets `K m ⊆ U`; each mass `μ(K m)`
has a measurable field version by the frozen input `LQGMassFunctionalMeasurableFrozen` (Frozen/S11d.lean:128),
and `μ(U) = ⨆ m, μ(K m)` by continuity of measure from below (`exists_mass_open_functional`).
-/

namespace HarmonicBalls

open MeasureTheory Filter Set
open scoped ENNReal

universe u

/-- The Weyl-shifted measure `μ.withDensity (e^{γ f})` has the same mass as `μ` on a measurable set `U` where `f = 0`
(the density is `exp 0 = 1` there, `weylShiftPair`, Frozen/S11c.lean:23). -/
theorem withDensity_exp_mass_eq {μ : Measure ℂ} {U : Set ℂ} (hU : MeasurableSet U) (γ : ℝ) {f : ℂ → ℝ}
    (hf : ∀ z ∈ U, f z = 0) :
    (μ.withDensity (fun z => ENNReal.ofReal (Real.exp (γ * f z)))) U = μ U := by
  rw [withDensity_apply _ hU]
  have h1 : ∫⁻ z in U, ENNReal.ofReal (Real.exp (γ * f z)) ∂μ = ∫⁻ _ in U, (1 : ℝ≥0∞) ∂μ :=
    setLIntegral_congr_fun hU (fun z hz => by simp [hf z hz])
  rw [h1]
  simp

/-- Field-level mass of an open set `U` (Lemma 11.17, coordinate 7 of `pinchScalars`): from the frozen field-level
mass of closed sets, a single measurable functional `F` with `F (h^ℂ + g) = μ(U)` almost surely for every continuous
`g` vanishing on `U`. Source: exhaustion `U = ⋃ₘ K m` by closed sets (`IsOpen.exists_iUnion_isClosed`, Mathlib) and
continuity of `μ` from below. -/
theorem exists_mass_open_functional (hF : LQGMassFunctionalMeasurableFrozen.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (γ α₀ : ℝ) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (U : Set ℂ) (hU : IsOpen U) :
    ∃ F : ((ℂ → ℝ) → ℝ) → ℝ≥0∞, Measurable[distributionMeasurableSpace] F ∧
      ∀ g : ℂ → ℝ, Continuous g → (∀ z ∈ U, g z = 0) →
        ∀ᵐ ω ∂P, F (addFunPairing (hC ω) g) = μ ω U := by
  obtain ⟨K, hKc, hKU, hKU', hKmono⟩ := hU.exists_iUnion_isClosed
  choose F hFm hFeq using fun m => hF γ α₀ Ω P hC hcirc μ hGFF hγ0 hγ2 hα hμ (K m) (hKc m)
  refine ⟨fun T => ⨆ m, F m T, Measurable.iSup fun m => hFm m, ?_⟩
  intro g hg hg0
  have hae : ∀ᵐ ω ∂P, ∀ m, F m (addFunPairing (hC ω) g) = μ ω (K m) :=
    ae_all_iff.2 fun m => hFeq m g hg fun z hz => hg0 z (hKU m hz)
  filter_upwards [hae] with ω hω
  simp only [hω]
  rw [← hKU']
  exact hKmono.measure_iUnion.symm

end HarmonicBalls
