import HarmonicBalls.Proofs.Sec8.OrdinaryFieldNormalizedRestriction
import HarmonicBalls.Proofs.Sec8.MeasurableStartingAtoms
import HarmonicBalls.Proofs.Sec8.AnnulusComparisonStationarity
import HarmonicBalls.Proofs.Sec8.GermPathErgodic

/-! # Stationary localized normalized measures

A fixed observation window is pulled back to each dyadic scale, then its mass
is normalized. The normalization removes the scalar in the LQG scaling law.
The imported Section 8 ergodic development uses Leonardo Bonanno's
LatticeProb formalization, `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal

namespace HarmonicBalls

/-- The dyadically rescaled restriction to a fixed observation window,
normalized by the mass of that window. -/
noncomputable def localizedDyadicMeasure (U : Set ℂ) (μ : Measure ℂ) (n : ℕ) : Measure ℂ :=
  normalizedRestriction (μ.map (fun z : ℂ => (dyadicScale n)⁻¹ • z)) U

/-- The localized dyadic path is measurable as a function of the measure. -/
theorem measurable_localizedDyadicMeasure (U : Set ℂ) (hU : MeasurableSet U) :
    Measurable (fun μ : Measure ℂ => fun n => localizedDyadicMeasure U μ n) := by
  apply Measurable.of_eval
  intro n
  apply (measurable_normalizedRestriction_measure U hU).comp
  exact Measure.measurable_map _ (by fun_prop)

/-- Normalized pullback by one dyadic step shifts the entire localized path. -/
theorem localizedDyadicMeasure_normalizedPullback (U : Set ℂ) (μ : Measure ℂ)
    (hcirc : ℝ → ℂ → ℝ) (γ α : ℝ) (n : ℕ) :
    localizedDyadicMeasure U (normalizedPullbackMeasure γ α (dyadicScale 1) hcirc μ) n =
      localizedDyadicMeasure U μ (n + 1) := by
  unfold localizedDyadicMeasure normalizedPullbackMeasure
  rw [Measure.map_smul _ ((by fun_prop : Measurable
    (fun z : ℂ => (dyadicScale n)⁻¹ • z)).aemeasurable)]
  rw [normalizedRestriction_smul _ _ (ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity)))
    ENNReal.ofReal_ne_top]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 2
  funext z
  simp only [Function.comp_apply, smul_smul, dyadicScale, pow_succ, mul_inv_rev]
  congr 1
  ring

/-- The path coordinate can be obtained from the normalized restriction to
the corresponding physical ball. -/
theorem localizedDyadicMeasure_ball (μ : Measure ℂ) (R : ℝ) (n : ℕ) :
    localizedDyadicMeasure (ball 0 R) μ n =
      (normalizedRestriction μ (ball 0 (dyadicScale n * R))).map
        (fun z : ℂ => (dyadicScale n)⁻¹ • z) := by
  have hf : Measurable (fun z : ℂ => (dyadicScale n)⁻¹ • z) := by fun_prop
  unfold localizedDyadicMeasure normalizedRestriction
  rw [Measure.map_apply hf isOpen_ball.measurableSet,
    preimage_inv_smul_ball_zero (dyadicScale_pos n),
    Measure.restrict_map hf isOpen_ball.measurableSet,
    preimage_inv_smul_ball_zero (dyadicScale_pos n),
    Measure.map_smul _ hf.aemeasurable]

/-- Local versions of normalized restrictions on every small ball give local
versions of all sufficiently late coordinates of the dyadic path. -/
theorem ae_local_localizedDyadicMeasure_of_normalizedRestriction_versions
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (germ : ℝ → MeasurableSpace Ω) (hgerm : Monotone germ)
    (μ : Ω → Measure ℂ) (R : ℝ) (hR : 0 < R)
    (hrep : ∀ r, 0 < r → ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (germ r) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 r)) :
    ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → Measure ℂ,
      (∀ n, K ≤ n → @Measurable Ω (Measure ℂ) (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω => localizedDyadicMeasure (ball 0 R) (μ ω) n) =ᵐ[P] Y n) := by
  intro ε hε
  obtain ⟨K, hK⟩ := dyadicScale_germ_cofinal.2 (ε / R) (div_pos hε hR)
  choose ν hνm hνeq using fun n : ℕ => hrep (dyadicScale n * R)
    (mul_pos (dyadicScale_pos n) hR)
  refine ⟨K, (fun n ω => (ν n ω).map (fun z : ℂ => (dyadicScale n)⁻¹ • z)), ?_, ?_⟩
  · intro n hn
    have hle : dyadicScale n * R ≤ ε := by
      apply (le_div_iff₀ hR).1
      exact (dyadicScale_germ_cofinal.1 hn).trans hK
    have hm : @Measurable Ω (Measure ℂ) (germ ε) _ (ν n) :=
      (hνm n).mono (hgerm hle) le_rfl
    let : MeasurableSpace Ω := germ ε
    exact (Measure.measurable_map _ (by fun_prop)).comp hm
  · intro n hn
    filter_upwards [hνeq n] with ω hω
    rw [localizedDyadicMeasure_ball, hω]

universe u

/-- The normalized restrictions of an LQG measure form a stationary path.
The affine-invariance and coordinate-change inputs are kept explicit. -/
theorem IsWholePlaneGFF.identDistrib_localizedDyadicMeasure_shift
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc)
    (U : Set ℂ) (hU : MeasurableSet U) :
    IdentDistrib (fun ω n => localizedDyadicMeasure U (μ ω) n)
      (fun ω n => localizedDyadicMeasure U (μ ω) (n + 1)) P P := by
  let F : Measure ℂ → ℕ → Measure ℂ := fun ν n => localizedDyadicMeasure U ν n
  have hF : Measurable F := measurable_localizedDyadicMeasure U hU
  have hd := (hGFF.identDistrib_normalizedPullback hAff hCC hγ hγ2 hα hμ
    (dyadicScale_pos 1)).comp hF
  apply hd.trans
  apply IdentDistrib.of_ae_eq hd.aemeasurable_snd
  filter_upwards [] with ω
  funext n
  exact localizedDyadicMeasure_normalizedPullback U (μ ω) (hcirc ω) γ α n

/-- The localized LQG measure path is ergodic when normalized restrictions
have the stated almost-sure versions in the local field modulo constants. -/
theorem IsWholePlaneGFF.ergodic_localizedDyadicMeasure_shift
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμm : Measurable μ) (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α hC hcirc) (R : ℝ) (hR : 0 < R)
    (hrep : ∀ r, 0 < r → ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ)
        (Section6.fieldSigmaAlgebraModConst α hC (ball 0 r)) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 r)) :
    Ergodic (fun x : ℕ → Measure ℂ => fun n => x (n + 1))
      (P.map (fun ω n => localizedDyadicMeasure (ball 0 R) (μ ω) n)) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let germ := fun r => Section6.fieldSigmaAlgebraModConst α hC (ball 0 r)
  have hXm : ∀ n, Measurable (fun ω => localizedDyadicMeasure (ball 0 R) (μ ω) n) := by
    intro n
    exact (measurable_pi_apply n).comp
      ((measurable_localizedDyadicMeasure _ isOpen_ball.measurableSet).comp hμm)
  have hstat : P.map (fun ω n => localizedDyadicMeasure (ball 0 R) (μ ω) (n + 1)) =
      P.map (fun ω n => localizedDyadicMeasure (ball 0 R) (μ ω) n) :=
    (hGFF.identDistrib_localizedDyadicMeasure_shift hγ hγ2 hα hμ hAff hCC _
      isOpen_ball.measurableSet).map_eq.symm
  exact ergodic_shift_of_stationary_ae_local_germ P germ dyadicScale dyadicScale_pos
    dyadicScale_germ_cofinal.2 dyadicScale_germ_cofinal.1
    (monotone_fieldSigmaAlgebraModConst_ball α hC 0) _ hXm hstat
    (ae_local_localizedDyadicMeasure_of_normalizedRestriction_versions P germ
      (monotone_fieldSigmaAlgebraModConst_ball α hC 0) μ R hR hrep)
    (hGFF.origin_germ_trivial α)

end HarmonicBalls
