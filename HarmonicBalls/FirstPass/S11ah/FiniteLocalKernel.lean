import Mathlib
import HarmonicBalls.FirstPass.S11r.Frozen

/-!
# A finite local measure decoder

Derived adapter for `hBad`. The raw local measure decoder `κ₀` of `LocalMeasureKernelStmt` (S11r/Frozen.lean:144)
is only `Measurable`, and the Step 5 measurability chain (`IsSFiniteKernel`, `exists_modified_failureSet_localCert`)
needs an s-finite kernel. The adapter is: replace `κ₀` by its normalized restriction to the decoder disk `D = ball c₂ r₂`,

  `κ ℓ = (1 + κ₀ ℓ D)⁻¹ • (κ₀ ℓ).restrict D`.

Its total mass is `≤ 1` for every observation `ℓ`, so `κ` is a finite kernel and `IsSFiniteKernel κ` is automatic.
Preservation: if `(κ₀ ℓ).restrict D = ofReal a • μ.restrict D` with `μ` locally finite, then `κ₀ ℓ D < ∞`, and the same
identity holds for `κ ℓ` with the scalar `a' = (1 + κ₀ ℓ D)⁻¹.toReal * a > 0`. Both clauses of `LocalMeasureKernelStmt`
therefore survive, with the same observation codes and the same root-measure quantifiers.

Nothing is assumed beyond `LocalMeasureKernelStmt` (a frozen Draft-level input) and Mathlib.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter Topology
open scoped ENNReal

universe u

namespace HarmonicBalls.FirstPassS11ahFinite

/-- The observation space of the local decoders on the disc `ball c₂ r₂`: the mean-zero test pairings of
`LocalMeasureKernelStmt`. -/
abbrev LocalObs (c₂ : ℂ) (r₂ : ℝ) : Type :=
  {φ : ℂ → ℝ // IsTestFunction (ball c₂ r₂) φ ∧ ∫ x, φ x = 0} → ℝ

/-- The normalizing factor is at most one: `(1 + x)⁻¹ * x ≤ 1` in `ℝ≥0∞`, also for `x = ∞`. -/
lemma inv_one_add_mul_le_one (x : ℝ≥0∞) : (1 + x)⁻¹ * x ≤ 1 := by
  by_cases hx : x = ⊤
  · simp [hx]
  · calc (1 + x)⁻¹ * x ≤ (1 + x)⁻¹ * (1 + x) := by
          gcongr
          exact le_add_self
      _ = 1 := ENNReal.inv_mul_cancel (by simp) (by simp [hx])

/-- Normalized restriction of an identity of restricted measures. If `ν.restrict D = ofReal a • μ.restrict D` with
`0 < a` and `μ D < ∞`, then `((1 + ν D)⁻¹ • ν.restrict D).restrict D = ofReal a' • μ.restrict D` for some `a' > 0`. -/
lemma exists_pos_normalized_restrict {D : Set ℂ} (hD : MeasurableSet D) {ν μ : Measure ℂ} {a : ℝ} (ha : 0 < a)
    (hμ : μ D ≠ ⊤) (h : ν.restrict D = ENNReal.ofReal a • μ.restrict D) :
    ∃ a' : ℝ, 0 < a' ∧ ((1 + ν D)⁻¹ • ν.restrict D).restrict D = ENNReal.ofReal a' • μ.restrict D := by
  have hνD : ν D ≠ ⊤ := by
    have h1 : (ν.restrict D) D = ν D := Measure.restrict_apply_self ν D
    rw [← h1, h, Measure.smul_apply, Measure.restrict_apply_self, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hμ
  have hinv0 : (1 + ν D)⁻¹ ≠ 0 := by simp [hνD]
  have hinvt : (1 + ν D)⁻¹ ≠ ⊤ := by simp
  refine ⟨((1 + ν D)⁻¹).toReal * a, mul_pos (ENNReal.toReal_pos hinv0 hinvt) ha, ?_⟩
  rw [Measure.restrict_smul, Measure.restrict_restrict hD, Set.inter_self, h, smul_smul]
  congr 1
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hinvt]

/-- **Finite local measure decoder (derived).** From the raw local measure decoder `κ₀` of `LocalMeasureKernelStmt`,
there is a finite kernel `κ` on the observation space of the disc `ball c₂ r₂` (hence `IsSFiniteKernel κ`) that satisfies
both clauses of `LocalMeasureKernelStmt` (the unrooted clause at `α < lqgQ γ` and the rooted clause for a.e. root `z` in
`ball c₁ r₁`), with positive scalars that may depend on the observation. The clauses are stated for `κ` with the same
quantifiers as in `LocalMeasureKernelStmt`. -/
theorem exists_finite_localMeasureKernel {γ : ℝ} {c₁ c₂ : ℂ} {r₁ r₂ : ℝ}
    (hκ : LocalMeasureKernelStmt.{u} γ c₁ c₂ r₁ r₂)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hr₁ : 0 < r₁) (hr₂ : 0 < r₂)
    (h12 : closedBall c₁ r₁ ⊆ ball c₂ r₂) (h21 : closedBall c₂ r₂ ⊆ ball (0 : ℂ) 1)
    (h0 : (0 : ℂ) ∉ closedBall c₂ r₂) :
    ∃ κ : Kernel (LocalObs c₂ r₂) ℂ, IsFiniteKernel κ ∧
      (∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
        ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
          (κ (localMeanZeroObs α (ball c₂ r₂) (hC ω))).restrict (ball c₂ r₂) =
            ENNReal.ofReal a • (μ ω).restrict (ball c₂ r₂)) ∧
      (∀ α : ℝ, α < lqgQ γ → ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
        IsWholePlaneGFF P hC hcirc →
        ∀ᵐ z ∂(volume.restrict (ball c₁ r₁)), ∀ μz : Ω → Measure ℂ,
          IsLQGMeasure P γ (fun ω => addCircleAverage (fieldCircleAverage α (hcirc ω))
            (fun w => -γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖))) μz →
          ∀ᵐ ω ∂P, ∃ a : ℝ, 0 < a ∧
            (κ (campbellReferenceObs γ α (ball c₂ r₂) (hC ω) z).2).restrict (ball c₂ r₂) =
              ENNReal.ofReal a • (μz ω).restrict (ball c₂ r₂)) := by
  obtain ⟨κ₀, hκ₀m, hA, hB⟩ := hκ hγ0 hγ2 hr₁ hr₂ h12 h21 h0
  have hD : MeasurableSet (ball c₂ r₂) := measurableSet_ball
  have hmeas : Measurable fun ℓ : LocalObs c₂ r₂ => κ₀ ℓ (ball c₂ r₂) :=
    (Measure.measurable_coe hD).comp hκ₀m
  let κ : Kernel (LocalObs c₂ r₂) ℂ :=
    ⟨fun ℓ => (1 + κ₀ ℓ (ball c₂ r₂))⁻¹ • (κ₀ ℓ).restrict (ball c₂ r₂), by
      refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
      simp only [Measure.smul_apply, Measure.restrict_apply hs, smul_eq_mul]
      exact ((measurable_const.add hmeas).inv).mul
        ((Measure.measurable_coe (hs.inter hD)).comp hκ₀m)⟩
  have hbound : ∀ ℓ, κ ℓ univ ≤ 1 := by
    intro ℓ
    show ((1 + κ₀ ℓ (ball c₂ r₂))⁻¹ • (κ₀ ℓ).restrict (ball c₂ r₂)) univ ≤ 1
    rw [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
    exact inv_one_add_mul_le_one _
  have hfin : IsFiniteKernel κ := ⟨⟨1, ENNReal.one_lt_top, hbound⟩⟩
  have hlocfin : ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ → μ (ball c₂ r₂) ≠ ⊤ := fun μ _ =>
    ne_top_of_le_ne_top (isCompact_closedBall c₂ r₂).measure_lt_top.ne (measure_mono ball_subset_closedBall)
  refine ⟨κ, hfin, fun α hα Ω _ P _ hC hcirc μ hGFF hμ => ?_, fun α hα Ω _ P _ hC hcirc hGFF => ?_⟩
  · have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ _ (μ ω) := hμ
    filter_upwards [hA α hα Ω P hC hcirc μ hGFF hμ, hμ'] with ω hω hωμ
    obtain ⟨a, ha, heq⟩ := hω
    exact exists_pos_normalized_restrict hD ha (hlocfin (μ ω) hωμ.isLocallyFiniteMeasure) heq
  · filter_upwards [hB α hα Ω P hC hcirc hGFF] with z hz
    intro μz hμz
    have hμz' : ∀ᵐ ω ∂P, IsLQGLimit _ _ (μz ω) := hμz
    filter_upwards [hz μz hμz, hμz'] with ω hω hωμ
    obtain ⟨a, ha, heq⟩ := hω
    exact exists_pos_normalized_restrict hD ha (hlocfin (μz ω) hωμ.isLocallyFiniteMeasure) heq

end HarmonicBalls.FirstPassS11ahFinite

#print axioms HarmonicBalls.FirstPassS11ahFinite.exists_finite_localMeasureKernel
