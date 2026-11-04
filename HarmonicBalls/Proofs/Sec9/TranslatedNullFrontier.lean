import HarmonicBalls.Proofs.Sec9.BoundaryExteriorDefect
import Mathlib.MeasureTheory.Group.Prod

/-! # Generic translations of planar null sets -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter

universe u

/-- For any s-finite measure, almost every translate of a planar Lebesgue-null
measurable set is null for that measure. -/
theorem ae_measure_translate_eq_zero_of_volume_eq_zero
    (μ : Measure ℂ) [SFinite μ] {F : Set ℂ} (hF : MeasurableSet F)
    (hnull : volume F = 0) :
    ∀ᵐ v : ℂ ∂volume, μ ((fun x : ℂ => v + x) '' F) = 0 := by
  let B : Set (ℂ × ℂ) := {p | p.2 - p.1 ∈ F}
  have hB : MeasurableSet B := hF.preimage (measurable_snd.sub measurable_fst)
  have hprod : ((volume : Measure ℂ).prod μ) B = 0 := by
    rw [Measure.prod_apply_symm hB]
    have hsec : ∀ x : ℂ, (volume : Measure ℂ) ((fun v : ℂ => x - v) ⁻¹' F) = 0 := by
      intro x
      rw [(Measure.measurePreserving_sub_left (volume : Measure ℂ) x).measure_preimage hF.nullMeasurableSet]
      exact hnull
    change (∫⁻ x, (volume : Measure ℂ) ((fun v : ℂ => x - v) ⁻¹' F) ∂μ) = 0
    simp only [hsec, lintegral_zero]
  have hae := Measure.measure_ae_null_of_prod_null hprod
  filter_upwards [hae] with v hv
  have heq : ((fun x : ℂ => v + x) '' F) = {x : ℂ | x - v ∈ F} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [add_comm] using hy
    · intro hx
      exact ⟨x - v, hx, by abel⟩
  simpa [B, heq] using hv

/-- Almost surely, for each planar Lebesgue-null measurable set, almost every
translate is null for the Liouville measure. The exceptional translations may
depend on the realization and on the set. -/
theorem ae_lqgMeasure_translate_eq_zero_of_volume_eq_zero
    {γ α₀ : ℝ} {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ F : Set ℂ, MeasurableSet F → volume F = 0 →
      ∀ᵐ v : ℂ ∂volume, μ ω ((fun x : ℂ => v + x) '' F) = 0 := by
  filter_upwards [hμ] with ω hlim
  let : IsLocallyFiniteMeasure (μ ω) := hlim.isLocallyFiniteMeasure
  intro F hF hnull
  exact ae_measure_translate_eq_zero_of_volume_eq_zero (μ ω) hF hnull

/-- For each Lebesgue-null measurable planar set and almost every translate,
weak uniqueness holds for all comparison balls whose common frontier is
contained in that translate. -/
theorem ae_subharmonicBall_sandwich_of_translated_null_frontier
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ F : Set ℂ, MeasurableSet F → volume F = 0 →
      ∀ᵐ v : ℂ ∂volume, ∀ (A : Set ℂ) (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
        z ∈ ball (0 : ℂ) R → closure A ⊆ ball 0 R →
        IsSubharmonicBall (μ ω) A z → μ ω A = ENNReal.ofReal t →
        frontier (cluster (μ ω) R z t) ∩ frontier A ⊆ (fun x : ℂ => v + x) '' F →
        cluster (μ ω) R z t ⊆ A ∧ A ⊆ regularizedCluster (μ ω) R z t ∧
        (IsRegularOpen A → regularizedCluster (μ ω) R z t = A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_lqgMeasure_translate_eq_zero_of_volume_eq_zero hμ,
    ae_subharmonicBall_uniqueness_of_null_common_frontier hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω htrans hcompare
  intro F hF hnull
  filter_upwards [htrans F hF hnull] with v hv
  intro A z t R ht hR hz hcl hA hmass hcover
  exact hcompare A z t R ht hR hz hcl hA hmass (measure_mono_null hcover hv)

/-- A planar set with Lebesgue-null frontier has the weak-uniqueness
inclusions at almost every translate whenever that translate is a
subharmonic ball. The exceptional translations can depend on the set and on
the Liouville measure, but not on the pole, mass or ambient disc. -/
theorem ae_subharmonicBall_sandwich_for_generic_translate
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ A : Set ℂ, volume (frontier A) = 0 →
      ∀ᵐ v : ℂ ∂volume, ∀ (z : ℂ) (t R : ℝ), 0 < t → 0 < R →
        z ∈ ball (0 : ℂ) R → closure ((fun x : ℂ => v + x) '' A) ⊆ ball 0 R →
        IsSubharmonicBall (μ ω) ((fun x : ℂ => v + x) '' A) z →
        μ ω ((fun x : ℂ => v + x) '' A) = ENNReal.ofReal t →
        cluster (μ ω) R z t ⊆ (fun x : ℂ => v + x) '' A ∧
        (fun x : ℂ => v + x) '' A ⊆ regularizedCluster (μ ω) R z t ∧
        (IsRegularOpen ((fun x : ℂ => v + x) '' A) →
          regularizedCluster (μ ω) R z t = (fun x : ℂ => v + x) '' A) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_subharmonicBall_sandwich_of_translated_null_frontier hI2
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hcompare
  intro A hnull
  filter_upwards [hcompare (frontier A) isClosed_frontier.measurableSet hnull] with v hv
  intro z t R ht hR hz hcl hA hmass
  apply hv ((fun x : ℂ => v + x) '' A) z t R ht hR hz hcl hA hmass
  have hfront : (fun x : ℂ => v + x) '' frontier A =
      frontier ((fun x : ℂ => v + x) '' A) := (Homeomorph.addLeft v).image_frontier A
  rw [hfront]
  exact inter_subset_right

end HarmonicBalls
