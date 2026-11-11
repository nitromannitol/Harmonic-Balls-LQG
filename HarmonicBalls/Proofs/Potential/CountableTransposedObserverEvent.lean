import HarmonicBalls.Proofs.Potential.FiniteSourceObservationIntegrability
import HarmonicBalls.Proofs.Potential.GreenPotentialExceptionalSet

/-!
# A common exceptional set for countably many transposed potentials

The potential-theoretic infrastructure uses work of Leonardo Bonanno.
The extended kernel retains its infinite diagonal value.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- Local upper growth gives one measurable null set for a countable family. -/
theorem exists_countable_transposed_observer_exceptional_set
    {μ : Measure ℂ} [IsLocallyFiniteMeasure μ]
    (hup : ∀ R : ℝ, 0 < R → ∃ r₀ β : ℝ, 0 < r₀ ∧ 0 < β ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ (ball z r) ≤ ENNReal.ofReal (r ^ β))
    (V : ℕ → Set ℂ) (ν : ℕ → Measure ℂ)
    (hV : ∀ n, IsOpen (V n)) (hVb : ∀ n, Bornology.IsBounded (V n))
    (hf : ∀ n, IsFiniteMeasure (ν n)) (hν : ∀ n, ∀ᵐ y ∂ν n, y ∈ V n) :
    ∃ N : Set ℂ, MeasurableSet N ∧ μ N = 0 ∧
      ∀ n x, x ∈ V n → x ∉ N →
        Integrable (fun y => greenFunction (V n) y x) (ν n) ∧
        (∫⁻ y, greenKernelExtended (V n) y x ∂ν n) < ⊤ ∧
        (∫⁻ y, greenKernelExtended (V n) y x ∂ν n) =
          ENNReal.ofReal (∫ y, greenFunction (V n) y x ∂ν n) := by
  classical
  have ha : ∀ n, ∀ᵐ x ∂μ, x ∈ V n →
      Integrable (fun y => greenFunction (V n) y x) (ν n) ∧ ν n {x} = 0 := by
    intro n
    let : IsFiniteMeasure (ν n) := hf n
    obtain ⟨r, hr⟩ := (hVb n).subset_ball (0 : ℂ)
    let R := max r 1
    have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    have hsub : V n ⊆ ball (0 : ℂ) R := hr.trans (ball_subset_ball (le_max_left _ _))
    obtain ⟨r₀, β, hr₀, hβ, hg⟩ := hup R hR
    have hatom := ae_measure_singleton_eq_zero_of_upper (ν := ν n) hR hr₀ hβ hg
      (measure_ball_lt_top (μ := μ)).ne
    have hatom' : ∀ᵐ x ∂μ.restrict (V n), ν n {x} = 0 :=
      Filter.Eventually.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)) hatom
    exact (ae_restrict_iff' (hV n).measurableSet).1
      ((finiteSource_transposedGreen_observation_integrability hup (hV n) (hVb n) (hν n)).1.and hatom')
  have hall : ∀ᵐ x ∂μ, ∀ n, x ∈ V n →
      Integrable (fun y => greenFunction (V n) y x) (ν n) ∧ ν n {x} = 0 :=
    ae_all_iff.2 ha
  obtain ⟨N, hsub, hNm, hN⟩ := exists_measurable_superset_of_null (ae_iff.1 hall)
  refine ⟨N, hNm, hN, ?_⟩
  intro n x hx hxN
  have hxgood : ∀ n, x ∈ V n →
      Integrable (fun y => greenFunction (V n) y x) (ν n) ∧ ν n {x} = 0 := by
    by_contra h; exact hxN (hsub h)
  obtain ⟨hi, hatom⟩ := hxgood n hx
  have hae : ∀ᵐ y ∂ν n, y ≠ x := ae_iff.mpr (by simpa using hatom)
  have heq : (∫⁻ y, greenKernelExtended (V n) y x ∂ν n) =
      ENNReal.ofReal (∫ y, greenFunction (V n) y x ∂ν n) := by
    calc
      (∫⁻ y, greenKernelExtended (V n) y x ∂ν n) =
          ∫⁻ y, ENNReal.ofReal (greenFunction (V n) y x) ∂ν n := by
            apply lintegral_congr_ae
            filter_upwards [hae] with y hy
            simp [greenKernelExtended, Ne.symm hy]
      _ = ENNReal.ofReal (∫ y, greenFunction (V n) y x ∂ν n) :=
        (ofReal_integral_eq_lintegral_ofReal hi
          (Eventually.of_forall fun y => greenFunction_nonneg (hVb n) y x)).symm
  exact ⟨hi, heq ▸ ENNReal.ofReal_lt_top, heq⟩

universe u

/-- I2 first selects a field event, on which every countable family admits
its own common observer null set. -/
theorem ae_lqg_countable_transposed_observer_exceptional_set
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (V : ℕ → Set ℂ) (ν : ℕ → Measure ℂ),
      (∀ n, IsOpen (V n)) → (∀ n, Bornology.IsBounded (V n)) →
      (∀ n, IsFiniteMeasure (ν n)) → (∀ n, ∀ᵐ y ∂ν n, y ∈ V n) →
      ∃ N : Set ℂ, MeasurableSet N ∧ μ ω N = 0 ∧
        ∀ n x, x ∈ V n → x ∉ N →
          Integrable (fun y => greenFunction (V n) y x) (ν n) ∧
          (∫⁻ y, greenKernelExtended (V n) y x ∂ν n) < ⊤ ∧
          (∫⁻ y, greenKernelExtended (V n) y x ∂ν n) =
            ENNReal.ofReal (∫ y, greenFunction (V n) y x ∂ν n) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  have ha : 0 < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) := by
    apply lt_min
    · have : 0 < 2 - γ := by linarith
      positivity
    · exact mul_pos hγ (sub_pos.mpr hα)
  let β : ℝ := min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) / 2
  have hβ : 0 < β := by dsimp [β]; linarith
  have hβlt : β < min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) := by
    dsimp [β]; linarith
  let B : ℝ := max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1
  have hB : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < B := by
    dsimp [B]; linarith
  filter_upwards [hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ, hμ] with ω hgrowth hlocal
  let : IsLocallyFiniteMeasure (μ ω) := hlocal.isLocallyFiniteMeasure
  have hup : ∀ R : ℝ, 0 < R → ∃ r₀ b : ℝ, 0 < r₀ ∧ 0 < b ∧
      ∀ r, 0 < r → r < r₀ → ∀ z ∈ ball (0 : ℂ) R,
        μ ω (ball z r) ≤ ENNReal.ofReal (r ^ b) := by
    intro R hR
    obtain ⟨r₀, hr₀, hg⟩ := hgrowth R hR β B hβ hβlt hB
    exact ⟨r₀, β, hr₀, hβ, fun r hr hrr z hz => (hg r hr hrr z hz).2⟩
  exact fun V ν hV hVb hf hν =>
    exists_countable_transposed_observer_exceptional_set hup V ν hV hVb hf hν


end HarmonicBalls
