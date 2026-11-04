import HarmonicBalls.Proofs.Sec6.NonpositiveSingularityNonatomic
import HarmonicBalls.Proofs.Sec8.OpenBallDensity

/-! # Absence of an atom at the logarithmic singularity -/

namespace HarmonicBalls.Section6

open MeasureTheory Filter Metric Set
open scoped Topology ENNReal

universe u

/-- A locally finite LQG limit with a stronger logarithmic singularity forces
any weaker singularity, formed from the same circle averages, to have no atom
at zero. -/
theorem origin_nonatomic_of_stronger_singularity
    {γ α β : ℝ} (hγ : 0 < γ) (hαβ : α < β)
    (hcirc : ℝ → ℂ → ℝ) (μ ν : Measure ℂ)
    (hm : IsLQGLimit γ (fieldCircleAverage α hcirc) μ)
    (hn : IsLQGLimit γ (fieldCircleAverage β hcirc) ν)
    (hc : ∀ k, Continuous (fieldCircleAverage β hcirc (dyadicScale k))) :
    μ {0} = 0 := by
  let : IsLocallyFiniteMeasure μ := hm.isLocallyFiniteMeasure
  let : IsLocallyFiniteMeasure ν := hn.isLocallyFiniteMeasure
  have hmfin : μ {0} ≠ ∞ := isCompact_singleton.measure_lt_top.ne
  have hnfin : ν {0} ≠ ∞ := isCompact_singleton.measure_lt_top.ne
  have hbound (n : ℕ) : (μ {0}).toReal ≤ Real.exp (-γ * n) * (ν {0}).toReal := by
    let R : ℝ := Real.exp (-((n : ℝ) + 1) / (β - α))
    have hR : 0 < R := Real.exp_pos _
    have hlogR : Real.log R = -((n : ℝ) + 1) / (β - α) := Real.log_exp _
    let f : ℂ → ℝ := fun _ => -(n : ℝ)
    have hf : Continuous f := continuous_const
    have hw := isLQGLimit_addCircleAverage hn hc f hf
    have hc' : ∀ k, Continuous (addCircleAverage (fieldCircleAverage β hcirc) f (dyadicScale k)) := by
      intro k
      change Continuous (fun z => fieldCircleAverage β hcirc (dyadicScale k) z +
        Real.circleAverage (fun _ : ℂ => -(n : ℝ)) z (dyadicScale k))
      simp only [Real.circleAverage_const]
      exact (hc k).add continuous_const
    have hloc : ∀ L : Set ℂ, IsCompact L → L ⊆ ball (0 : ℂ) R →
        ∀ᶠ k : ℕ in atTop, ∀ z ∈ L,
          fieldCircleAverage α hcirc (dyadicScale k) z ≤
            addCircleAverage (fieldCircleAverage β hcirc) f (dyadicScale k) z := by
      intro L _ hL
      filter_upwards [(tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
        (Iio_mem_nhds hR)] with k hk z hz
      have hr := dyadicScale_pos k
      have hzR : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hL hz
      have hmax : 0 < max (dyadicScale k) ‖z‖ := lt_max_of_lt_left hr
      have hmaxR : max (dyadicScale k) ‖z‖ ≤ R := max_le hk.le hzR.le
      have hl : Real.log (max (dyadicScale k) ‖z‖) ≤ Real.log R := Real.log_le_log hmax hmaxR
      have hd : 0 < β - α := sub_pos.mpr hαβ
      have hp : (β - α) * Real.log (max (dyadicScale k) ‖z‖) ≤ -((n : ℝ) + 1) := by
        calc
          _ ≤ (β - α) * Real.log R := mul_le_mul_of_nonneg_left hl hd.le
          _ = -((n : ℝ) + 1) := by rw [hlogR]; field_simp
      rw [fieldCircleAverage_eq _ _ hr, addCircleAverage, Real.circleAverage_const,
        fieldCircleAverage_eq _ _ hr]
      nlinarith
    have hle := isLQGLimit_measure_compact_le hγ.le hm hw hc'
      (U := ball (0 : ℂ) R) (K := {0}) isOpen_ball isCompact_singleton
      (by simpa using hR) hloc
    change μ {0} ≤ (ν.withDensity (fun _ => ENNReal.ofReal (Real.exp (γ * -(n : ℝ))))) {0} at hle
    rw [withDensity_const, Measure.smul_apply] at hle
    have ht : ENNReal.ofReal (Real.exp (γ * -(n : ℝ))) * ν {0} ≠ ∞ := by
      exact ENNReal.mul_ne_top (by simp) hnfin
    have hreal := ENNReal.toReal_mono ht hle
    simpa [f, ENNReal.toReal_mul, Real.exp_nonneg, mul_neg] using hreal
  have hlim : Tendsto (fun n : ℕ => Real.exp (-γ * n) * (ν {0}).toReal) atTop (𝓝 0) := by
    have ht : Tendsto (fun n : ℕ => -γ * (n : ℝ)) atTop atBot :=
      tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg (neg_lt_zero.mpr hγ)
    simpa using (Real.tendsto_exp_atBot.comp ht).mul_const (ν {0}).toReal
  have hz : (μ {0}).toReal = 0 := le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall hbound)) ENNReal.toReal_nonneg
  rw [ENNReal.toReal_eq_zero_iff] at hz
  exact hz.resolve_right hmfin

/-- Existence at any strictly larger subcritical singularity removes the atom
at zero of the given LQG measure. -/
theorem ae_origin_nonatomic_of_stronger_existence
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α β : ℝ)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαβ : α < β) (hβ : β < lqgQ γ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hE : LQGMeasureExistence P γ β hC hcirc)
    (μ : Ω → Measure ℂ) (hG : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ) : ∀ᵐ ω ∂P, μ ω {0} = 0 := by
  obtain ⟨ν, hν⟩ := hE hG hγ hγ2 hβ
  have hc : ∀ᵐ ω ∂P, ∀ k, Continuous (fieldCircleAverage β (hcirc ω) (dyadicScale k)) :=
    ae_all_iff.mpr (fun k => hG.ae_continuous_fieldCircleAverage β (dyadicScale_pos k))
  filter_upwards [hμ, hν, hc] with ω hm hn hc
  exact origin_nonatomic_of_stronger_singularity hγ hαβ (hcirc ω) (μ ω) (ν ω) hm hn hc

/-- The whole-plane mass bound and existence at subcritical singularity
strengths imply non-atomicity, including at the logarithmic singularity. -/
theorem lqgMeasureNonatomic_of_existence
    (hS : WholePlaneScaledBallMassStep.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hE : ∀ β, LQGMeasureExistence P γ β hC hcirc) :
    LQGMeasureNonatomic P γ α hC hcirc := by
  intro hG hγ hγ2 hα μ hμ
  let β := (α + lqgQ γ) / 2
  have hαβ : α < β := by dsimp [β]; linarith
  have hβ : β < lqgQ γ := by dsimp [β]; linarith
  filter_upwards [ae_origin_nonatomic_of_stronger_existence P γ α β hγ hγ2 hαβ hβ
      hC hcirc (hE β) μ hG hμ,
    ae_singular_nonatomic_off_origin_of_scaledBallMass hS P γ α hγ hγ2 hα
      hC hcirc (hE 0) μ hG hμ] with ω h0 hoff z
  by_cases hz : z = 0
  · simpa [hz] using h0
  · exact hoff z hz

end HarmonicBalls.Section6
