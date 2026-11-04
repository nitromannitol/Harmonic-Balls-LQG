import HarmonicBalls.Proofs.Sec8.GreenKernelContinuity
import HarmonicBalls.Proofs.Sec8.ExitTimeScaling

/-! # Countable approximation of annular balls

A dense set of admissible centers and rational radii approximate every
admissible ball from inside. This geometric step does not assume that the
measure is finite or assigns zero mass to spheres.
-/

open MeasureTheory Metric Set Filter ProbabilityTheory
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Every positive-radius ball centered in `S` contains a ball with center
in a prescribed dense subset of `S` and rational radius arbitrarily close to
the original radius from below. -/
theorem exists_rational_ball_subset_of_dense {X : Type*} [PseudoMetricSpace X]
    (S : Set X) (D : Set S) (hD : Dense D) (z : S) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) :
    ∃ z' : S, z' ∈ D ∧ ∃ q : ℚ,
      0 < (q : ℝ) ∧ r - ε < q ∧ (q : ℝ) < r ∧
        ball (z' : X) (q : ℝ) ⊆ ball (z : X) r := by
  let δ : ℝ := min ε r / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδε : 4 * δ ≤ ε := by dsimp [δ]; linarith [min_le_left ε r]
  have hδr : 4 * δ ≤ r := by dsimp [δ]; linarith [min_le_right ε r]
  obtain ⟨z', hdist, hz'D⟩ := (Metric.dense_iff.mp hD) z δ hδ
  have hdist' : dist (z : X) (z' : X) < δ := by
    simpa only [Metric.mem_ball, dist_comm, Subtype.dist_eq] using hdist
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn (show r - 2 * δ < r - δ by linarith)
  refine ⟨z', hz'D, q, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · intro x hx
    rw [mem_ball] at hx ⊢
    have ht := dist_triangle x (z' : X) (z : X)
    rw [dist_comm (z' : X) (z : X)] at ht
    linarith

/-- A dense family of centers and rational radii gives the same annular
ball-mass infimum as the original uncountable family. -/
theorem annulusBallMassSize_eq_dense_rational (μ : Measure ℂ) (β ρ : ℝ)
    (x₀ : ℂ) (hρ : 0 < ρ)
    (D : Set (annulus x₀ (ρ / 2) ρ)) (hD : Dense D) :
    annulusBallMassSize μ β ρ x₀ =
      ⨅ z : D, ⨅ q : ℚ, ⨅ (_ : (q : ℝ) ∈ Ioo 0 (ρ / 4)),
        μ (ball (z.1 : ℂ) (q : ℝ)) / ENNReal.ofReal (((q : ℝ) / ρ) ^ β) := by
  let F : ℝ≥0∞ := ⨅ z : D, ⨅ q : ℚ, ⨅ (_ : (q : ℝ) ∈ Ioo 0 (ρ / 4)),
    μ (ball (z.1 : ℂ) (q : ℝ)) / ENNReal.ofReal (((q : ℝ) / ρ) ^ β)
  change annulusBallMassSize μ β ρ x₀ = F
  apply le_antisymm
  · refine le_iInf fun z => le_iInf fun q => le_iInf fun hq => ?_
    exact iInf_le_of_le (z.1 : ℂ) (iInf_le_of_le z.1.2
      (iInf_le_of_le (q : ℝ) (iInf_le_of_le hq le_rfl)))
  · unfold annulusBallMassSize
    refine le_iInf fun z => le_iInf fun hz => le_iInf fun r => le_iInf fun hr => ?_
    have hε (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hex (n : ℕ) := exists_rational_ball_subset_of_dense
      (annulus x₀ (ρ / 2) ρ) D hD ⟨z, hz⟩ hr.1 (hε n)
    choose zn hzn qn hqpos hqlo hqhi hsub using hex
    have hqT : Tendsto (fun n => (qn n : ℝ)) atTop (𝓝 r) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le
        (show Tendsto (fun n : ℕ => r - 1 / ((n : ℝ) + 1)) atTop (𝓝 r) by
          simpa using (tendsto_const_nhds.sub
            (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))))
        tendsto_const_nhds
      · intro n; exact (hqlo n).le
      · intro n; exact (hqhi n).le
    have hpT : Tendsto (fun n => ENNReal.ofReal (((qn n : ℝ) / ρ) ^ β)) atTop
        (𝓝 (ENNReal.ofReal ((r / ρ) ^ β))) := by
      apply ENNReal.tendsto_ofReal
      simpa only [Function.comp_def] using
        (Real.continuousAt_rpow_of_ne (r / ρ, β) (div_pos hr.1 hρ).ne').tendsto.comp
          ((hqT.div_const ρ).prodMk_nhds tendsto_const_nhds)
    have hlim := ENNReal.Tendsto.const_div (a := μ (ball z r)) hpT (Or.inl ENNReal.ofReal_ne_top)
    apply ge_of_tendsto hlim
    filter_upwards [] with n
    have hqn : (qn n : ℝ) ∈ Ioo 0 (ρ / 4) := ⟨hqpos n, lt_trans (hqhi n) hr.2⟩
    calc
      F ≤ μ (ball (zn n : ℂ) (qn n : ℝ)) / ENNReal.ofReal (((qn n : ℝ) / ρ) ^ β) :=
        iInf_le_of_le ⟨zn n, hzn n⟩ (iInf_le_of_le (qn n) (iInf_le_of_le hqn le_rfl))
      _ ≤ μ (ball z r) / ENNReal.ofReal (((qn n : ℝ) / ρ) ^ β) := by
        gcongr
        exact hsub n

/-- The annular ball-mass size is measurable as a function of the measure. -/
theorem measurable_annulusBallMassSize (β ρ : ℝ) (x₀ : ℂ) (hρ : 0 < ρ) :
    Measurable (fun μ : Measure ℂ => annulusBallMassSize μ β ρ x₀) := by
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense (annulus x₀ (ρ / 2) ρ)
  let : Countable D := hDc.to_subtype
  have hm : Measurable (fun μ : Measure ℂ =>
      ⨅ z : D, ⨅ q : ℚ, ⨅ (_ : (q : ℝ) ∈ Ioo 0 (ρ / 4)),
        μ (ball (z.1 : ℂ) (q : ℝ)) / ENNReal.ofReal (((q : ℝ) / ρ) ^ β)) := by
    apply Measurable.iInf
    intro z
    apply Measurable.iInf
    intro q
    apply Measurable.iInf
    intro hq
    exact (Measure.measurable_coe isOpen_ball.measurableSet).div measurable_const
  convert hm using 1
  funext μ
  exact annulusBallMassSize_eq_dense_rational μ β ρ x₀ hρ D hD

/-- The normalized annular ball-mass size is measurable. -/
theorem measurable_annulusBallMassSize_ratio (β ρ : ℝ) (x₀ : ℂ) (hρ : 0 < ρ) :
    Measurable (fun μ : Measure ℂ => annulusBallMassSize μ β ρ x₀ /
      μ (annulus x₀ (ρ / 4) (2 * ρ))) := by
  exact (measurable_annulusBallMassSize β ρ x₀ hρ).div
    (Measure.measurable_coe (isOpen_ball.sdiff isClosed_closedBall).measurableSet)

/-- At the origin, measurable individual good-annulus events imply that the
very-good-annulus event is measurable. -/
theorem measurableSet_isVeryGoodAnnulus_zero_of_good_events
    (βminus ρ : ℝ) (hρ : 0 < ρ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ : ℝ)
    (hgood : ∀ (n : ℕ) (j k : ℤ) (l : ℕ), MeasurableSet {μ : Measure ℂ |
      IsGoodAnnulus μ (ρ * (7 : ℝ)⁻¹ ^ l)
        (((dyadicScale n * ρ / 100 : ℝ) : ℂ) * ((j : ℂ) + (k : ℂ) * Complex.I)) a b}) :
    MeasurableSet {μ : Measure ℂ |
      IsVeryGoodAnnulus μ βminus ρ 0 N₀ a b C₁m C₁p C₂m C₂p C₃} :=
  measurableSet_isVeryGoodAnnulus_zero_of_measurable_parts βminus ρ hρ N₀
    a b C₁m C₁p C₂m C₂p C₃ (measurable_annulusBallMassSize_ratio βminus ρ 0 hρ) hgood

open Classical in
/-- Stationarity of the joint indicators follows from measurability of the
individual good-annulus events and the staged LQG invariance inputs. -/
theorem identDistrib_lqg_veryGoodComparable_sequence_of_good_events
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hgood : ∀ (s n : ℕ) (j k : ℤ) (l : ℕ), MeasurableSet {ν : Measure ℂ |
      IsGoodAnnulus ν (dyadicScale s * (7 : ℝ)⁻¹ ^ l)
        (((dyadicScale n * dyadicScale s / 100 : ℝ) : ℂ) *
          ((j : ℂ) + (k : ℂ) * Complex.I)) a b}) :
    IdentDistrib
      (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0)
      (fun ω n => if IsVeryGoodAnnulus (μ ω) β (dyadicScale (1 + n)) 0 N₀
        a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) (1 + n) 0 m then (1 : ℝ) else 0)
      P P := by
  apply identDistrib_lqg_veryGoodComparable_sequence_of_measurable hγ hγ2 hα
    hGFF hμ hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m
  intro s
  exact measurableSet_isVeryGoodAnnulus_zero_of_good_events β (dyadicScale s)
    (dyadicScale_pos s) N₀ a b C₁m C₁p C₂m C₂p C₃ (hgood s)

end HarmonicBalls
