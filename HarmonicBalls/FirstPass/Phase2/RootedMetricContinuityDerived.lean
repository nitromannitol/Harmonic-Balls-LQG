import HarmonicBalls.FirstPass.S11r.Frozen

/-!
# Continuity of the rooted physical metric at an insertion, through a confined single-insertion estimate



Target: `RootedPhysicalMetricContinuousAtInsertionFrozen` (FirstPass/S11r/Frozen.lean:115-124).

Proved here, with no new mathematics:
* `weylScalingIn D U ξ f u v`: the Weyl-scaled distance of `D` by `ξ f` restricted to paths whose image lies in `U`
  (the confined-path weight of route step (3)). It dominates `weylScaling` (Defs/LQGMetric.lean:107).
* `weylScalingIn_le_mul_of_abs_sub_le`: on the confining set `U`, a bounded change of the weight changes the confined
  distance by at most the constant factor `e^{|ξ| M}`.
* `rootedPhysicalMetricContinuousAtInsertion_of_confined`: the frozen statement follows from the named hypothesis
  `ConfinedSingleInsertionWeightStmt`, the single-insertion confined estimate with weight `-γ log|· - z|`.

NOT proved here (BLOCKED-STEP): `ConfinedSingleInsertionWeightStmt` is taken as an explicit hypothesis. It is the
confined-path output of the annular proof of Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.17
(printed pp. 43-44, eq. (3.56)), with insertion strength `γ` at `z`. Step (2) of the route cites it and gives no
written argument for its confinement. The unconfined continuity (metric induces the Euclidean topology) is clause I of
`LQGMetricFieldAxioms` (Proposed/LQG.lean) only at the insertion point `0`; it does not give confined paths.
-/

namespace HarmonicBalls

open MeasureTheory Filter Metric Set
open scoped ENNReal

universe u

/-- Confined Weyl-scaled distance: the infimum of the Weyl-scaled integrals `∫_0^T e^{ξ f(p t)} dt` over the paths
`p : [0, T] → ℂ` parametrized by `D`-length, from `u` to `v`, whose image lies in `U`. The extra constraint
`p([0, T]) ⊆ U` makes it dominate `weylScaling D ξ f u v` (`weylScaling_le_weylScalingIn`). -/
noncomputable def weylScalingIn (D : ℂ → ℂ → ℝ) (U : Set ℂ) (ξ : ℝ) (f : ℂ → ℝ) (u v : ℂ) : ℝ≥0∞ :=
  ⨅ (T : ℝ) (p : ℝ → ℂ) (_ : IsLengthParametrized D p T) (_ : p 0 = u) (_ : p T = v)
    (_ : ∀ t ∈ Icc 0 T, p t ∈ U),
    ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t)))

/-- Confinement only removes admissible paths, so the confined distance dominates the unconfined one. -/
theorem weylScaling_le_weylScalingIn (D : ℂ → ℂ → ℝ) (U : Set ℂ) (ξ : ℝ) (f : ℂ → ℝ) (u v : ℂ) :
    weylScaling D ξ f u v ≤ weylScalingIn D U ξ f u v := by
  unfold weylScaling weylScalingIn
  refine le_iInf fun T => le_iInf fun p => le_iInf fun hp => le_iInf fun h0 => le_iInf fun hT =>
    le_iInf fun hU => ?_
  exact (((((iInf_le _ T).trans (iInf_le _ p)).trans (iInf_le _ hp)).trans (iInf_le _ h0)).trans
    (iInf_le _ hT))

/-- On the confining set `U`, a bounded perturbation `|f - g| ≤ M` of the weight multiplies the confined distance
by at most `e^{|ξ| M}`. -/
theorem weylScalingIn_le_mul_of_abs_sub_le (D : ℂ → ℂ → ℝ) (U : Set ℂ) (ξ : ℝ) (f g : ℂ → ℝ) {M : ℝ}
    (hfg : ∀ w ∈ U, |f w - g w| ≤ M) (u v : ℂ) :
    weylScalingIn D U ξ f u v ≤ ENNReal.ofReal (Real.exp (|ξ| * M)) * weylScalingIn D U ξ g u v := by
  have hK : ENNReal.ofReal (Real.exp (|ξ| * M)) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hK0 : ENNReal.ofReal (Real.exp (|ξ| * M)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hint : ∀ (T : ℝ) (p : ℝ → ℂ), (∀ t ∈ Icc 0 T, p t ∈ U) →
      ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) ≤
        ENNReal.ofReal (Real.exp (|ξ| * M)) *
          ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * g (p t))) := by
    intro T p hpU
    rw [← lintegral_const_mul' _ _ hK]
    refine setLIntegral_mono' measurableSet_Icc fun t ht => ?_
    have hw := hfg (p t) (hpU t ht)
    have h1 : ξ * f (p t) - ξ * g (p t) ≤ |ξ| * M := by
      rw [← mul_sub]
      calc ξ * (f (p t) - g (p t)) ≤ |ξ * (f (p t) - g (p t))| := le_abs_self _
        _ = |ξ| * |f (p t) - g (p t)| := abs_mul _ _
        _ ≤ |ξ| * M := mul_le_mul_of_nonneg_left hw (abs_nonneg _)
    have h2 : Real.exp (ξ * f (p t)) ≤ Real.exp (|ξ| * M) * Real.exp (ξ * g (p t)) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    exact (ENNReal.ofReal_le_ofReal h2).trans (ENNReal.ofReal_mul (Real.exp_pos _).le).le
  unfold weylScalingIn
  simp only [ENNReal.mul_iInf_of_ne hK0 hK]
  refine iInf_mono fun T => iInf_mono fun p => iInf_mono fun hp => iInf_mono fun h0 =>
    iInf_mono fun hT => iInf_mono fun hU => ?_
  exact hint T p hU

/-- BLOCKED-STEP (named hypothesis, not proved here): the confined single-insertion estimate. For a whole-plane GFF
`hC`, an LQG metric `𝔇` and an insertion of strength `γ ∈ (0, 2)` at `z ≠ 0`, almost surely, for every radius `ρ > 0`,
the confined distance with weight `-γ log|· - z|` tends to `0` as `x → z`.
Source: Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380v2, Proposition 3.17 (printed p. 43, eq. (3.56)) and its
annular proof (pp. 43-44), with insertion strength `γ` at `z`. -/
def ConfinedSingleInsertionWeightStmt : Prop :=
  ∀ (γ ξ : ℝ) (z : ℂ), 0 < γ → γ < 2 → z ≠ 0 →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc →
      ∀ (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), IsLQGMetric γ ξ 𝔇 →
      ∀ᵐ ω ∂P, ∀ ρ : ℝ, 0 < ρ →
        Tendsto (fun x => weylScalingIn (𝔇 (hC ω)) (ball z ρ) ξ (fun w => -γ * Real.log ‖w - z‖) x z)
          (nhds z) (nhds 0)

/-- The rooted physical metric is continuous at an insertion, almost surely, from the confined single-insertion
estimate `ConfinedSingleInsertionWeightStmt`. On the ball `B(z, ‖z‖/2)`, which avoids `0`, the frozen weight equals
`-γ log|· - z|` plus a bounded function, so the frozen distance is squeezed between `0` and a constant multiple of the
confined distance of the single insertion. -/
theorem rootedPhysicalMetricContinuousAtInsertion_of_confined (hConf : ConfinedSingleInsertionWeightStmt.{u}) :
    RootedPhysicalMetricContinuousAtInsertionFrozen.{u} := by
  intro γ ξ α z hγ0 hγ2 _ hz Ω _ P _ hC hcirc hgff 𝔇 h𝔇
  filter_upwards [hConf γ ξ z hγ0 hγ2 hz Ω P hC hcirc hgff 𝔇 h𝔇] with ω hω
  have hznorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hρ : 0 < ‖z‖ / 2 := half_pos hznorm
  have hnear : ∀ x ∈ closedBall z (‖z‖ / 2), ‖z‖ / 2 ≤ ‖x‖ := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    have h1 := norm_sub_norm_le z x
    rw [norm_sub_rev] at h1
    linarith
  have hgcont : ContinuousOn (fun x : ℂ => -α * Real.log ‖x‖ + γ * Real.log (max 1 ‖x‖))
      (closedBall z (‖z‖ / 2)) := by
    refine ContinuousOn.add (continuousOn_const.mul ?_) (continuousOn_const.mul ?_)
    · exact continuous_norm.continuousOn.log fun x hx => (lt_of_lt_of_le hρ (hnear x hx)).ne'
    · exact ((continuous_const.max continuous_norm).log
        fun x => (lt_of_lt_of_le one_pos (le_max_left _ _)).ne').continuousOn
  obtain ⟨M, hM⟩ := (isCompact_closedBall z (‖z‖ / 2)).exists_bound_of_continuousOn hgcont
  have hcomp : ∀ x ∈ ball z (‖z‖ / 2),
      |(-α * Real.log ‖x‖ - γ * Real.log ‖x - z‖ + γ * Real.log (max 1 ‖x‖)) - (-γ * Real.log ‖x - z‖)| ≤ M := by
    intro x hx
    have hx' : x ∈ closedBall z (‖z‖ / 2) := ball_subset_closedBall hx
    have hid : (-α * Real.log ‖x‖ - γ * Real.log ‖x - z‖ + γ * Real.log (max 1 ‖x‖)) -
        (-γ * Real.log ‖x - z‖) = -α * Real.log ‖x‖ + γ * Real.log (max 1 ‖x‖) := by ring
    rw [hid, ← Real.norm_eq_abs]
    exact hM x hx'
  have hlim : Tendsto (fun x => ENNReal.ofReal (Real.exp (|ξ| * M)) *
      weylScalingIn (𝔇 (hC ω)) (ball z (‖z‖ / 2)) ξ (fun w => -γ * Real.log ‖w - z‖) x z)
      (nhds z) (nhds (ENNReal.ofReal (Real.exp (|ξ| * M)) * 0)) :=
    ENNReal.Tendsto.const_mul (hω (‖z‖ / 2) hρ) (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [ball_mem_nhds z hρ] with x hx
  exact (weylScaling_le_weylScalingIn _ _ _ _ _ _).trans
    (weylScalingIn_le_mul_of_abs_sub_le _ _ _ _ _ hcomp x z)

end HarmonicBalls
