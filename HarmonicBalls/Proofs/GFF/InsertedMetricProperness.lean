import HarmonicBalls.FirstPass.Phase2.MetricPropernessProved
import LatticeProb.LQG.WeylScalingAnnulusCrossing

/-!
# Large-scale crossings for a logarithmic insertion

The normalized crossing estimate retains the scale factor and the circle
average needed to compare the metric with a logarithmic Weyl scaling.
The annulus comparison adapts the crossing argument in
`LatticeProb.LQG.WeylScalingAnnulusCrossing`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HarmonicBalls

open LQGMetric LQGMetric.Blueprint LQGMetric.DFGPS.L38 LQGMetric.GM.Tight

/-- Infinitely many annuli have the normalized lower crossing bound for the
whole-plane metric, simultaneously for all pairs crossing each annulus. -/
theorem ae_frequently_normalized_far_crossing {γ : ℝ} {D : DistC → ContMetric}
    (hD : IsWeakLQGMetric γ D (fun r => r ^ (xiGamma γ * Q γ)))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWPGFF h P) :
    ∃ s : ℝ, 0 < s ∧ ∀ᵐ ω ∂P, ∀ m : ℕ, ∃ j : ℕ, m ≤ j ∧
      ∀ x y : ℂ, ‖x‖ ≤ 8 ^ j / 4 → 3 * 8 ^ j / 8 ≤ ‖y‖ →
        s * (8 ^ j : ℝ) ^ (xiGamma γ * Q γ) *
          Real.exp (xiGamma γ * circleAvg (h ω) (8 ^ j) 0) ≤ (D (h ω)).1 (x, y) := by
  obtain ⟨p, hp0, hp1, HA⟩ := ae_frequently_crossing LQGMetric.LM.lmLem3_1a
  obtain ⟨s, hs, Hev⟩ := exists_crossing_event hD (ε := ENNReal.ofReal (1 - p))
    (ENNReal.ofReal_pos.2 (by linarith))
  refine ⟨s, hs, ?_⟩
  have hwp := hh.1
  choose E hEm hEc hEae using fun ρ : {ρ : ℝ // 0 < ρ} => Hev P h hwp ρ.1 ρ.2
  have hEp : ∀ ρ, ENNReal.ofReal p ≤ P (E ρ) := fun ρ => by
    have h1 : (1 : ℝ≥0∞) ≤ P (E ρ) + P (E ρ)ᶜ := by
      rw [← measure_univ (μ := P)]
      exact (measure_mono (union_compl_self (E ρ)).symm.subset).trans (measure_union_le _ _)
    have h2 : ENNReal.ofReal p + ENNReal.ofReal (1 - p) = 1 := by
      rw [← ENNReal.ofReal_add hp0.le (by linarith)]
      simp
    rw [← h2] at h1
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1
      (h1.trans (add_le_add le_rfl (hEc ρ).le))
  have hEall : ∀ᵐ ω ∂P, ∀ j : ℕ, ω ∈ E ⟨8 ^ j, by positivity⟩ →
      ∀ u ∈ sphere (0 : ℂ) (8 ^ j / 4), ∀ v ∈ sphere (0 : ℂ) (3 * 8 ^ j / 8),
        ENNReal.ofReal (s * (8 ^ j : ℝ) ^ (xiGamma γ * Q γ) *
          Real.exp (xiGamma γ * circleAvg (h ω) (8 ^ j) 0)) ≤
          (D (h ω)).internal (LQGMetric.Blueprint.annulus 0 (1 / 8 * 8 ^ j) (1 / 2 * 8 ^ j)) u v :=
    ae_all_iff.2 fun j => hEae ⟨8 ^ j, by positivity⟩
  filter_upwards [HA P h hh E hEm hEp,
    hD.length P h (isGFFPlusCont_of_wp hwp), hEall] with ω hfreq hlen hcross
  intro m
  obtain ⟨j, hj, hjE⟩ := hfreq m
  refine ⟨j, hj, fun x y hx hy => ?_⟩
  have hU : {w : ℂ | 8 ^ j / 4 ≤ ‖w - 0‖ ∧ ‖w - 0‖ ≤ 3 * 8 ^ j / 8} ⊆
      (LQGMetric.Blueprint.annulus 0 (1 / 8 * 8 ^ j) (1 / 2 * 8 ^ j) : Set ℂ) := fun w hw => by
    show 1 / 8 * 8 ^ j < ‖w - 0‖ ∧ ‖w - 0‖ < 1 / 2 * (8 : ℝ) ^ j
    constructor <;> linarith [hw.1, hw.2, show (0 : ℝ) < 8 ^ j by positivity]
  exact le_of_forall_internal_crossing (y := y) hlen (by linarith [show (0 : ℝ) < 8 ^ j by positivity]) hU
    (by simpa only [sub_zero] using hx) (by simpa only [sub_zero] using hy) (hcross j hjE)

/-- A lower bound on the Weyl weight and on the unweighted distance between
annular boundaries gives a lower bound on every crossing of the annulus. -/
theorem ofReal_exp_mul_le_weylScaling_of_annulus_crossing
    {D : ℂ → ℂ → ℝ} {ξ : ℝ} {f : ℂ → ℝ} {r r' m c : ℝ}
    (hrr' : r < r')
    (hm : ∀ z : ℂ, r < ‖z‖ → ‖z‖ < r' → m ≤ ξ * f z)
    (hc : ∀ a b : ℂ, ‖a‖ = r → ‖b‖ = r' → c ≤ D a b)
    {x y : ℂ} (hx : r' ≤ ‖x‖) (hy : ‖y‖ < r) :
    ENNReal.ofReal (Real.exp m * c) ≤ LatticeProb.LQG.weylScaling D ξ f x y := by
  unfold LatticeProb.LQG.weylScaling
  refine le_iInf₂ fun T p => le_iInf₂ fun hp h0 => le_iInf fun hT => ?_
  have h0' : r' ≤ ‖p 0‖ := by rw [h0]; exact hx
  have hTy : ‖p T‖ < r := by rw [hT]; exact hy
  obtain ⟨s₀, s₁, hs₀, hs₀₁, hs₁, hn₀, hn₁, hmid⟩ :=
    LatticeProb.LQG.exists_norm_crossing_interval hp.2.1 hrr' h0' ⟨hp.1, le_rfl⟩ hTy
  have hlen : LatticeProb.LQG.curveLength D p s₀ s₁ = ENNReal.ofReal (s₁ - s₀) :=
    hp.2.2 s₀ s₁ hs₀ hs₀₁ hs₁
  have hcD : ENNReal.ofReal c ≤ ENNReal.ofReal (s₁ - s₀) :=
    (ENNReal.ofReal_le_ofReal (hc _ _ hn₁ hn₀)).trans
      ((LatticeProb.LQG.two_point_le_curveLength (D := D) p hs₀₁).trans hlen.le)
  calc ENNReal.ofReal (Real.exp m * c) = ENNReal.ofReal (Real.exp m) * ENNReal.ofReal c :=
        ENNReal.ofReal_mul (Real.exp_pos m).le
    _ ≤ ENNReal.ofReal (Real.exp m) * ENNReal.ofReal (s₁ - s₀) := by gcongr
    _ = ∫⁻ _ in Ioo s₀ s₁, ENNReal.ofReal (Real.exp m) := by
        rw [setLIntegral_const, Real.volume_Ioo, mul_comm]
    _ ≤ ∫⁻ t in Ioo s₀ s₁, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
        setLIntegral_mono' measurableSet_Ioo fun t ht =>
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hm _ (hmid t ht).1 (hmid t ht).2))
    _ ≤ ∫⁻ t in Icc 0 T, ENNReal.ofReal (Real.exp (ξ * f (p t))) :=
        lintegral_mono_set (Ioo_subset_Icc_self.trans (Icc_subset_Icc hs₀ hs₁))

/-- The normalized crossing estimate holds for the original field and its
metric, with the circle-average factors of the same field. -/
theorem IsWholePlaneGFF.ae_frequently_normalized_far_crossing
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (h𝔇 : IsLQGMetric γ ξ 𝔇) :
    ∃ s : ℝ, 0 < s ∧ ∀ᵐ ω ∂P, ∀ m : ℕ, ∃ j : ℕ, m ≤ j ∧
      ∀ x y : ℂ, ‖x‖ ≤ 8 ^ j / 4 → 3 * 8 ^ j / 8 ≤ ‖y‖ →
        s * (8 ^ j : ℝ) ^ (xiGamma γ * Q γ) *
          Real.exp (xiGamma γ * hcirc ω (8 ^ j) 0) ≤ 𝔇 (hC ω) x y := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨s, hs, hcross⟩ := HarmonicBalls.ae_frequently_normalized_far_crossing
    (isWeakLQGMetric_distributionMetric hγ hγ₂ h𝔇) P (reconstructedGFF hC)
    hh.reconstructedGFF_normalized
  refine ⟨s, hs, ?_⟩
  have hcircle : ∀ᵐ ω ∂P, ∀ j : ℕ,
      hcirc ω (8 ^ j) 0 = circleAvg (reconstructedGFF hC ω) (8 ^ j) 0 :=
    ae_all_iff.2 fun j => hh.ae_circleAvg_reconstructedGFF (by positivity) 0
  filter_upwards [hcross, hh.ae_distributionMetric_reconstructedGFF h𝔇, hcircle] with ω hcross heq hc
  intro m
  obtain ⟨j, hj, hjcross⟩ := hcross m
  refine ⟨j, hj, ?_⟩
  intro x y hx hy
  rw [hc j, ← heq x y]
  exact hjcross x y hx hy

/-- The logarithmic Weyl exponent has a uniform lower bound on a scaled
annulus, for insertions of either sign. -/
theorem log_weight_lower_on_scaled_annulus {ξ α R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz₁ : R / 4 < ‖z‖) (hz₂ : ‖z‖ < 3 * R / 8) :
    -(ξ * α) * Real.log R - |ξ * α| * Real.log 4 ≤
      ξ * (-α * Real.log ‖z‖) := by
  have hz : 0 < ‖z‖ := (show 0 < R / 4 by positivity).trans hz₁
  have hlow : Real.log R - Real.log 4 ≤ Real.log ‖z‖ := by
    have h := Real.log_le_log (show 0 < R / 4 by positivity) hz₁.le
    rw [Real.log_div hR.ne' (by norm_num)] at h
    exact h
  have hupp : Real.log ‖z‖ ≤ Real.log R :=
    Real.log_le_log hz (by linarith)
  have habs : |Real.log ‖z‖ - Real.log R| ≤ Real.log 4 :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hmul : ξ * α * (Real.log ‖z‖ - Real.log R) ≤ |ξ * α| * Real.log 4 := by
    calc ξ * α * (Real.log ‖z‖ - Real.log R)
        ≤ |ξ * α * (Real.log ‖z‖ - Real.log R)| := le_abs_self _
      _ = |ξ * α| * |Real.log ‖z‖ - Real.log R| := abs_mul _ _
      _ ≤ |ξ * α| * Real.log 4 := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  nlinarith

/-- The inserted metric has normalized lower bounds on arbitrarily large
annular crossings, using the same field and metric assignment. -/
theorem IsWholePlaneGFF.ae_frequently_normalized_inserted_far_crossing
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {γ ξ α : ℝ} {D : Ω → ℂ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ₂ : γ < 2)
    (hD : IsLQGMetricOfField P γ ξ α hC D) :
    ∃ s : ℝ, 0 < s ∧ ∀ᵐ ω ∂P, ∀ m : ℕ, ∃ j : ℕ, m ≤ j ∧
      ∀ x y : ℂ, ‖x‖ < 8 ^ j / 4 → 3 * 8 ^ j / 8 ≤ ‖y‖ →
        Real.exp (-(ξ * α) * Real.log (8 ^ j) - |ξ * α| * Real.log 4) *
          (s * (8 ^ j : ℝ) ^ (xiGamma γ * Q γ) *
            Real.exp (xiGamma γ * hcirc ω (8 ^ j) 0)) ≤ D ω y x := by
  obtain ⟨𝔇, h𝔇, hrepr⟩ := hD
  obtain ⟨s, hs, hcross⟩ := hh.ae_frequently_normalized_far_crossing hγ hγ₂ h𝔇
  refine ⟨s, hs, ?_⟩
  filter_upwards [hcross, hrepr] with ω hcross hrepr
  intro m
  obtain ⟨j, hj, hjcross⟩ := hcross m
  refine ⟨j, hj, ?_⟩
  intro x y hx hy
  have hR : (0 : ℝ) < 8 ^ j := by positivity
  have hbound := ofReal_exp_mul_le_weylScaling_of_annulus_crossing
    (D := 𝔇 (hC ω)) (ξ := ξ) (f := fun z => -α * Real.log ‖z‖)
    (r := (8 : ℝ) ^ j / 4) (r' := 3 * (8 : ℝ) ^ j / 8)
    (m := -(ξ * α) * Real.log (8 ^ j) - |ξ * α| * Real.log 4)
    (c := s * (8 ^ j : ℝ) ^ (xiGamma γ * Q γ) *
      Real.exp (xiGamma γ * hcirc ω (8 ^ j) 0))
    (by linarith) (fun z hz₁ hz₂ => log_weight_lower_on_scaled_annulus hR hz₁ hz₂)
    (fun a b ha hb => hjcross a b (by linarith) (by linarith)) (x := y) (y := x) hy hx
  have heq : ENNReal.ofReal (D ω y x) =
      LatticeProb.LQG.weylScaling (𝔇 (hC ω)) ξ (fun z => -α * Real.log ‖z‖) y x :=
    (hrepr y x).2
  rw [← heq] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (hrepr y x).1).mp hbound

end HarmonicBalls
