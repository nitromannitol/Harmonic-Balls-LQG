import HarmonicBalls.FirstPass.Phase2.PinchExplicitGeometry
import HarmonicBalls.FirstPass.Phase2.CameronMartinMutualDerived
import HarmonicBalls.FirstPass.Phase2.GFFExistsConstructed
import HarmonicBalls.FirstPass.LPBridge.M5b
import HarmonicBalls.FirstPass.LPBridge.M1
import LatticeProb.LQG.LQGMetricPointScaling
import LatticeProb.LQG.InternalMetricSquareTail
import LatticeProb.LQG.LQGMetricMeasurable
import LatticeProb.LQG.LQGMeasureExistenceNonpos
import LatticeProb.Gauss.GFFCovPSD7
import LatticeProb.LQG.LQGMetricUniv

/-! # The Weyl scaling exponent of a γ-LQG metric is positive

`isLQGMetric_xi_pos`: if `𝔇` is a γ-LQG metric with Weyl scaling exponent `ξ` (`IsLQGMetric γ ξ 𝔇`) and `0 < γ < 2`,
then `0 < ξ`. This is the binder `hξ` of `firstPass_11_12_derivedInputsMetricOfXiPos` and of
`pinchThirdEventPositiveStmt_of_faithful` (FirstPass/Phase2/PinchExplicitGeometry.lean); the frozen Draft Lemmas 11.12 and
11.17 quantify over every real `ξ`.

Argument (scaling at the origin). Suppose `ξ ≤ 0`, take a whole-plane GFF `h` (it exists on a probability space of
`Type`), and let `r_n = 2^{-(n+1)}`. Almost surely, for all `n`,
`D_h(r_n, 0) = e^{ξ (h_{r_n}(0) + Q log r_n)} D_{h̃_n}(1, 0)`, where `h̃_n = h(r_n ·) - h_{r_n}(0)` is again a whole-plane
GFF (`LatticeProb.LQG.IsLQGMetric.ae_scaling`).
1. Axiom I and continuity give `D_h(r_n, 0) → D_h(0, 0) = 0` almost surely, hence in probability.
2. `D_h(1, 0) > 0` almost surely, so `p = P[D_h(1, 0) ≤ η] < 1/2` for some `η > 0`; by uniqueness of the law of the
   whole-plane GFF on the distribution σ-algebra, `P[D_{h̃_n}(1, 0) ≤ η] = p` for every `n`.
3. `h_{r_n}(0)` is a centred Gaussian, so `P[h_{r_n}(0) ≤ 0] ≥ 1/2`. On that event `h_{r_n}(0) + Q log r_n ≤ 0`, so
   `e^{ξ(...)} ≥ 1` and `D_h(r_n, 0) ≥ D_{h̃_n}(1, 0)`. Hence `1/2 ≤ P[D_h(r_n, 0) ≥ η] + p` for every `n`, which
   contradicts 1.
-/

namespace HarmonicBalls

universe u
namespace LQGMetricXiPos

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

/-- A Euclidean length metric is nonnegative. -/
theorem euclideanLengthMetric_nonneg {D : ℂ → ℂ → ℝ} (h : LatticeProb.LQG.IsEuclideanLengthMetric D)
    (z w : ℂ) : 0 ≤ D z w := by
  have h1 := h.triangle z w z
  rw [h.self_eq_zero, h.symm w z] at h1
  linarith

/-- A Euclidean length metric is positive off the diagonal. -/
theorem euclideanLengthMetric_pos {D : ℂ → ℂ → ℝ} (h : LatticeProb.LQG.IsEuclideanLengthMetric D) {z w : ℂ}
    (hzw : z ≠ w) : 0 < D z w :=
  lt_of_le_of_ne (euclideanLengthMetric_nonneg h z w) fun h0 => hzw (h.eq_of_eq_zero z w h0.symm)

/-- The median of a centred real Gaussian variable is `0`: `P[X ≤ 0] ≥ 1/2`. -/
theorem half_le_measure_nonpos_of_hasGaussianLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : HasGaussianLaw X P) (hXm : Measurable X)
    (h0 : ∫ ω, X ω ∂P = 0) : (1 / 2 : ℝ≥0∞) ≤ P {ω | X ω ≤ 0} := by
  set μ : Measure ℝ := P.map X with hμ
  have : IsGaussian μ := hX.isGaussian_map
  have : IsProbabilityMeasure μ := (Measure.isProbabilityMeasure_map_iff hXm.aemeasurable).2 ‹_›
  have hmean : μ[id] = 0 := by
    rw [hμ, integral_map hXm.aemeasurable aestronglyMeasurable_id]
    simpa using h0
  have hG : μ = gaussianReal 0 (Var[id; μ]).toNNReal := by
    conv_lhs => rw [IsGaussian.eq_gaussianReal μ ‹_›]
    rw [hmean]
  have hsymm : μ.map (fun x => -x) = μ := by
    rw [hG, gaussianReal_map_neg, neg_zero]
  have hIic : μ (Iic 0) = μ (Ici 0) := by
    have h1 : (μ.map (fun x => -x)) (Iic (0 : ℝ)) = μ (Iic 0) := by rw [hsymm]
    rw [Measure.map_apply measurable_neg measurableSet_Iic] at h1
    have hpre : (fun x : ℝ => -x) ⁻¹' Iic 0 = Ici 0 := by
      ext x
      simp
    rw [hpre] at h1
    exact h1.symm
  have hle : (1 : ℝ≥0∞) ≤ μ (Iic 0) * 2 := by
    calc (1 : ℝ≥0∞) = μ univ := measure_univ.symm
      _ = μ (Iic 0 ∪ Ici 0) := by rw [Iic_union_Ici]
      _ ≤ μ (Iic 0) + μ (Ici 0) := measure_union_le _ _
      _ = μ (Iic 0) * 2 := by rw [← hIic, mul_two]
  have hP : P {ω | X ω ≤ 0} = μ (Iic 0) := by
    rw [hμ, Measure.map_apply hXm measurableSet_Iic]
    rfl
  rw [hP]
  exact ENNReal.div_le_of_le_mul hle

/-- Law transfer between two whole-plane GFFs on the same probability space: for `B` in the distribution σ-algebra,
`P[h' ∈ B] = P[h ∈ B]`. -/
theorem measure_preimage_eq_of_isWholePlaneGFF {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC hC' : Ω → (ℂ → ℝ) → ℝ} {hcirc hcirc' : Ω → ℝ → ℂ → ℝ}
    (hW : IsWholePlaneGFF P hC hcirc) (hW' : IsWholePlaneGFF P hC' hcirc')
    {B : Set ((ℂ → ℝ) → ℝ)} (hB : MeasurableSet[distributionMeasurableSpace] B) :
    P (hC' ⁻¹' B) = P (hC ⁻¹' B) := by
  rw [distributionMeasurableSpace_eq_comap_cmDerivedEval] at hB
  obtain ⟨B', hB', rfl⟩ := MeasurableSpace.measurableSet_comap.1 hB
  have hmap := wholePlaneGFF_localFieldPairings_map_eq hW hW' 0 Set.univ
  have e1 : localFieldPairings 0 hC Set.univ = fun ω => cmDerivedEval (hC ω) := by
    funext ω φ
    simp [localFieldPairings, fieldPairing, cmDerivedEval]
  have e2 : localFieldPairings 0 hC' Set.univ = fun ω => cmDerivedEval (hC' ω) := by
    funext ω φ
    simp [localFieldPairings, fieldPairing, cmDerivedEval]
  rw [e1, e2] at hmap
  have hF : Measurable fun ω => cmDerivedEval (hC ω) :=
    measurable_pi_iff.2 fun φ => hW.measurable_pairing φ.1 φ.2
  have hF' : Measurable fun ω => cmDerivedEval (hC' ω) :=
    measurable_pi_iff.2 fun φ => hW'.measurable_pairing φ.1 φ.2
  have hLHS : P (hC ⁻¹' (cmDerivedEval ⁻¹' B')) = (P.map fun ω => cmDerivedEval (hC ω)) B' :=
    (Measure.map_apply hF hB').symm
  have hRHS : P (hC' ⁻¹' (cmDerivedEval ⁻¹' B')) = (P.map fun ω => cmDerivedEval (hC' ω)) B' :=
    (Measure.map_apply hF' hB').symm
  rw [hLHS, hRHS, hmap]

end LQGMetricXiPos

open MeasureTheory Set Filter Topology ProbabilityTheory LQGMetricXiPos
open scoped ENNReal

/-- **The Weyl scaling exponent of a γ-LQG metric is positive**: if `IsLQGMetric γ ξ 𝔇` and `0 < γ < 2`, then
`0 < ξ`. -/
theorem isLQGMetric_xi_pos : ∀ (γ ξ : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ), 0 < γ → γ < 2 →
    IsLQGMetric γ ξ 𝔇 → 0 < ξ := by
  intro γ ξ 𝔇 hγ _ h𝔇
  by_contra hξ0
  have hξ : ξ ≤ 0 := not_lt.1 hξ0
  have hL := (LPBridge.isLQGMetric_iff γ ξ 𝔇).1 h𝔇
  obtain ⟨Ω, _, P, hP, hC, hcirc, hG⟩ := LatticeProb.Gauss.exists_isWholePlaneGFF_of_psd
    LatticeProb.Gauss.wholePlaneCovPSD_proved lp_increment_bound
  set r : ℕ → ℝ := fun n => (1 / 2 : ℝ) ^ (n + 1) with hr_def
  have hr0 : ∀ n, 0 < r n := fun n => by positivity
  have hr1 : ∀ n, r n < 1 := fun n => pow_lt_one₀ (by norm_num) (by norm_num) (Nat.succ_ne_zero n)
  have hrt : Tendsto r atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).comp
      (tendsto_add_atTop_nat 1)
  -- Axiom I for `h`.
  have hI := hL.ae_isEuclideanLengthMetric_self hG
  -- Measurability of `ω ↦ D_h(x, y)`.
  have hmeas : ∀ x y : ℂ, Measurable fun ω => 𝔇 (hC ω) x y := fun x y =>
    (show Measurable (fun T : LatticeProb.LQG.PairingFun => 𝔇 T x y) from hL.measurable_apply x y).comp
      (LatticeProb.LQG.measurable_toPairingFun hG.measurable_pairing)
  -- Scaling about the origin.
  have hS : ∀ᵐ ω ∂P, ∀ n, 𝔇 (hC ω) (r n) 0 =
      Real.exp (ξ * (hcirc ω (r n) 0 + LatticeProb.LQG.lqgQ γ * Real.log (r n))) *
        𝔇 (LatticeProb.LQG.recentredPairing hC hcirc (r n) 0 ω) 1 0 :=
    ae_all_iff.2 fun n => (hL.ae_scaling hG (hr0 n) 0).mono fun ω h => by simpa using h 1 0
  -- Step 1: `D_h(r_n, 0) → 0` almost surely, hence in probability.
  have hconv : ∀ᵐ ω ∂P, Tendsto (fun n => 𝔇 (hC ω) (r n) 0) atTop (𝓝 0) := by
    filter_upwards [hI] with ω h
    have hc : Tendsto (fun n => ((r n : ℝ) : ℂ)) atTop (𝓝 (0 : ℂ)) := by
      have h1 := (Complex.continuous_ofReal.tendsto 0).comp hrt
      rw [Complex.ofReal_zero] at h1
      exact h1
    have h1 := ((h.continuous_left 0).tendsto 0).comp hc
    rw [h.self_eq_zero] at h1
    exact h1
  have hTIM := tendstoInMeasure_iff_dist.1
    (tendstoInMeasure_of_tendsto_ae (g := fun _ => (0 : ℝ))
      (fun n => (hmeas (r n) 0).aestronglyMeasurable) hconv)
  -- Step 2: a level `η > 0` with `p = P[D_h(1, 0) ≤ η] < 1/2`.
  have hpos : ∀ᵐ ω ∂P, 0 < 𝔇 (hC ω) 1 0 := hI.mono fun ω h => euclideanLengthMetric_pos h one_ne_zero
  set A : ℕ → Set Ω := fun k => {ω | 𝔇 (hC ω) 1 0 ≤ 1 / ((k : ℝ) + 1)} with hA_def
  have hAm : ∀ k, MeasurableSet (A k) := fun k => measurableSet_le (hmeas 1 0) measurable_const
  have hAanti : Antitone A := by
    intro k l hkl ω hω
    simp only [hA_def, mem_ofPred_eq] at hω ⊢
    refine hω.trans (one_div_le_one_div_of_le (by positivity) ?_)
    have : (k : ℝ) ≤ l := by exact_mod_cast hkl
    linarith
  have hAnull : P (⋂ k, A k) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.1 hpos)
    simp only [hA_def, mem_iInter, mem_ofPred_eq] at hω
    simp only [mem_ofPred_eq, not_lt]
    by_contra hcon0
    have hcon : 0 < 𝔇 (hC ω) 1 0 := not_le.1 hcon0
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hcon
    exact absurd (hω k) (not_le.2 hk)
  have hAlim : Tendsto (fun k => P (A k)) atTop (𝓝 0) := by
    have h1 := tendsto_measure_iInter_atTop (μ := P) (fun k => (hAm k).nullMeasurableSet) hAanti
      ⟨0, measure_ne_top _ _⟩
    rw [hAnull] at h1
    exact h1
  obtain ⟨k, hk⟩ := (hAlim.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < 1 / 2 by norm_num))).exists
  set η : ℝ := 1 / ((k : ℝ) + 1) with hη_def
  have hη : 0 < η := by positivity
  -- The recentred fields have the law of `h`.
  have hlaw : ∀ n, P {ω | 𝔇 (LatticeProb.LQG.recentredPairing hC hcirc (r n) 0 ω) 1 0 ≤ η} = P (A k) := by
    intro n
    have hW := (LPBridge.isWholePlaneGFF_iff P hC hcirc).2 hG
    have hW' := (LPBridge.isWholePlaneGFF_iff P _ _).2
      (LatticeProb.LQG.isWholePlaneGFF_recentredPairing hG (hr0 n) 0)
    exact measure_preimage_eq_of_isWholePlaneGFF hW hW' ((h𝔇.measurable_apply 1 0) measurableSet_Iic)
  -- Step 3: the median bound and the pointwise comparison.
  have hmed : ∀ n, (1 / 2 : ℝ≥0∞) ≤ P {ω | hcirc ω (r n) 0 ≤ 0} := by
    intro n
    have hX : HasGaussianLaw (fun ω => hcirc ω (r n) 0) P :=
      hG.isGaussianProcess.hasGaussianLaw_eval ⟨.circle (r n) 0, hr0 n⟩
    exact half_le_measure_nonpos_of_hasGaussianLaw hX (hG.measurable_circle _ _ (hr0 n))
      (hG.integral_eq_zero (.circle (r n) 0) (hr0 n))
  have hEle : ∀ n, (1 / 2 : ℝ≥0∞) ≤ P {ω | η ≤ dist (𝔇 (hC ω) (r n) 0) 0} + P (A k) := by
    intro n
    refine (hmed n).trans ?_
    calc P {ω | hcirc ω (r n) 0 ≤ 0}
        ≤ P ({ω | η ≤ dist (𝔇 (hC ω) (r n) 0) 0} ∪
            {ω | 𝔇 (LatticeProb.LQG.recentredPairing hC hcirc (r n) 0 ω) 1 0 ≤ η}) := by
          refine measure_mono_ae (hS.mono fun ω hω hneg => ?_)
          have hneg' : hcirc ω (r n) 0 ≤ 0 := hneg
          rcases le_or_gt (𝔇 (LatticeProb.LQG.recentredPairing hC hcirc (r n) 0 ω) 1 0) η with hX | hX
          · exact Or.inr hX
          · refine Or.inl ?_
            show η ≤ dist (𝔇 (hC ω) (r n) 0) 0
            have hc : hcirc ω (r n) 0 + LatticeProb.LQG.lqgQ γ * Real.log (r n) ≤ 0 := by
              have := mul_neg_of_pos_of_neg (LatticeProb.LQG.LQGMeasureExistenceNonpos.lqgQ_pos hγ) (Real.log_neg (hr0 n) (hr1 n))
              linarith
            have he : 1 ≤ Real.exp (ξ * (hcirc ω (r n) 0 + LatticeProb.LQG.lqgQ γ * Real.log (r n))) :=
              Real.one_le_exp (mul_nonneg_of_nonpos_of_nonpos hξ hc)
            rw [Real.dist_0_eq_abs, hω n]
            refine le_trans ?_ (le_abs_self _)
            calc η ≤ 𝔇 (LatticeProb.LQG.recentredPairing hC hcirc (r n) 0 ω) 1 0 := hX.le
              _ ≤ _ := le_mul_of_one_le_left (hη.trans hX).le he
      _ ≤ P {ω | η ≤ dist (𝔇 (hC ω) (r n) 0) 0} +
            P {ω | 𝔇 (LatticeProb.LQG.recentredPairing hC hcirc (r n) 0 ω) 1 0 ≤ η} :=
          measure_union_le _ _
      _ = P {ω | η ≤ dist (𝔇 (hC ω) (r n) 0) 0} + P (A k) := by rw [hlaw n]
  -- Contradiction with step 1.
  have hgap : (0 : ℝ≥0∞) < 1 / 2 - P (A k) := tsub_pos_of_lt hk
  obtain ⟨n, hn⟩ := ((hTIM η hη).eventually (gt_mem_nhds hgap)).exists
  have h2 : P {ω | η ≤ dist (𝔇 (hC ω) (r n) 0) 0} + P (A k) < 1 / 2 := by
    have h3 := ENNReal.add_lt_add_right (ne_top_of_lt hk) hn
    rwa [tsub_add_cancel_of_le hk.le] at h3
  exact absurd (hEle n) (not_le.2 h2)

/-- Draft Lemma 11.17 (`PinchThirdEventPositiveStmt`, every real `ξ`) from the metric inputs of the corrected
Lemma 11.17 (`hDC hFin hAx`); the positivity of `ξ` is `isLQGMetric_xi_pos`. -/
theorem pinchThirdEventPositiveStmt_derivedInputsMetric (hDC : DyadicCellDiamSmallFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u}) (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchThirdEventPositiveStmt.{u} :=
  pinchThirdEventPositiveStmt_of_faithful (firstPass_11_17_corrected_derivedInputsMetric hDC hFin hAx)
    isLQGMetric_xi_pos

/-- Lemma 11.12 (Draft form) from the metric inputs of the corrected Lemma 11.17 (`hDC hFin hAx`, all literature
inputs of the LQG metric) alone. -/
theorem firstPass_11_12_derivedInputsMetric (hDC : DyadicCellDiamSmallFrozen.{u})
    (hFin : ConnectedSquareUnionDiamFiniteFrozen.{u}) (hAx : LQGMetricFieldAxiomsUnivFrozen.{u}) :
    PinchEventPositiveProbabilityStmt.{u} :=
  firstPass_11_12_derivedInputsMetricOfXiPos hDC hFin hAx isLQGMetric_xi_pos

end HarmonicBalls
