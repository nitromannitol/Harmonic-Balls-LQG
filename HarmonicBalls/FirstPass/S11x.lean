import HarmonicBalls.FirstPass.Frozen.S11j
import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.FirstPass.S11m.LocalDecoder
import HarmonicBalls.FirstPass.S11x.DistributionLaw
import HarmonicBalls.FirstPass.S11x.CircleVariance
import HarmonicBalls.FirstPass.S11x.MetricFacts

/-!
# The Weyl exponent of an LQG metric is positive

The derived theorem `lqgMetricExponentPositive_of_inputs` proves the frozen Prop `LQGMetricExponentPositive`
(FirstPass/Frozen/S11j.lean:94) from two named inputs, both used as explicit hypotheses:
* `WholePlaneGFFExistsFrozen` (FirstPass/S11r/Frozen.lean:31): a whole-plane GFF on some `Type` (truth TRUE);
* `WholePlaneGFFAffineInvariance` (Proposed/LQG.lean:51): the normalized whole-plane GFF is invariant under
  `h ↦ h(a · ) - h_a(0)` (PENDING TRUTH CHECK, kept as a hypothesis).

Argument (Bou-Rabee-Gwynne
arXiv:2208.11795v3, Section 2.1, (2.1)-(2.2), p. 8; Duplantier-Sheffield, Berestycki-Powell for the GFF):
with `r_n = e^{-s_n}`, `s_n = n + 1`, `H_n = h_{r_n}(0)`, the field `h^{(n)} = h(r_n ·) - H_n` has the law of `h`
(`wholePlaneGFF_distribution_preimage_eq`), `Var H_n = s_n`, and the Weyl scaling and coordinate change of the
metric give `D_h(0, r_n) = e^{ξ(H_n - Q s_n)} D_{h^{(n)}}(0, 1)` a.s. If `ξ ≤ 0`, then `D_h(0, r_n) ≥ D_{h^{(n)}}(0,1)`
on `{H_n ≤ Q s_n}`, so `P(D_h(0,1) > a) ≤ P(D_h(0,r_n) > a) + (Q² s_n)⁻¹`, while `D_h(0, r_n) → 0` a.s. gives
`P(D_h(0,r_n) > a) → 0`. No independence between `H_n` and the metric is used.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- `wpShift n = n + 1`: the scale exponent `s_n` of the radius `r_n = exp (-s_n)`. -/
noncomputable def wpShift (n : ℕ) : ℝ := (n : ℝ) + 1

/-- The radii `r_n = exp (-s_n)` of the scaling argument: `0 < r_n ≤ 1` and `r_n → 0`. -/
noncomputable def wpRadius (n : ℕ) : ℝ := Real.exp (-wpShift n)

theorem wpShift_pos (n : ℕ) : 0 < wpShift n := by
  unfold wpShift
  positivity

theorem wpRadius_pos (n : ℕ) : 0 < wpRadius n := Real.exp_pos _

theorem wpRadius_le_one (n : ℕ) : wpRadius n ≤ 1 := by
  unfold wpRadius
  rw [Real.exp_le_one_iff]
  linarith [wpShift_pos n]

theorem wpRadius_log (n : ℕ) : Real.log (wpRadius n) = -wpShift n := by
  unfold wpRadius
  rw [Real.log_exp]

theorem wpRadius_tendsto : Tendsto wpRadius atTop (𝓝 0) := by
  have h1 : Tendsto wpShift atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp h1

theorem wpRadius_complex_tendsto :
    Tendsto (fun n => ((wpRadius n : ℝ) : ℂ)) atTop (𝓝 0) := by
  have h := (Complex.continuous_ofReal.tendsto 0).comp wpRadius_tendsto
  rw [Complex.ofReal_zero] at h
  exact h

/-- Adding a constant function to the pairing functional: `(T + c)(φ) = T φ + c ∫ φ`. -/
theorem addFunPairing_zero (T : (ℂ → ℝ) → ℝ) : addFunPairing T (fun _ => (0 : ℝ)) = T := by
  funext φ
  simp [addFunPairing]

theorem addFunPairing_const_const (T : (ℂ → ℝ) → ℝ) (c d : ℝ) :
    addFunPairing (addFunPairing T (fun _ => c)) (fun _ => d) = addFunPairing T (fun _ => c + d) := by
  funext φ
  simp only [addFunPairing, integral_const_mul]
  ring

theorem norm_ofReal_of_pos {a : ℝ} (ha : 0 < a) : ‖(a : ℂ)‖ = a := by
  rw [Complex.norm_real, Real.norm_of_nonneg ha.le]

/-- The normalized pullback of `hC` at radius `a > 0`: the field `h(a · ) - h_a(0)` of
`WholePlaneGFFAffineInvariance` with `b = 0`, i.e. the pairing `φ ↦ a⁻² (h, φ(·/a)) - h_a(0) ∫ φ`. -/
noncomputable def shiftedWholePlaneField {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (a : ℝ) : Ω → (ℂ → ℝ) → ℝ :=
  fun ω φ => (‖(a : ℂ)‖ ^ 2)⁻¹ * hC ω (fun y => φ ((y - 0) / (a : ℂ))) - hcirc ω ‖(a : ℂ)‖ 0 * ∫ x, φ x

/-- The shifted pairing is the affine pullback with the constant `-h_a(0)` added. -/
theorem shiftedWholePlaneField_eq {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    {a : ℝ} (ha : 0 < a) (ω : Ω) :
    shiftedWholePlaneField hC hcirc a ω =
      addFunPairing (affinePullbackPairing (hC ω) a 0) (fun _ => -hcirc ω a 0) := by
  funext φ
  simp only [shiftedWholePlaneField, addFunPairing, affinePullbackPairing, norm_ofReal_of_pos ha,
    sub_zero, neg_mul, integral_neg, integral_const_mul]
  ring

/-- Main result: the frozen Prop `LQGMetricExponentPositive` (FirstPass/Frozen/S11j.lean:94), derived from the
existence of a whole-plane GFF and its affine invariance (both named inputs, see the module docstring). -/
theorem lqgMetricExponentPositive_of_inputs
    (hExists : WholePlaneGFFExistsFrozen.{0})
    (hAff : ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneGFFAffineInvariance P hC hcirc) :
    LQGMetricExponentPositive := by
  intro γ ξ 𝔇 hγ0 _hγ2 hL
  by_contra hξ0
  replace hξ : ξ ≤ 0 := not_lt.1 hξ0
  obtain ⟨Ω, mΩ, P, hP, hC, hcirc, hG⟩ := hExists
  have hQ : 0 < lqgQ γ := by
    unfold lqgQ
    exact add_pos (div_pos two_pos hγ0) (half_pos hγ0)
  -- the shifted fields are whole-plane GFFs (affine invariance input)
  have hGn : ∀ n, ∃ hc' : Ω → ℝ → ℂ → ℝ,
      IsWholePlaneGFF P (shiftedWholePlaneField hC hcirc (wpRadius n)) hc' := by
    intro n
    have hne : ((wpRadius n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (wpRadius_pos n).ne'
    exact ⟨_, hAff Ω P hC hcirc hG ((wpRadius n : ℝ) : ℂ) hne 0⟩
  choose hc' hGn using hGn
  -- metric axioms for the unshifted and the shifted fields
  have hS0 : SatisfiesLQGMetricAxioms P γ ξ 𝔇 hC := by
    have h := hL.satisfiesLQGMetricAxioms Ω P hC hcirc (fun _ _ => (0 : ℝ)) hG
      (fun _ => continuous_const) (fun _ => measurable_const)
    simpa [addFunPairing_zero] using h
  have hSn : ∀ n, SatisfiesLQGMetricAxioms P γ ξ 𝔇 (shiftedWholePlaneField hC hcirc (wpRadius n)) := by
    intro n
    have h := hL.satisfiesLQGMetricAxioms Ω P _ (hc' n) (fun _ _ => (0 : ℝ)) (hGn n)
      (fun _ => continuous_const) (fun _ => measurable_const)
    simpa [addFunPairing_zero] using h
  have hE0 : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := hS0.ae_isEuclideanLengthMetric
  have hEn : ∀ n, ∀ᵐ ω ∂P,
      IsEuclideanLengthMetric (𝔇 (shiftedWholePlaneField hC hcirc (wpRadius n) ω)) :=
    fun n => (hSn n).ae_isEuclideanLengthMetric
  -- coordinate change at radius r_n (axiom IV)
  have hcoord : ∀ n, ∀ᵐ ω ∂P, ∀ u v : ℂ,
      𝔇 (hC ω) (((wpRadius n : ℝ) : ℂ) * u + 0) (((wpRadius n : ℝ) : ℂ) * v + 0) =
        𝔇 (addFunPairing (affinePullbackPairing (hC ω) (wpRadius n) 0)
          (fun _ => lqgQ γ * Real.log (wpRadius n))) u v :=
    fun n => hS0.coordChange (wpRadius n) (wpRadius_pos n) 0
  -- constant Weyl scaling (axiom III applied to the shifted field, constant weights)
  have hscale : ∀ n, ∀ᵐ ω ∂P, ∀ c : ℝ, ∀ u v : ℂ,
      ENNReal.ofReal (𝔇 (addFunPairing (shiftedWholePlaneField hC hcirc (wpRadius n) ω) (fun _ => c)) u v) =
        ENNReal.ofReal (Real.exp (ξ * c)) *
          ENNReal.ofReal (𝔇 (shiftedWholePlaneField hC hcirc (wpRadius n) ω) u v) := by
    intro n
    filter_upwards [(hSn n).ae_weylScaling, (hSn n).ae_isEuclideanLengthMetric] with ω hω hEω
    intro c u v
    rw [hω (fun _ => c) continuous_const u v,
      HarmonicBalls.S11m.weylScaling_const_eq_mul_ofReal hEω ξ c u v]
  -- the coordinate-change argument rewritten as a shift by a constant
  have hK : ∀ n ω, addFunPairing (affinePullbackPairing (hC ω) (wpRadius n) 0)
      (fun _ => lqgQ γ * Real.log (wpRadius n)) =
      addFunPairing (shiftedWholePlaneField hC hcirc (wpRadius n) ω)
        (fun _ => lqgQ γ * Real.log (wpRadius n) + hcirc ω (wpRadius n) 0) := by
    intro n ω
    rw [shiftedWholePlaneField_eq hC hcirc (wpRadius_pos n) ω, addFunPairing_const_const]
    congr 1
    funext x
    ring
  -- the pointwise identity D_h(0, r_n) = exp(ξ (H_n - Q s_n)) D_{h^{(n)}}(0, 1) a.s.
  have hYn : ∀ n, ∀ᵐ ω ∂P, 𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ) =
      Real.exp (ξ * (lqgQ γ * Real.log (wpRadius n) + hcirc ω (wpRadius n) 0)) *
        𝔇 (shiftedWholePlaneField hC hcirc (wpRadius n) ω) 0 1 := by
    intro n
    filter_upwards [hcoord n, hscale n, hE0, hEn n] with ω h1 h2 hE0ω hEnω
    have h3 := h1 0 1
    simp only [mul_zero, mul_one, add_zero] at h3
    rw [hK n ω] at h3
    have h4 := h2 (lqgQ γ * Real.log (wpRadius n) + hcirc ω (wpRadius n) 0) 0 1
    rw [← h3, ← ENNReal.ofReal_mul (Real.exp_pos
      (ξ * (lqgQ γ * Real.log (wpRadius n) + hcirc ω (wpRadius n) 0))).le] at h4
    rw [ENNReal.ofReal_eq_ofReal_iff (hE0ω.dist_nonneg _ _)
      (mul_nonneg (Real.exp_pos _).le (hEnω.dist_nonneg _ _))] at h4
    exact h4
  -- the circle averages H_n = h_{r_n}(0)
  have hH : ∀ n, ∫ ω, hcirc ω (wpRadius n) 0 ∂P = 0 ∧
      variance (fun ω => hcirc ω (wpRadius n) 0) P = wpShift n := by
    intro n
    obtain ⟨h1, h2⟩ := wholePlaneGFF_circle_zero_mean_var hG (wpRadius_pos n) (wpRadius_le_one n)
    refine ⟨h1, ?_⟩
    rw [h2, wpRadius_log, neg_neg]
  -- measurability
  have hmeasY : ∀ n, Measurable (fun ω => 𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ)) := fun n =>
    (hL.measurable_apply 0 ((wpRadius n : ℝ) : ℂ)).comp (measurable_wholePlaneGFF_distribution hG)
  -- the law of the shifted metric equals the law of the metric (affine invariance of the GFF law)
  have hlaw : ∀ n (a : ℝ), P {ω | a < 𝔇 (shiftedWholePlaneField hC hcirc (wpRadius n) ω) 0 1} =
      P {ω | a < 𝔇 (hC ω) 0 1} := by
    intro n a
    have hA : MeasurableSet[distributionMeasurableSpace]
        ((fun T : (ℂ → ℝ) → ℝ => 𝔇 T 0 1) ⁻¹' Ioi a) :=
      measurableSet_Ioi.preimage (hL.measurable_apply 0 1)
    exact wholePlaneGFF_distribution_preimage_eq (hGn n) hG hA
  -- the tail inequality: P(a < D_h(0,1)) ≤ P(a < D_h(0, r_n)) + (Q² s_n)⁻¹
  have hineq : ∀ n (a : ℝ), P {ω | a < 𝔇 (hC ω) 0 1} ≤
      P {ω | a < 𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ)} +
        ENNReal.ofReal ((lqgQ γ ^ 2)⁻¹ * (wpShift n)⁻¹) := by
    intro n a
    have hsub : ∀ᵐ ω ∂P,
        a < 𝔇 (shiftedWholePlaneField hC hcirc (wpRadius n) ω) 0 1 →
          a < 𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ) ∨ lqgQ γ * wpShift n < hcirc ω (wpRadius n) 0 := by
      filter_upwards [hYn n, hEn n] with ω hω hEnω ha
      by_cases hHle : lqgQ γ * wpShift n < hcirc ω (wpRadius n) 0
      · exact Or.inr hHle
      · left
        have hc' : lqgQ γ * Real.log (wpRadius n) + hcirc ω (wpRadius n) 0 ≤ 0 := by
          rw [wpRadius_log, mul_neg]
          linarith [not_lt.1 hHle]
        have hexp : 1 ≤ Real.exp (ξ * (lqgQ γ * Real.log (wpRadius n) + hcirc ω (wpRadius n) 0)) :=
          Real.one_le_exp (mul_nonneg_of_nonpos_of_nonpos hξ hc')
        have hX0 : 0 ≤ 𝔇 (shiftedWholePlaneField hC hcirc (wpRadius n) ω) 0 1 :=
          hEnω.dist_nonneg _ _
        calc a < 𝔇 (shiftedWholePlaneField hC hcirc (wpRadius n) ω) 0 1 := ha
          _ ≤ Real.exp (ξ * (lqgQ γ * Real.log (wpRadius n) + hcirc ω (wpRadius n) 0)) *
              𝔇 (shiftedWholePlaneField hC hcirc (wpRadius n) ω) 0 1 :=
                le_mul_of_one_le_left hX0 hexp
          _ = 𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ) := hω.symm
    have hmono : P {ω | a < 𝔇 (shiftedWholePlaneField hC hcirc (wpRadius n) ω) 0 1} ≤
        P ({ω | a < 𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ)} ∪
          {ω | lqgQ γ * wpShift n < hcirc ω (wpRadius n) 0}) :=
      measure_mono_ae (hsub.mono fun ω hω h => hω h)
    have htail := measure_lt_le_inv_of_variance (wholePlaneGFF_circle_zero_memLp hG (wpRadius_pos n))
      (hH n).1 (wpShift_pos n) hQ (hH n).2
    rw [hlaw n a] at hmono
    calc P {ω | a < 𝔇 (hC ω) 0 1} ≤
          P ({ω | a < 𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ)} ∪
            {ω | lqgQ γ * wpShift n < hcirc ω (wpRadius n) 0}) := hmono
      _ ≤ P {ω | a < 𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ)} +
            P {ω | lqgQ γ * wpShift n < hcirc ω (wpRadius n) 0} := measure_union_le _ _
      _ ≤ P {ω | a < 𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ)} +
            ENNReal.ofReal ((lqgQ γ ^ 2)⁻¹ * (wpShift n)⁻¹) := add_le_add le_rfl htail
  -- D_h(0, r_n) → 0 almost surely, hence in probability
  have hlim_Y : ∀ a : ℝ, 0 < a →
      Tendsto (fun n => P {ω | a < 𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ)}) atTop (𝓝 0) := by
    intro a ha
    have hae : ∀ᵐ ω ∂P, Tendsto (fun n => 𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ)) atTop
        (𝓝 ((fun _ => (0 : ℝ)) ω)) := by
      filter_upwards [hE0] with ω hω
      exact hω.tendsto_zero.comp wpRadius_complex_tendsto
    have hTIM := tendstoInMeasure_of_tendsto_ae (μ := P)
      (fun n => (hmeasY n).aestronglyMeasurable) hae
    have hT := hTIM (ENNReal.ofReal a) (ENNReal.ofReal_pos.2 ha)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT
      (Pi.le_def.2 fun n => zero_le) (Pi.le_def.2 fun n => measure_mono ?_)
    intro ω hω
    have hω' : a < 𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ) := hω
    show ENNReal.ofReal a ≤ edist (𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ)) ((fun _ => (0 : ℝ)) ω)
    rw [edist_dist, Real.dist_eq, sub_zero]
    exact ENNReal.ofReal_le_ofReal (hω'.le.trans (le_abs_self _))
  -- P(a < D_h(0,1)) = 0 for every a > 0
  have hzero : ∀ a : ℝ, 0 < a → P {ω | a < 𝔇 (hC ω) 0 1} = 0 := by
    intro a ha
    have h3 : Tendsto (fun n : ℕ => (lqgQ γ ^ 2)⁻¹ * (wpShift n)⁻¹) atTop (𝓝 0) := by
      have h4 : Tendsto (fun n : ℕ => (wpShift n)⁻¹) atTop (𝓝 0) := by
        have h5 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [wpShift, one_div] using h5
      have h6 : Tendsto (fun n : ℕ => (lqgQ γ ^ 2)⁻¹ * (wpShift n)⁻¹) atTop
          (𝓝 ((lqgQ γ ^ 2)⁻¹ * 0)) :=
        tendsto_const_nhds.mul h4
      rwa [mul_zero] at h6
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal ((lqgQ γ ^ 2)⁻¹ * (wpShift n)⁻¹)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal h3
    have hY := hlim_Y a ha
    have hlimit : Tendsto (fun n => P {ω | a < 𝔇 (hC ω) 0 ((wpRadius n : ℝ) : ℂ)} +
        ENNReal.ofReal ((lqgQ γ ^ 2)⁻¹ * (wpShift n)⁻¹)) atTop (𝓝 0) := by
      have := hY.add h2
      rwa [add_zero] at this
    have hle : P {ω | a < 𝔇 (hC ω) 0 1} ≤ 0 :=
      ge_of_tendsto hlimit (Filter.Eventually.of_forall fun n => hineq n a)
    exact le_antisymm hle (zero_le)
  -- D_h(0,1) > 0 almost surely, so some P(1/(k+1) < D_h(0,1)) > 0: contradiction
  have hXpos : ∀ᵐ ω ∂P, 0 < 𝔇 (hC ω) 0 1 := by
    filter_upwards [hE0] with ω hω
    have hne : 𝔇 (hC ω) 0 1 ≠ 0 := fun h0 => by
      have h1 := hω.eq_of_eq_zero _ _ h0
      exact zero_ne_one h1
    exact lt_of_le_of_ne (hω.dist_nonneg _ _) (Ne.symm hne)
  have hae : ∀ᵐ ω ∂P, ∀ k : ℕ, ¬ (1 / ((k : ℝ) + 1) < 𝔇 (hC ω) 0 1) := by
    rw [ae_all_iff]
    intro k
    have h0 : P {ω | 1 / ((k : ℝ) + 1) < 𝔇 (hC ω) 0 1} = 0 := hzero _ (by positivity)
    exact measure_eq_zero_iff_ae_notMem.1 h0
  obtain ⟨ω, hω1, hω2⟩ := (hXpos.and hae).exists
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hω1
  exact hω2 k hk

end HarmonicBalls
