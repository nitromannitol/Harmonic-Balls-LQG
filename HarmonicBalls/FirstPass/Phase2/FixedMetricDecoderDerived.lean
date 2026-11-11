import HarmonicBalls.FirstPass.S11r.Frozen
import HarmonicBalls.Steps.Sec11.CenteredFieldSigma
import HarmonicBalls.Steps.Sec11.PairingCovarianceLinearity
import HarmonicBalls.Steps.Sec11.ContinuousFieldShift
import HarmonicBalls.Steps.Sec11.MetricConstantScaling
import HarmonicBalls.Steps.Sec11.InternalMetricContinuity
import HarmonicBalls.Steps.Sec11.CountableCoordinateObservables
import HarmonicBalls.FirstPass.S11m.Finiteness
import HarmonicBalls.FirstPass.S11m.LocalDecoder
import HarmonicBalls.FirstPass.Phase2.AxiomsUnivDerived

/-!
# Fixed-metric normalized measurable decoder, derived (task fp-phase2-b1-decoder-derive, owner z4)

Target: `LocalLQGMetricNormalizedMeasurableFixedMetricFrozen` (`FirstPass/S11r/Frozen.lean:89`), audit binder hB1.
Route: MQ-lh-4 (`notes/fp-gaps/MATH-ANSWERS.md` lines 405-431).

Proved here: the square decoder infrastructure (`exists_dense_decode_ball`), the nonnegativity of a length metric,
the centred test functions `ψ_φ = φ - (∫φ) ρ` on a ball, and, for one fixed sample space, the factorization of
the Weyl-normalized internal metric at one point through the mean-zero ball observations
(`fmd_factor_point`). The sample-space-independent (universal) decoder is not yet derived; see the report.
The Type-`u` premise (axioms I-IV) is `lqgMetricSatisfiesAxiomsUniv_derived` (`FirstPass/Phase2/AxiomsUnivDerived.lean`).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric ProbabilityTheory Filter
open scoped ENNReal

universe u

/-- The open square `ball c r ×ˢ ball c r` is a Polish space (open subspace of `ℂ × ℂ`). -/
instance ballSquare_polishSpace (c : ℂ) (r : ℝ) :
    PolishSpace ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) :=
  IsOpen.polishSpace ((isOpen_ball).prod isOpen_ball)

/-- The open square `ball c r ×ˢ ball c r` is locally compact. -/
instance ballSquare_locallyCompactSpace (c : ℂ) (r : ℝ) :
    LocallyCompactSpace ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) :=
  IsOpen.locallyCompactSpace ((isOpen_ball).prod isOpen_ball)

/-- A countable dense sequence in the open square `ball c r ×ˢ ball c r`, and a measurable decoder that
recovers a continuous function on the square from its values along the sequence (Borel embedding of
`C(X, ℝ)` into `ℕ → ℝ`, as in `IsLQGMetric.exists_common_continuous_observable`). -/
theorem exists_dense_decode_ball (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ d : ℕ → ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)), DenseRange d ∧
      ∃ decode : (ℕ → ℝ) → C(↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)), ℝ), Measurable decode ∧
        ∀ f : C(↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)), ℝ), decode (fun n => f (d n)) = f := by
  have hne : Nonempty ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) :=
    ⟨⟨(c, c), mem_ball_self hr, mem_ball_self hr⟩⟩
  let d : ℕ → ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) := TopologicalSpace.denseSeq _
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq _
  let e : C(↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)), ℝ) → ℕ → ℝ := fun f n => f (d n)
  have he : Measurable e := measurable_pi_iff.mpr fun n => (continuous_eval_const (d n)).measurable
  have hinj : Function.Injective e := by
    intro f g h
    apply ContinuousMap.ext
    have hdense := hd.equalizer f.continuous g.continuous
    apply congrFun (hdense ?_)
    funext n
    exact congrFun h n
  have hemb : MeasurableEmbedding e := he.measurableEmbedding hinj
  obtain ⟨decode, hdecode, hdecode_eq⟩ :=
    hemb.exists_measurable_extend (g := id) measurable_id (fun _ => inferInstance)
  exact ⟨d, hd, decode, hdecode, fun f => congrFun hdecode_eq f⟩

/-- A length metric is nonnegative: `D x x = 0 ≤ D x y + D y x = 2 D x y` by the triangle inequality and symmetry. -/
theorem fmd_nonneg {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D) (x y : ℂ) : 0 ≤ D x y := by
  have h := hD.triangle x y x
  rw [hD.self_eq_zero, hD.symm y x] at h
  linarith

/-- A test function supported in a ball is a test function on the whole plane. -/
theorem fmd_univ_of_ball {c : ℂ} {r : ℝ} {φ : ℂ → ℝ} (h : IsTestFunction (ball c r) φ) :
    IsTestFunction univ φ :=
  ⟨h.1, h.2.1, subset_univ _⟩

/-- The mean-zero correction `ψ_φ = 1 * φ + (-(∫φ)) * ρ` of a ball test function `φ` is a ball test function. -/
theorem fmd_centered_test {c : ℂ} {r : ℝ} {ρ φ : ℂ → ℝ} (hρ : IsTestFunction (ball c r) ρ)
    (hφ : IsTestFunction (ball c r) φ) :
    IsTestFunction (ball c r) (fun x => 1 * φ x + (-(∫ y, φ y)) * ρ x) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ((contDiff_const (c := (1 : ℝ))).mul hφ.1).add ((contDiff_const (c := -(∫ y, φ y))).mul hρ.1)
  · have c1 : HasCompactSupport (fun x => (1 : ℝ) * φ x) := by
      exact hφ.2.1.mul_left
    have c2 : HasCompactSupport (fun x => (-(∫ y, φ y)) * ρ x) := by
      exact hρ.2.1.mul_left
    exact c1.add c2
  · exact (tsupport_add _ _).trans (union_subset
      ((tsupport_mul_subset_right (f := fun _ => (1 : ℝ)) (g := φ)).trans hφ.2.2)
      ((tsupport_mul_subset_right (f := fun _ => -(∫ y, φ y)) (g := ρ)).trans hρ.2.2))

/-- The centred correction `ψ_φ` has integral zero when `∫ ρ = 1`. -/
theorem fmd_integral_centered {c : ℂ} {r : ℝ} {ρ φ : ℂ → ℝ} (hρ : IsTestFunction (ball c r) ρ)
    (hφ : IsTestFunction (ball c r) φ) (hρint : ∫ x, ρ x = 1) :
    ∫ x, (1 * φ x + (-(∫ y, φ y)) * ρ x) = 0 := by
  have hi1 : Integrable φ := hφ.1.continuous.integrable_of_hasCompactSupport hφ.2.1
  have hi2 : Integrable ρ := hρ.1.continuous.integrable_of_hasCompactSupport hρ.2.1
  simp only [one_mul]
  rw [integral_add hi1 (hi2.const_mul _), integral_const_mul, hρint]
  ring

/-- Ω-wise factorization at one point of the square. For a whole-plane GFF `hC` on a fixed sample space, the
Weyl-normalized internal metric of the ball at `q` is a measurable function of the mean-zero ball observations
`localMeanZeroObs 0 (ball c r) (hC ω)` almost surely. The factor is measurable on the observation space
`S → ℝ`; it is not yet independent of the sample space (see `FixedMetricDecoderDerived` report). -/
theorem fmd_factor_point {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    {γ ξ : ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hLQG : IsLQGMetric γ ξ 𝔇)
    {c : ℂ} {r : ℝ} {ρ : ℂ → ℝ} (hρ : IsTestFunction (ball c r) ρ) (hρint : ∫ x, ρ x = 1)
    (q : ℂ × ℂ) (hq : q ∈ ball c r ×ˢ ball c r) :
    ∃ Dq : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) → ℝ, Measurable Dq ∧
      ∀ᵐ ω ∂P, Dq (localMeanZeroObs 0 (ball c r) (hC ω)) =
        Real.exp (ξ * (-(hC ω ρ))) * (internalMetric (𝔇 (hC ω)) (ball c r) q.1 q.2).toReal := by
  -- the shifted field `Y ω = hC ω - hC ω ρ` and the unshifted field, both with axioms I-IV (Type-u derived)
  have hY := lqgMetricSatisfiesAxiomsUniv_derived γ ξ 𝔇 hLQG Ω P hC hcirc (fun ω _ => -(hC ω ρ)) hGFF
    (fun ω => continuous_const) (fun x => (hGFF.measurable_pairing ρ (fmd_univ_of_ball hρ)).neg)
  have h0 := lqgMetricSatisfiesAxiomsUniv_derived γ ξ 𝔇 hLQG Ω P hC hcirc (fun _ _ => (0 : ℝ)) hGFF
    (fun ω => continuous_const) (fun x => measurable_const)
  have hid : (fun ω => addFunPairing (hC ω) (fun _ : ℂ => (0 : ℝ))) = hC := by
    funext ω φ
    simp [addFunPairing]
  rw [hid] at h0
  have hW := h0.ae_weylScaling
  have hI0 := h0.ae_isEuclideanLengthMetric
  have hIY := hY.ae_isEuclideanLengthMetric
  obtain ⟨G, hGm, hGeq⟩ := hY.locality (ball c r) isOpen_ball
  -- coordinates: the shifted pairings on ball test functions
  let Ycoords : Ω → {φ : ℂ → ℝ // IsTestFunction (ball c r) φ} → ℝ :=
    fun ω φ => addFunPairing (hC ω) (fun _ => -(hC ω ρ)) φ.1
  let Λ : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) →
      ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ} → ℝ) :=
    fun v φ => v ⟨fun x => 1 * φ.1 x + (-(∫ y, φ.1 y)) * ρ x,
      fmd_centered_test hρ φ.2, fmd_integral_centered hρ φ.2 hρint⟩
  have hΛ : Measurable Λ := Measurable.of_eval fun φ => measurable_pi_apply _
  -- the pairing σ-algebra of the shifted field on the ball is generated by the coordinates `Ycoords`
  have hle : pairingSigmaAlgebra (fun ω => addFunPairing (hC ω) (fun _ => -(hC ω ρ))) (ball c r) ≤
      MeasurableSpace.comap Ycoords MeasurableSpace.pi := by
    refine iSup₂_le fun φ hφ => ?_
    have hm : Measurable[MeasurableSpace.comap Ycoords MeasurableSpace.pi]
        (fun ω => addFunPairing (hC ω) (fun _ => -(hC ω ρ)) φ) :=
      (measurable_pi_apply (⟨φ, hφ⟩ : {φ : ℂ → ℝ // IsTestFunction (ball c r) φ})).comp
        (comap_measurable Ycoords)
    exact measurable_iff_comap_le.mp hm
  have hgm : Measurable[MeasurableSpace.comap Ycoords MeasurableSpace.pi]
      (fun ω => (G ω q.1 q.2).toReal) :=
    Measurable.mono (ENNReal.measurable_toReal.comp (hGm q.1 q.2)) hle le_rfl
  obtain ⟨K, hK, hKeq⟩ := Measurable.exists_eq_measurable_comp hgm
  -- a.s. coordinatewise identity: shifted pairing equals the mean-zero pairing of ψ_φ
  have hcoord : ∀ φ : {φ : ℂ → ℝ // IsTestFunction (ball c r) φ}, ∀ᵐ ω ∂P,
      Ycoords ω φ = Λ (localMeanZeroObs 0 (ball c r) (hC ω)) φ := by
    rintro ⟨φ, hφ⟩
    filter_upwards [hGFF.ae_centeredTestPairing_eq (fmd_univ_of_ball hφ) (fmd_univ_of_ball hρ)] with ω hω
    have hcp : hC ω (fun x => 1 * φ x + (-(∫ y, φ y)) * ρ x) = centeredTestPairing (hC ω) ρ φ := rfl
    have hint : ∫ x, -(hC ω ρ) * φ x = -(hC ω ρ) * ∫ x, φ x := integral_const_mul _ _
    simp only [Ycoords, Λ, localMeanZeroObs, fieldPairing, addFunPairing, zero_mul, sub_zero]
    rw [hcp, hω, hint]
    ring
  have hall := ae_eq_measurable_comp_of_coordinatewise_ae_eq Ycoords
    (fun ω => Λ (localMeanZeroObs 0 (ball c r) (hC ω))) hcoord K hK
  -- locality of the metric at `q`, and the Weyl scaling by the constant `-(hC ω ρ)`
  have hlocq : ∀ᵐ ω ∂P, internalMetric (𝔇 (addFunPairing (hC ω) (fun _ => -(hC ω ρ)))) (ball c r) q.1 q.2 =
      G ω q.1 q.2 := by
    filter_upwards [hGeq] with ω hω
    exact hω q.1 hq.1 q.2 hq.2
  have hscale : ∀ᵐ ω ∂P, ∀ z w, internalMetric (𝔇 (addFunPairing (hC ω) (fun _ => -(hC ω ρ))))
      (ball c r) z w = ENNReal.ofReal (Real.exp (ξ * (-(hC ω ρ)))) * internalMetric (𝔇 (hC ω)) (ball c r) z w := by
    filter_upwards [hW, hI0, hIY] with ω hWω hI0ω hIYω
    have hk : ∀ u v, 𝔇 (addFunPairing (hC ω) (fun _ => -(hC ω ρ))) u v =
        Real.exp (ξ * (-(hC ω ρ))) * 𝔇 (hC ω) u v := by
      intro u v
      have h1 := hWω (fun _ => -(hC ω ρ)) continuous_const u v
      rw [S11m.weylScaling_const_eq_mul_ofReal hI0ω, ← ENNReal.ofReal_mul (Real.exp_nonneg _)] at h1
      exact (ENNReal.ofReal_eq_ofReal_iff (fmd_nonneg hIYω u v)
        (mul_nonneg (Real.exp_nonneg _) (fmd_nonneg hI0ω u v))).mp h1
    have hfun : 𝔇 (addFunPairing (hC ω) (fun _ => -(hC ω ρ))) =
        fun u v => Real.exp (ξ * (-(hC ω ρ))) * 𝔇 (hC ω) u v :=
      funext fun u => funext fun v => hk u v
    intro z w
    rw [hfun]
    exact internalMetric_const_mul (𝔇 (hC ω)) (Real.exp_pos _) (ball c r) z w
  refine ⟨fun v => K (Λ v), hK.comp hΛ, ?_⟩
  filter_upwards [hall, hlocq, hscale] with ω hallω hlocω hscaleω
  -- chain: decoded value = K(Ycoords) = G-value = internal metric of the shifted field = Weyl factor times
  -- the internal metric of `hC ω`
  have hGq : (G ω q.1 q.2).toReal =
      Real.exp (ξ * (-(hC ω ρ))) * (internalMetric (𝔇 (hC ω)) (ball c r) q.1 q.2).toReal := by
    rw [← hlocω, hscaleω, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  calc K (Λ (localMeanZeroObs 0 (ball c r) (hC ω)))
      = K (Ycoords ω) := hallω.symm
    _ = (G ω q.1 q.2).toReal := (congrFun hKeq ω).symm
    _ = _ := hGq

/-- The metric property holds almost surely, from the Type-`u` derived axioms (`f = 0`, `addFunPairing T 0 = T`). -/
theorem fmd_ae_metric {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) {γ ξ : ℝ}
    {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ} (hLQG : IsLQGMetric γ ξ 𝔇) :
    ∀ᵐ ω ∂P, IsEuclideanLengthMetric (𝔇 (hC ω)) := by
  have h0 := lqgMetricSatisfiesAxiomsUniv_derived γ ξ 𝔇 hLQG Ω P hC hcirc (fun _ _ => (0 : ℝ)) hGFF
    (fun ω => continuous_const) (fun x => measurable_const)
  have hid : (fun ω => addFunPairing (hC ω) (fun _ : ℂ => (0 : ℝ))) = hC := by
    funext ω φ
    simp [addFunPairing]
  rw [hid] at h0
  exact h0.ae_isEuclideanLengthMetric

/-- Fixed-metric normalized measurable decoder `LocalLQGMetricNormalizedMeasurableFixedMetricFrozen`, derived from the
sample-space-free point decoder `hUnivPt` (named hypothesis; the universal clause, BLOCKED-STEP MQ-lh-23). For each point
`q` of the square, `hUnivPt` gives one measurable functional `Dq` of the mean-zero ball observations, valid for every
whole-plane GFF on every probability space. The decoder `M` is the dense-sequence decode of these values (`exists_dense_decode_ball`);
the square-continuity and finiteness of the internal metric of `hC ω` on the ball come from the derived axioms. -/
theorem localLQGMetricNormalizedMeasurableFixedMetric_of_univPoint
    (hUnivPt : ∀ (γ ξ : ℝ) (c : ℂ) (r : ℝ) (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (ρ : ℂ → ℝ),
      0 < γ → γ < 2 → 0 < r → (0 : ℂ) ∉ closedBall c r → IsLQGMetric γ ξ 𝔇 →
      IsTestFunction (ball c r) ρ → ∫ x, ρ x = 1 → ∀ q : ℂ × ℂ, q ∈ ball c r ×ˢ ball c r →
      ∃ Dq : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) → ℝ, Measurable Dq ∧
        ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
          ∀ᵐ ω ∂P, Dq (localMeanZeroObs 0 (ball c r) (hC ω)) =
            Real.exp (ξ * (-(hC ω ρ))) * (internalMetric (𝔇 (hC ω)) (ball c r) q.1 q.2).toReal) :
    LocalLQGMetricNormalizedMeasurableFixedMetricFrozen.{u} := by
  intro γ ξ c r hγ hγ2 hr h0c 𝔇 hLQG
  obtain ⟨ρ, hρ, hρint⟩ := IsTestFunction.exists_integral_eq_one isOpen_ball ⟨c, mem_ball_self hr⟩
  obtain ⟨d, _hd, decode, hdec, hdecode_eq⟩ := exists_dense_decode_ball c hr
  have hpt : ∀ n : ℕ, ∃ Dq : ({φ : ℂ → ℝ // IsTestFunction (ball c r) φ ∧ ∫ x, φ x = 0} → ℝ) → ℝ,
      Measurable Dq ∧ ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), IsWholePlaneGFF P hC hcirc →
        ∀ᵐ ω ∂P, Dq (localMeanZeroObs 0 (ball c r) (hC ω)) =
          Real.exp (ξ * (-(hC ω ρ))) * (internalMetric (𝔇 (hC ω)) (ball c r) (d n).1.1 (d n).1.2).toReal :=
    fun n => hUnivPt γ ξ c r 𝔇 ρ hγ hγ2 hr h0c hLQG hρ hρint (d n).1 (d n).2
  choose Dq hDqm hDq using hpt
  refine ⟨ρ, fun v => decode (fun n => Dq n v), hρ, hρint, hdec.comp (Measurable.of_eval fun n => hDqm n), ?_⟩
  intro Ω _ P _ hC hcirc hGFF
  have hmet := fmd_ae_metric hGFF hLQG
  have hae : ∀ᵐ ω ∂P, ∀ n, Dq n (localMeanZeroObs 0 (ball c r) (hC ω)) =
      Real.exp (ξ * (-(hC ω ρ))) * (internalMetric (𝔇 (hC ω)) (ball c r) (d n).1.1 (d n).1.2).toReal :=
    ae_all_iff.mpr fun n => hDq n Ω P hC hcirc hGFF
  filter_upwards [hmet, hae] with ω hωm hω
  have hcont : ContinuousOn (fun p : ℂ × ℂ => internalMetric (𝔇 (hC ω)) (ball c r) p.1 p.2)
      (ball c r ×ˢ ball c r) :=
    hωm.continuousOn_internalMetric_pair (fmd_nonneg hωm) isOpen_ball
  have hfin : ∀ p : ℂ × ℂ, p ∈ ball c r ×ˢ ball c r → internalMetric (𝔇 (hC ω)) (ball c r) p.1 p.2 ≠ ⊤ :=
    fun p hp => S11m.internalMetric_ne_top_of_isConnected hωm isOpen_ball
      ((convex_ball c r).isConnected ⟨c, mem_ball_self hr⟩) hp.1 hp.2
  have hcR : Continuous (fun q : ↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)) =>
      (internalMetric (𝔇 (hC ω)) (ball c r) q.1.1 q.1.2).toReal) := by
    have h1 : ContinuousOn (fun p : ℂ × ℂ => (internalMetric (𝔇 (hC ω)) (ball c r) p.1 p.2).toReal)
        (ball c r ×ˢ ball c r) :=
      ContinuousOn.comp (g := ENNReal.toReal) ENNReal.continuousOn_toReal hcont
        (fun p hp => hfin p hp)
    exact continuousOn_iff_continuous_domRestrict.mp h1
  let F : C(↥(ball c r ×ˢ ball c r : Set (ℂ × ℂ)), ℝ) :=
    ⟨fun q => Real.exp (ξ * (-(hC ω ρ))) * (internalMetric (𝔇 (hC ω)) (ball c r) q.1.1 q.1.2).toReal,
      continuous_const.mul hcR⟩
  have hv : (fun n => Dq n (localMeanZeroObs 0 (ball c r) (hC ω))) = fun n => F (d n) :=
    funext fun n => hω n
  have hM : decode (fun n => Dq n (localMeanZeroObs 0 (ball c r) (hC ω))) = F := by
    rw [hv]
    exact hdecode_eq F
  intro p
  have hexp : -ξ * fieldPairing 0 (hC ω) ρ = ξ * (-(hC ω ρ)) := by
    simp only [fieldPairing, zero_mul, sub_zero]
    ring
  show ENNReal.ofReal (decode (fun n => Dq n (localMeanZeroObs 0 (ball c r) (hC ω))) p) = _
  rw [hM, hexp]
  show ENNReal.ofReal (Real.exp (ξ * (-(hC ω ρ))) * (internalMetric (𝔇 (hC ω)) (ball c r) p.1.1 p.1.2).toReal) = _
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_toReal (hfin p.1 p.2)]

end HarmonicBalls
