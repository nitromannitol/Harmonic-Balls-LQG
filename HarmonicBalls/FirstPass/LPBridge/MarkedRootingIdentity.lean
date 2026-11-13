import HarmonicBalls.FirstPass.S11r.FrozenMetricReplacement
import HarmonicBalls.FirstPass.LPBridge.M1
import HarmonicBalls.FirstPass.LPBridge.M4
import LatticeProb.LQG.MarkedRootingCov
import LatticeProb.LQG.MarkedRootingMeasurable
import LatticeProb.LQG.MarkedRootingSingular
import LatticeProb.Prob.RandomMeasureIntensityCylinder

/-!
# Bridge: the marked rooting identity with the root density

`HarmonicBalls.LocalMarkedRootingIdentityWeightedFrozen` is proved from two library results:

* `LatticeProb.Gauss.IsWholePlaneGFF.lintegral_lqgMeasureOfField_marked_ball` (`LatticeProb/LQG/MarkedRootingSingular.lean`):
  the marked rooting identity for the whole-plane field with a logarithmic singularity on a ball `B(0, 2^j)`, for
  finitely many mean-zero test functions and a measurable set `U` of roots avoiding the origin;
* `LatticeProb.aemeasurable_and_lintegral_eq_of_cylinders` (`LatticeProb/Prob/RandomMeasureIntensityCylinder.lean`):
  the passage from rectangles `A × T`, `T` a measurable cylinder, to all measurable sets of
  `ℂ × (MarkedTest D → ℝ)` (the index set is uncountable).

The marks of the library statement are the pairings `fieldPairing α₀ (hC ω) φ`; the marks of the reference
observation `campbellReferenceObs` agree with the shifted marks `fieldPairing + γ ∫ φ(x) Cov(x, z) dx`
(`campbellReferenceObs_eq`), by `LatticeProb.Gauss.integral_mul_wholePlaneCov_eq` and `∫ φ = 0`.
The frozen statement and its use sites are unchanged; the HB definitions are kept.
-/

namespace HarmonicBalls.LPBridge

open MeasureTheory Set Metric
open scoped ENNReal

universe u

/-- The mean-zero test functions supported in `D`: the index set of the marked observations. -/
abbrev MarkedTest (D : Set ℂ) : Type := {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0}

/-- A mean-zero test function on `D` is a test function on the plane. -/
theorem MarkedTest.isTestFunction_univ {D : Set ℂ} (φ : MarkedTest D) :
    LatticeProb.Gauss.IsTestFunction Set.univ φ.1 :=
  ⟨φ.2.1.1, φ.2.1.2.1, Set.subset_univ _⟩

/-- The reference observation at a root, in terms of the covariance of the whole-plane field. -/
theorem campbellReferenceObs_eq (γ α₀ : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (z : ℂ) :
    campbellReferenceObs γ α₀ D hC z = (z, fun φ : MarkedTest D => fieldPairing α₀ hC φ.1 +
      γ * ∫ x, φ.1 x * LatticeProb.Gauss.wholePlaneCov x z) := by
  refine Prod.ext rfl (funext fun φ => ?_)
  have h := LatticeProb.Gauss.integral_mul_wholePlaneCov_eq (MarkedTest.isTestFunction_univ φ) z
  rw [φ.2.2, mul_zero, zero_sub] at h
  show fieldPairing α₀ hC φ.1 - γ * ∫ w, (Real.log ‖w - z‖ - Real.log (max 1 ‖w‖)) * φ.1 w =
    fieldPairing α₀ hC φ.1 + γ * ∫ x, φ.1 x * LatticeProb.Gauss.wholePlaneCov x z
  rw [h]
  ring

/-- The reference observation is jointly measurable in the root and the field. -/
theorem measurable_campbellReferenceObs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α₀ : ℝ) (D : Set ℂ) :
    Measurable fun q : ℂ × Ω => campbellReferenceObs γ α₀ D (hC q.2) q.1 := by
  simp only [campbellReferenceObs_eq]
  refine measurable_fst.prodMk (measurable_pi_iff.2 fun φ => ?_)
  have hφ := MarkedTest.isTestFunction_univ φ
  have h1 : Measurable fun q : ℂ × Ω => hC q.2 φ.1 := (hh.measurable_pairing _ hφ).comp measurable_snd
  have h2 : Measurable fun q : ℂ × Ω => ∫ x, φ.1 x * LatticeProb.Gauss.wholePlaneCov x q.1 :=
    (LatticeProb.Gauss.measurable_integral_mul_wholePlaneCov hφ).comp measurable_fst
  exact (h1.sub_const _).add (h2.const_mul γ)

/-- The marked observation is measurable in the root. -/
theorem measurable_campbellMarkedObs (α₀ : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) :
    Measurable (campbellMarkedObs α₀ D hC) :=
  measurable_id.prodMk measurable_const

/-- The law of the marked observation at a root drawn from `m` on `U`. -/
noncomputable def markedLaw (α₀ : ℝ) (D U : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (m : Measure ℂ) :
    Measure (ℂ × (MarkedTest D → ℝ)) :=
  (m.restrict U).map (campbellMarkedObs α₀ D hC)

theorem markedLaw_apply (α₀ : ℝ) (D U : Set ℂ) (hC : (ℂ → ℝ) → ℝ) (m : Measure ℂ)
    {S : Set (ℂ × (MarkedTest D → ℝ))} (hS : MeasurableSet S) :
    markedLaw α₀ D U hC m S =
      ∫⁻ z in U, S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellMarkedObs α₀ D hC z) ∂m := by
  have hm := measurable_campbellMarkedObs α₀ D hC
  unfold markedLaw
  rw [Measure.map_apply hm hS, ← lintegral_indicator_one (hm hS)]
  rfl

/-- The Lebesgue mixture over roots in `U` of the reference observations. -/
noncomputable def referenceLaw {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ)
    (D U : Set ℂ) (hC : Ω → (ℂ → ℝ) → ℝ) : Measure (ℂ × (MarkedTest D → ℝ)) :=
  (((volume.restrict U).withDensity (rootWeight γ α₀)).prod P).map
    fun q : ℂ × Ω => campbellReferenceObs γ α₀ D (hC q.2) q.1

theorem measurable_rootWeight (γ α₀ : ℝ) : Measurable (rootWeight γ α₀) := by
  unfold rootWeight
  fun_prop

theorem referenceLaw_apply {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α₀ : ℝ) (D U : Set ℂ)
    {S : Set (ℂ × (MarkedTest D → ℝ))} (hS : MeasurableSet S) :
    referenceLaw P γ α₀ D U hC S = ∫⁻ z in U, rootWeight γ α₀ z *
      ∫⁻ ω, S.indicator (fun _ => (1 : ℝ≥0∞)) (campbellReferenceObs γ α₀ D (hC ω) z) ∂P := by
  have hG := measurable_campbellReferenceObs hh γ α₀ D
  unfold referenceLaw
  rw [Measure.map_apply hG hS, Measure.prod_apply (hG hS),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_rootWeight γ α₀)
      (measurable_measure_prodMk_left (hG hS))]
  refine lintegral_congr fun z => ?_
  have hm : MeasurableSet {ω | campbellReferenceObs γ α₀ D (hC ω) z ∈ S} :=
    (hG.comp measurable_prodMk_left) hS
  show rootWeight γ α₀ z * P {ω | campbellReferenceObs γ α₀ D (hC ω) z ∈ S} = _
  rw [← lintegral_indicator_one hm]
  rfl

/-- The cylinder over the finite set `I` of test functions with base `B`, as a set of marks. -/
abbrev cyl {D : Set ℂ} (I : Finset (MarkedTest D)) (B : Set (I → ℝ)) : Set (MarkedTest D → ℝ) :=
  cylinder I B

/-- The root density has finite mass on a disk whose closure avoids the origin. -/
theorem lintegral_rootWeight_lt_top (γ α₀ : ℝ) {c : ℂ} {r : ℝ} (h0 : (0 : ℂ) ∉ closedBall c r) :
    ∫⁻ z in ball c r, rootWeight γ α₀ z < ∞ := by
  have hcont : ContinuousOn (fun z : ℂ =>
      Real.exp (-γ * α₀ * Real.log ‖z‖ + γ ^ 2 * Real.log (max ‖z‖ 1))) (closedBall c r) := by
    intro z hz
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 fun h => h0 (h ▸ hz)
    refine ContinuousAt.continuousWithinAt ?_
    have h1 : ContinuousAt (fun z : ℂ => Real.log ‖z‖) z := continuous_norm.continuousAt.log hn
    have h2 : ContinuousAt (fun z : ℂ => Real.log (max ‖z‖ 1)) z :=
      (continuous_norm.max continuous_const).continuousAt.log (lt_max_of_lt_right one_pos).ne'
    exact ((h1.const_mul _).add (h2.const_mul _)).rexp
  obtain ⟨M, hM⟩ := (isCompact_closedBall c r).bddAbove_image hcont
  calc ∫⁻ z in ball c r, rootWeight γ α₀ z ≤ ∫⁻ z in ball c r, ENNReal.ofReal M :=
        setLIntegral_mono measurable_const fun z hz =>
          ENNReal.ofReal_le_ofReal (hM ⟨z, ball_subset_closedBall hz, rfl⟩)
    _ = ENNReal.ofReal M * volume (ball c r) := setLIntegral_const _ _
    _ < ∞ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- The marked rooting identity on a rectangle `A × T`, `T` a cylinder over finitely many test functions. -/
theorem marked_rect {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) {γ α₀ : ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < LatticeProb.LQG.lqgQ γ) {μ : Ω → Measure ℂ}
    (hμ : LatticeProb.LQG.IsLQGMeasureOfField P γ α₀ hcirc μ) (j : ℕ) {D U : Set ℂ}
    (hDsub : D ⊆ ball (0 : ℂ) ((2 : ℝ) ^ j)) (hUm : MeasurableSet U)
    (hUc : U ⊆ ball (0 : ℂ) ((2 : ℝ) ^ j)) (hU0 : (0 : ℂ) ∉ U) {A : Set ℂ} (hA : MeasurableSet A)
    (I : Finset (MarkedTest D)) {B : Set (I → ℝ)} (hB : MeasurableSet B) :
    AEMeasurable (fun ω => markedLaw α₀ D U (hC ω) (μ ω) (A ×ˢ cyl I B)) P ∧
    ∫⁻ ω, markedLaw α₀ D U (hC ω) (μ ω) (A ×ˢ cyl I B) ∂P =
      referenceLaw P γ α₀ D U hC (A ×ˢ cyl I B) := by
  classical
  have := hh.isProbabilityMeasure
  have hSm : MeasurableSet (A ×ˢ cyl I B) := hA.prod (hB.cylinder I)
  rw [referenceLaw_apply hh γ α₀ D U hSm]
  simp only [markedLaw_apply α₀ D U _ _ hSm]
  let e : I ≃ Fin I.card := I.equivFin
  let φ : Fin I.card → ℂ → ℝ := fun i => (e.symm i).1.1
  let f : ℂ × (Fin I.card → ℝ) → ℝ≥0∞ := Set.indicator
    (A ×ˢ ((fun w : Fin I.card → ℝ => fun a : I => w (e a)) ⁻¹' B)) (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator
    (hA.prod ((measurable_pi_iff.2 fun a => measurable_pi_apply (e a)) hB))
  have key := LatticeProb.Gauss.IsWholePlaneGFF.lintegral_lqgMeasureOfField_marked_ball hh hγ0 hγ2 hα
    hμ j (φ := φ) (fun i => MarkedTest.isTestFunction_univ _) (fun i => (e.symm i).1.2.2)
    (fun i y hy => mem_ball_zero_iff.1 (hDsub ((e.symm i).1.2.1.2.2
      (subset_tsupport _ (Function.mem_support.2 hy))))) hUm hUc hU0 hf
  have hpt : ∀ (g : MarkedTest D → ℝ) (z : ℂ), f (z, fun i => g (e.symm i)) =
      (A ×ˢ cyl I B).indicator (fun _ => (1 : ℝ≥0∞)) (z, g) := by
    intro g z
    simp [f, Set.indicator, cyl, cylinder]
    rfl
  have hL : ∀ ω, ∫⁻ z in U, (A ×ˢ cyl I B).indicator (fun _ => (1 : ℝ≥0∞))
      (campbellMarkedObs α₀ D (hC ω) z) ∂μ ω =
      ∫⁻ z in U, f (z, fun i => hC ω (φ i) - α₀ * ∫ x, φ i x * Real.log ‖x‖) ∂μ ω :=
    fun ω => lintegral_congr fun z => (hpt (fun φ' => fieldPairing α₀ (hC ω) φ'.1) z).symm
  have hR : ∀ z, ∫⁻ ω, (A ×ˢ cyl I B).indicator (fun _ => (1 : ℝ≥0∞))
      (campbellReferenceObs γ α₀ D (hC ω) z) ∂P =
      ∫⁻ ω, f (z, fun i => hC ω (φ i) - α₀ * (∫ x, φ i x * Real.log ‖x‖) +
        γ * ∫ x, φ i x * LatticeProb.Gauss.wholePlaneCov x z) ∂P := fun z =>
    lintegral_congr fun ω => by
      rw [campbellReferenceObs_eq]
      exact (hpt (fun φ' => fieldPairing α₀ (hC ω) φ'.1 +
        γ * ∫ x, φ'.1 x * LatticeProb.Gauss.wholePlaneCov x z) z).symm
  refine ⟨key.1.congr (Filter.Eventually.of_forall fun ω => (hL ω).symm), ?_⟩
  calc ∫⁻ ω, ∫⁻ z in U, (A ×ˢ cyl I B).indicator (fun _ => (1 : ℝ≥0∞))
        (campbellMarkedObs α₀ D (hC ω) z) ∂μ ω ∂P
      = ∫⁻ ω, ∫⁻ z in U, f (z, fun i => hC ω (φ i) - α₀ * ∫ x, φ i x * Real.log ‖x‖) ∂μ ω ∂P :=
        lintegral_congr hL
    _ = _ := key.2
    _ = _ := lintegral_congr fun z => by rw [hR z]; rfl

/-- **The marked rooting identity with the root density.** The local marked rooting identity
`LocalMarkedRootingIdentityWeightedFrozen` holds: it follows from the marked rooting identity of the
whole-plane field with a logarithmic singularity on a ball of radius `2^j`, extended from rectangles with a
cylinder side to all measurable sets. -/
theorem localMarkedRootingIdentityWeighted_of_lp : LocalMarkedRootingIdentityWeightedFrozen.{u} := by
  intro γ α₀ hγ0 hγ2 hα Ω _ P _ hC hcirc μ hGFF hμ c₁ c₂ r₁ r₂ hr₁ hr₂ hsub h0 S hS
  have hh := (isWholePlaneGFF_iff P hC hcirc).1 hGFF
  have hμ' := (isLQGMeasureOfField_iff P γ α₀ hcirc μ).1 hμ
  obtain ⟨j, hj⟩ := pow_unbounded_of_one_lt (‖c₂‖ + r₂) (one_lt_two : (1 : ℝ) < 2)
  have hDsub : ball c₂ r₂ ⊆ ball (0 : ℂ) ((2 : ℝ) ^ j) := fun y hy => by
    rw [mem_ball_zero_iff]
    have h1 := mem_ball_iff_norm.1 hy
    calc ‖y‖ = ‖(y - c₂) + c₂‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - c₂‖ + ‖c₂‖ := norm_add_le _ _
      _ < (2 : ℝ) ^ j := by linarith
  have hUsub : ball c₁ r₁ ⊆ ball c₂ r₂ := ball_subset_closedBall.trans hsub
  have hU0 : (0 : ℂ) ∉ ball c₁ r₁ := fun h => h0 (ball_subset_closedBall (hUsub h))
  have h01 : (0 : ℂ) ∉ closedBall c₁ r₁ := fun h => h0 (ball_subset_closedBall (hsub h))
  have hfin : IsFiniteMeasure ((volume.restrict (ball c₁ r₁)).withDensity (rootWeight γ α₀)) :=
    isFiniteMeasure_withDensity (lintegral_rootWeight_lt_top γ α₀ h01).ne
  have hρ : IsFiniteMeasure (referenceLaw P γ α₀ (ball c₂ r₂) (ball c₁ r₁) hC) := by
    unfold referenceLaw
    infer_instance
  have hbase : ∀ A : Set ℂ, MeasurableSet A → ∀ T ∈ measurableCylinders (fun _ : MarkedTest (ball c₂ r₂) => ℝ),
      AEMeasurable (fun ω => markedLaw α₀ (ball c₂ r₂) (ball c₁ r₁) (hC ω) (μ ω) (A ×ˢ T)) P ∧
      ∫⁻ ω, markedLaw α₀ (ball c₂ r₂) (ball c₁ r₁) (hC ω) (μ ω) (A ×ˢ T) ∂P =
        referenceLaw P γ α₀ (ball c₂ r₂) (ball c₁ r₁) hC (A ×ˢ T) := by
    intro A hA T hT
    obtain ⟨I, B, hB, rfl⟩ := (mem_measurableCylinders _).1 hT
    exact marked_rect hh hγ0 hγ2 hα hμ' j hDsub measurableSet_ball (hUsub.trans hDsub) hU0 hA I hB
  have key := LatticeProb.aemeasurable_and_lintegral_eq_of_cylinders (P := P)
    (fun ω => markedLaw α₀ (ball c₂ r₂) (ball c₁ r₁) (hC ω) (μ ω))
    (referenceLaw P γ α₀ (ball c₂ r₂) (ball c₁ r₁) hC) hbase S hS
  have := key.2
  simp only [markedLaw_apply α₀ _ _ _ _ hS, referenceLaw_apply hh γ α₀ _ _ hS] at this
  exact this

end HarmonicBalls.LPBridge
