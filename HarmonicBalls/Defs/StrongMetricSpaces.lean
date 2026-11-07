import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Defs.LQGGraphDistance
import Mathlib.Analysis.Distribution.Distribution

/-!
# Spaces for strong LQG metrics

The distribution and metric spaces in Gwynne--Miller, arXiv:1905.00383v3,
Section 1.2, pp. 5--6. The distribution space has the weak topology, and the
metric space has the topology of locally uniform convergence.
-/

namespace HarmonicBalls

open TopologicalSpace
open scoped Distributions

/-- Real distributions on the complex plane. -/
abbrev PlaneDistribution := Distribution (⊤ : Opens ℂ) ℝ ⊤

/-- A distribution as a pairing functional, extended by zero outside the test functions. -/
noncomputable def planeDistributionPairing (distribution : PlaneDistribution) : (ℂ → ℝ) → ℝ := by
  classical
  exact fun test => if htest : IsTestFunction Set.univ test then
    distribution ⟨test, htest.1, htest.2.1, htest.2.2⟩ else 0

/-- On a bundled test function, the pairing extension evaluates the distribution. -/
theorem planeDistributionPairing_apply (distribution : PlaneDistribution)
    (test : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    planeDistributionPairing distribution test = distribution test := by
  classical
  have htest : IsTestFunction Set.univ test :=
    ⟨test.contDiff, test.hasCompactSupport, test.tsupport_subset⟩
  simp [planeDistributionPairing, htest]
  congr 1

/-- The pairing extension uniquely identifies the distribution. -/
theorem planeDistributionPairing_injective : Function.Injective planeDistributionPairing := by
  intro first second heq
  ext test
  simpa only [planeDistributionPairing_apply] using congrFun heq test

/-- A pairing functional represents a distribution when they agree on all test functions. -/
def RepresentsPlaneDistribution (pairing : (ℂ → ℝ) → ℝ) (distribution : PlaneDistribution) : Prop :=
  ∀ test : TestFunction (⊤ : Opens ℂ) ℝ ⊤, pairing test = distribution test

/-- A pairing functional represents at most one distribution. -/
theorem RepresentsPlaneDistribution.unique {pairing : (ℂ → ℝ) → ℝ} {first second : PlaneDistribution}
    (hfirst : RepresentsPlaneDistribution pairing first) (hsecond : RepresentsPlaneDistribution pairing second) :
    first = second := by
  ext test
  exact (hfirst test).symm.trans (hsecond test)

/-- The canonical pairing functional represents its distribution. -/
theorem planeDistributionPairing_represents (distribution : PlaneDistribution) :
    RepresentsPlaneDistribution (planeDistributionPairing distribution) distribution := by
  exact planeDistributionPairing_apply distribution

/-- Adding a continuous function to a represented pairing gives the corresponding distribution. -/
theorem RepresentsPlaneDistribution.add_continuous
    {pairing : (ℂ → ℝ) → ℝ} {distribution : PlaneDistribution}
    (hrep : RepresentsPlaneDistribution pairing distribution) {f : ℂ → ℝ} (hf : Continuous f) :
    RepresentsPlaneDistribution (addFunPairing pairing f)
      (distribution + Distribution.ofFun (⊤ : Opens ℂ) f MeasureTheory.volume ⊤) := by
  intro test
  have hfint : MeasureTheory.LocallyIntegrableOn f Set.univ MeasureTheory.volume :=
    hf.continuousOn.locallyIntegrableOn MeasurableSet.univ
  have hfint' : MeasureTheory.LocallyIntegrableOn f (⊤ : Opens ℂ) MeasureTheory.volume := by
    simpa using hfint
  have hfun : (Distribution.ofFun (⊤ : Opens ℂ) f MeasureTheory.volume ⊤ : PlaneDistribution) test =
      ∫ x, test x * f x := by
    simpa only [smul_eq_mul] using (Distribution.ofFun_apply hfint' (φ := test))
  simp only [addFunPairing, hrep test, add_apply, hfun, mul_comm]

/-- A continuous pullback operator on test functions induces the affine pullback distribution. -/
theorem RepresentsPlaneDistribution.affine_pullback_of_testMap
    {pairing : (ℂ → ℝ) → ℝ} {distribution : PlaneDistribution}
    (hrep : RepresentsPlaneDistribution pairing distribution) (r : ℝ) (z : ℂ)
    (pull : TestFunction (⊤ : Opens ℂ) ℝ ⊤ →L[ℝ] TestFunction (⊤ : Opens ℂ) ℝ ⊤)
    (hpull : ∀ (test : TestFunction (⊤ : Opens ℂ) ℝ ⊤) y, pull test y = test ((y - z) / r)) :
    ∃ transformed : PlaneDistribution,
      RepresentsPlaneDistribution (affinePullbackPairing pairing r z) transformed := by
  refine ⟨(r ^ 2)⁻¹ • pull.precompCompactConvergenceCLM ℝ distribution, ?_⟩
  intro test
  change (r ^ 2)⁻¹ * pairing (fun y => test ((y - z) / r)) = (r ^ 2)⁻¹ * distribution (pull test)
  congr 1
  rw [← hrep (pull test)]
  congr 1
  funext y
  exact (hpull test y).symm

/-- Affine precomposition is a linear map on plane test functions. -/
noncomputable def affineTestPullbackLinear (r : ℝ) (hr : r ≠ 0) (z : ℂ) :
    TestFunction (⊤ : Opens ℂ) ℝ ⊤ →ₗ[ℝ] TestFunction (⊤ : Opens ℂ) ℝ ⊤ where
  toFun test := by
    refine ⟨fun y => test ((y - z) / r), ?_, ?_, Set.subset_univ _⟩
    · exact test.contDiff.comp (by fun_prop)
    · have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
      let e : ℂ ≃ₜ ℂ := (Homeomorph.addRight (-z)).trans
        (Homeomorph.mulLeft₀ (r : ℂ)⁻¹ (inv_ne_zero hr'))
      simpa [e, Function.comp_def, sub_eq_add_neg, div_eq_mul_inv, mul_comm] using
        test.hasCompactSupport.comp_homeomorph e
  map_add' := by
    intro f g
    ext y
    rfl
  map_smul' := by
    intro c f
    ext y
    rfl

/-- The affine test-function pullback is precomposition by the inverse affine map. -/
theorem affineTestPullbackLinear_apply (r : ℝ) (hr : r ≠ 0) (z : ℂ)
    (test : TestFunction (⊤ : Opens ℂ) ℝ ⊤) (y : ℂ) :
    affineTestPullbackLinear r hr z test y = test ((y - z) / r) := rfl

/-- Derivatives of an affine precomposition have the standard operator-norm bound. -/
theorem norm_iteratedFDeriv_affine_precomp_le (f : ℂ → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (L : ℂ →L[ℝ] ℂ) (z y : ℂ) (i : ℕ) :
    ‖iteratedFDeriv ℝ i (fun x => f (L (x - z))) y‖ ≤
      ‖L‖ ^ i * ‖iteratedFDeriv ℝ i f (L (y - z))‖ := by
  change ‖iteratedFDeriv ℝ i (fun x => (f ∘ L) (x - z)) y‖ ≤ _
  rw [iteratedFDeriv_comp_sub, L.iteratedFDeriv_comp_right hf _ (by simp)]
  simpa [mul_comm] using
    (ContinuousMultilinearMap.norm_compContinuousLinearMap_le
      (iteratedFDeriv ℝ i f (L (y - z))) (fun _ => L))

/-- Affine precomposition preserves the test-function topology. -/
theorem continuous_affineTestPullbackLinear (r : ℝ) (hr : r ≠ 0) (z : ℂ) :
    Continuous (affineTestPullbackLinear r hr z) := by
  apply (TestFunction.continuous_iff_continuous_comp _).2
  intro K hK
  let L : ℂ →L[ℝ] ℂ := r⁻¹ • ContinuousLinearMap.id ℝ ℂ
  let K' : Compacts ℂ := ⟨(fun x : ℂ => r • x + z) '' K,
    K.isCompact.image (by fun_prop)⟩
  let A : 𝓓_{K}(ℂ, ℝ) →L[ℝ] 𝓓_{K'}(ℂ, ℝ) :=
    ContDiffMapSupportedIn.mkCLM ℝ (fun f x => f (L (x - z)))
      (by intros; rfl) (by intros; rfl)
      (by intro f; exact f.contDiff.comp (by fun_prop))
      (by
        intro f x hx
        apply f.zero_on_compl
        intro hxK
        apply hx
        change x ∈ (fun x : ℂ => r • x + z) '' (K : Set ℂ)
        refine ⟨L (x - z), hxK, ?_⟩
        simp [L, hr])
      (by
        intro i hi
        refine ⟨{i}, ‖L‖ ^ i, by positivity, ?_⟩
        intro f x hx
        calc
          ‖iteratedFDeriv ℝ i (fun x => f (L (x - z))) x‖ ≤
              ‖L‖ ^ i * ‖iteratedFDeriv ℝ i f (L (x - z))‖ :=
            norm_iteratedFDeriv_affine_precomp_le f f.contDiff L z x i
          _ ≤ ‖L‖ ^ i * (Finset.sup {i} fun j =>
              ContDiffMapSupportedIn.seminorm ℝ ℂ ℝ ⊤ K j) f := by
            simp only [Finset.sup_singleton]
            gcongr
            exact ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ)
  have hcont := (TestFunction.ofSupportedInCLM ℝ
    (show (K' : Set ℂ) ⊆ (⊤ : Opens ℂ) from Set.subset_univ _)).continuous.comp A.continuous
  convert hcont using 1
  funext f
  ext x
  change f ((x - z) / r) = f (r⁻¹ • (x - z))
  congr 1
  simp [div_eq_mul_inv, mul_comm]

/-- The continuous linear pullback of test functions by an inverse affine map. -/
noncomputable def affineTestPullbackCLM (r : ℝ) (hr : r ≠ 0) (z : ℂ) :
    TestFunction (⊤ : Opens ℂ) ℝ ⊤ →L[ℝ] TestFunction (⊤ : Opens ℂ) ℝ ⊤ :=
  ⟨affineTestPullbackLinear r hr z, continuous_affineTestPullbackLinear r hr z⟩

/-- Affine pullback of a represented field remains a represented distribution. -/
theorem RepresentsPlaneDistribution.affine_pullback
    {pairing : (ℂ → ℝ) → ℝ} {distribution : PlaneDistribution}
    (hrep : RepresentsPlaneDistribution pairing distribution) (r : ℝ) (hr : r ≠ 0) (z : ℂ) :
    RepresentsPlaneDistribution (affinePullbackPairing pairing r z)
      ((r ^ 2)⁻¹ • (affineTestPullbackCLM r hr z).precompCompactConvergenceCLM ℝ distribution) := by
  intro test
  change (r ^ 2)⁻¹ * pairing (fun y => test ((y - z) / r)) =
    (r ^ 2)⁻¹ * distribution (affineTestPullbackCLM r hr z test)
  congr 1
  rw [← hrep (affineTestPullbackCLM r hr z test)]
  congr 1

/-- Weak topology on plane distributions, generated by evaluation at test functions. -/
@[instance_reducible]
noncomputable def planeDistributionWeakTopology : TopologicalSpace PlaneDistribution :=
  TopologicalSpace.induced
    (fun (distribution : PlaneDistribution) (test : TestFunction (⊤ : Opens ℂ) ℝ ⊤) =>
      distribution test) inferInstance

/-- Evaluation at a test function is continuous in the weak topology. -/
theorem continuous_planeDistribution_evaluation (test : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    @Continuous _ _ planeDistributionWeakTopology inferInstance (fun distribution => distribution test) := by
  let : TopologicalSpace PlaneDistribution := planeDistributionWeakTopology
  exact (continuous_apply test).comp continuous_induced_dom

/-- Precomposition by a continuous test-function map is continuous for weak distributions. -/
theorem continuous_planeDistribution_precomp
    (pull : TestFunction (⊤ : Opens ℂ) ℝ ⊤ →L[ℝ] TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    @Continuous PlaneDistribution PlaneDistribution planeDistributionWeakTopology
      planeDistributionWeakTopology (fun distribution => pull.precompCompactConvergenceCLM ℝ distribution) := by
  let : TopologicalSpace PlaneDistribution := planeDistributionWeakTopology
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro test
  exact continuous_planeDistribution_evaluation (pull test)

/-- A weakly measurable distribution-valued field stays measurable under test precomposition. -/
theorem measurable_planeDistribution_precomp {Ω : Type*} [MeasurableSpace Ω]
    (pull : TestFunction (⊤ : Opens ℂ) ℝ ⊤ →L[ℝ] TestFunction (⊤ : Opens ℂ) ℝ ⊤)
    (field : Ω → PlaneDistribution)
    (hfield : @Measurable Ω PlaneDistribution inferInstance (@borel _ planeDistributionWeakTopology) field) :
    @Measurable Ω PlaneDistribution inferInstance (@borel _ planeDistributionWeakTopology)
      (fun ω => pull.precompCompactConvergenceCLM ℝ (field ω)) := by
  let : TopologicalSpace PlaneDistribution := planeDistributionWeakTopology
  let : MeasurableSpace PlaneDistribution := borel PlaneDistribution
  let : BorelSpace PlaneDistribution := ⟨rfl⟩
  exact (continuous_planeDistribution_precomp pull).measurable.comp hfield

/-- Scalar multiplication of a distribution is continuous in the weak topology. -/
theorem continuous_planeDistribution_const_smul (c : ℝ) :
    @Continuous PlaneDistribution PlaneDistribution planeDistributionWeakTopology
      planeDistributionWeakTopology (fun distribution => c • distribution) := by
  let : TopologicalSpace PlaneDistribution := planeDistributionWeakTopology
  apply continuous_induced_rng.mpr
  apply continuous_pi
  intro test
  change Continuous (fun distribution : PlaneDistribution => c * distribution test)
  exact continuous_const.mul (continuous_planeDistribution_evaluation test)

/-- With a continuous test pullback, the corresponding affine distribution pullback is weakly continuous. -/
theorem continuous_planeDistribution_affine_of_testMap (r : ℝ)
    (pull : TestFunction (⊤ : Opens ℂ) ℝ ⊤ →L[ℝ] TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    @Continuous PlaneDistribution PlaneDistribution planeDistributionWeakTopology
      planeDistributionWeakTopology
      (fun distribution => (r ^ 2)⁻¹ • pull.precompCompactConvergenceCLM ℝ distribution) := by
  let : TopologicalSpace PlaneDistribution := planeDistributionWeakTopology
  exact (continuous_planeDistribution_const_smul (r ^ 2)⁻¹).comp
    (continuous_planeDistribution_precomp pull)

/-- Weak-Borel measurable distribution-valued fields have measurable test-function pairings. -/
theorem measurable_planeDistribution_evaluation {Ω : Type*} [MeasurableSpace Ω]
    (field : Ω → PlaneDistribution)
    (hfield : @Measurable Ω PlaneDistribution inferInstance (@borel _ planeDistributionWeakTopology) field)
    (test : TestFunction (⊤ : Opens ℂ) ℝ ⊤) : Measurable (fun ω => field ω test) := by
  let : TopologicalSpace PlaneDistribution := planeDistributionWeakTopology
  let : MeasurableSpace PlaneDistribution := borel PlaneDistribution
  let : BorelSpace PlaneDistribution := ⟨rfl⟩
  exact (continuous_planeDistribution_evaluation test).measurable.comp hfield

/-- A continuous metric on the plane inducing the Euclidean topology. -/
def IsContinuousPlaneMetric (distance : C(ℂ × ℂ, ℝ)) : Prop :=
  (∀ z, distance (z, z) = 0) ∧
  (∀ z w, distance (z, w) = 0 → z = w) ∧
  (∀ z w, distance (z, w) = distance (w, z)) ∧
  (∀ x y z, distance (x, z) ≤ distance (x, y) + distance (y, z)) ∧
  (∀ U : Set ℂ, IsOpen U ↔ ∀ z ∈ U, ∃ ε > 0, ∀ w, distance (z, w) < ε → w ∈ U)

/-- Continuous plane metrics equipped with the compact-open, hence locally uniform, topology. -/
abbrev ContinuousPlaneMetric := {distance : C(ℂ × ℂ, ℝ) // IsContinuousPlaneMetric distance}

/-- Euclidean distance is a continuous plane metric. -/
theorem continuousPlaneMetric_nonempty : Nonempty ContinuousPlaneMetric := by
  refine ⟨⟨⟨fun point => dist point.1 point.2, continuous_fst.dist continuous_snd⟩, ?_⟩⟩
  refine ⟨dist_self, ?_, dist_comm, dist_triangle, ?_⟩
  · intro z w h
    exact dist_eq_zero.mp h
  · intro U
    change IsOpen U ↔ ∀ z ∈ U, ∃ ε > 0, ∀ w, dist z w < ε → w ∈ U
    simpa only [Set.subset_def, Metric.mem_ball, dist_comm] using (Metric.isOpen_iff (s := U))

/-- Measurability from weak distributions to continuous metrics with their locally uniform Borel structure. -/
def IsMeasurablePlaneMetricMap (metric : PlaneDistribution → ContinuousPlaneMetric) : Prop :=
  @Measurable _ _ (@borel _ planeDistributionWeakTopology) (borel ContinuousPlaneMetric) metric

/-- A strong metric map has weak-Borel measurable pointwise distances. -/
theorem IsMeasurablePlaneMetricMap.measurable_apply
    {metric : PlaneDistribution → ContinuousPlaneMetric} (hmetric : IsMeasurablePlaneMetricMap metric)
    (z w : ℂ) : @Measurable _ _ (@borel _ planeDistributionWeakTopology) inferInstance
      (fun distribution => (metric distribution).1 (z, w)) := by
  let : MeasurableSpace ContinuousPlaneMetric := borel ContinuousPlaneMetric
  let : BorelSpace ContinuousPlaneMetric := ⟨rfl⟩
  have heval : Continuous (fun distance : ContinuousPlaneMetric => distance.1 (z, w)) :=
    (continuous_eval_const (z, w)).comp continuous_subtype_val
  exact heval.measurable.comp hmetric

/-- Evaluating a measurable metric map on a measurable distribution-valued field is measurable. -/
theorem IsMeasurablePlaneMetricMap.measurable_field_apply
    {Ω : Type*} [MeasurableSpace Ω] {metric : PlaneDistribution → ContinuousPlaneMetric}
    (hmetric : IsMeasurablePlaneMetricMap metric) (field : Ω → PlaneDistribution)
    (hfield : @Measurable Ω PlaneDistribution inferInstance (@borel _ planeDistributionWeakTopology) field)
    (z w : ℂ) : Measurable (fun ω => (metric (field ω)).1 (z, w)) :=
  (hmetric.measurable_apply z w).comp hfield

/-- Extend a metric map to pairing functionals; non-distributions receive the Euclidean metric. -/
noncomputable def extendPlaneMetricMap (metric : PlaneDistribution → ContinuousPlaneMetric)
    (pairing : (ℂ → ℝ) → ℝ) (z w : ℂ) : ℝ := by
  classical
  exact if h : ∃ distribution, RepresentsPlaneDistribution pairing distribution then
    (metric (Classical.choose h)).1 (z, w) else dist z w

/-- The extension agrees with the original map whenever the pairing represents a distribution. -/
theorem extendPlaneMetricMap_of_represents (metric : PlaneDistribution → ContinuousPlaneMetric)
    (pairing : (ℂ → ℝ) → ℝ) (distribution : PlaneDistribution)
    (hrep : RepresentsPlaneDistribution pairing distribution) (z w : ℂ) :
    extendPlaneMetricMap metric pairing z w = (metric distribution).1 (z, w) := by
  classical
  unfold extendPlaneMetricMap
  split
  · rename_i h
    have heq := RepresentsPlaneDistribution.unique (Classical.choose_spec h) hrep
    rw [heq]
  · rename_i h
    exact (h ⟨distribution, hrep⟩).elim

/-- The extension agrees with the original map on the canonical pairing. -/
theorem extendPlaneMetricMap_apply (metric : PlaneDistribution → ContinuousPlaneMetric)
    (distribution : PlaneDistribution) (z w : ℂ) :
    extendPlaneMetricMap metric (planeDistributionPairing distribution) z w = (metric distribution).1 (z, w) :=
  extendPlaneMetricMap_of_represents metric _ distribution (planeDistributionPairing_represents distribution) z w

/-- The extension evaluates a continuous perturbation at the corresponding sum of distributions. -/
theorem extendPlaneMetricMap_add_continuous (metric : PlaneDistribution → ContinuousPlaneMetric)
    (pairing : (ℂ → ℝ) → ℝ) (distribution : PlaneDistribution)
    (hrep : RepresentsPlaneDistribution pairing distribution) (f : ℂ → ℝ) (hf : Continuous f)
    (z w : ℂ) : extendPlaneMetricMap metric (addFunPairing pairing f) z w =
      (metric (distribution + Distribution.ofFun (⊤ : Opens ℂ) f MeasureTheory.volume ⊤)).1 (z, w) :=
  extendPlaneMetricMap_of_represents metric _ _ (hrep.add_continuous hf) z w

/-- A represented measurable field gives almost-everywhere measurable metric evaluations. -/
theorem IsMeasurablePlaneMetricMap.aemeasurable_extend_apply
    {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    {metric : PlaneDistribution → ContinuousPlaneMetric} (hmetric : IsMeasurablePlaneMetricMap metric)
    (field : Ω → PlaneDistribution) (pairing : Ω → (ℂ → ℝ) → ℝ)
    (hfield : @Measurable Ω PlaneDistribution inferInstance (@borel _ planeDistributionWeakTopology) field)
    (hrep : ∀ᵐ ω ∂P, RepresentsPlaneDistribution (pairing ω) (field ω)) (z w : ℂ) :
    AEMeasurable (fun ω => extendPlaneMetricMap metric (pairing ω) z w) P := by
  apply (hmetric.measurable_field_apply field hfield z w).aemeasurable.congr
  filter_upwards [hrep] with ω hω
  exact (extendPlaneMetricMap_of_represents metric _ _ hω z w).symm

/-- Metric axioms on distribution-valued GFFs, parameterized by a candidate dimension.

The dimension is a parameter here; identifying it with the LQG dimension requires the
graph-distance characterization. The representation and weak-Borel measurability hypotheses
make explicit the connection between the distribution-valued field and the pairing interface.
The axioms are those of Gwynne--Miller, arXiv:1905.00383v3, Section 1.2, p. 6.
-/
structure SatisfiesStrongMetricAxiomsAtDimension (γ dimension : ℝ)
    (metric : PlaneDistribution → ContinuousPlaneMetric) : Prop where
  dimension_pos : 0 < dimension
  measurable_metric : IsMeasurablePlaneMetricMap metric
  axioms : ∀ (Ω : Type) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (field : Ω → PlaneDistribution) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (f : Ω → ℂ → ℝ),
    @Measurable Ω PlaneDistribution inferInstance (@borel _ planeDistributionWeakTopology) field →
    (∀ᵐ ω ∂P, RepresentsPlaneDistribution (hC ω) (field ω)) →
    IsWholePlaneGFF P hC hcirc → (∀ ω, Continuous (f ω)) →
    (∀ x, Measurable fun ω => f ω x) →
    SatisfiesLQGMetricAxioms P γ (γ / dimension) (extendPlaneMetricMap metric)
      (fun ω => addFunPairing (hC ω) (f ω))

/-- A strong LQG metric at the graph-distance choice of `d_γ`. -/
def IsStrongLQGMetric (γ : ℝ) (metric : PlaneDistribution → ContinuousPlaneMetric) : Prop :=
  SatisfiesStrongMetricAxiomsAtDimension γ (lqgGraphDimension γ) metric

end HarmonicBalls
