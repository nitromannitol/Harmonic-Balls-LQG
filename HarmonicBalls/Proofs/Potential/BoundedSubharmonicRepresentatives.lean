import HarmonicBalls.Audit.GreenSubharmonicTestClass
import HarmonicBalls.Proofs.Potential.GreenBall
import HarmonicBalls.Proofs.Potential.GreenPositivity
import HarmonicBalls.Proofs.Sec6.GreenMono
import HarmonicBalls.Proofs.Sec4.GreenAwayFromPole
import HarmonicBalls.Proofs.Sec10.DominatedComponentRiesz
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.MeasureTheory.Measure.Count
import HarmonicBalls.Proofs.Sec8.CircleDensityPolarIntegrability

/-!
# Bounded witnesses for subharmonic tests

A geometric localization and a conditional transport of the two source potentials.
The latter records the separate pointwise and almost-everywhere correction obligations;
it does not establish them. Leonardo Bonanno contributed to this formalization.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace
open scoped ENNReal NNReal

/-- A distributional Laplacian on an open set is unchanged by a
volume-almost-everywhere modification on that set. -/
theorem HasLaplacian.congr_ae_restrict_volume
    {U : Set ℂ} {f g : ℂ → ℝ} {α β : Measure ℂ}
    (hU : MeasurableSet U) (hf : HasLaplacian f α β U)
    (hfg : f =ᵐ[volume.restrict U] g) : HasLaplacian g α β U := by
  refine ⟨hf.1.congr hfg, fun φ hφ => ?_⟩
  have hfg' := (ae_restrict_iff' hU).1 hfg
  have heq : (fun x => f x * Laplacian.laplacian φ x) =ᵐ[volume]
      fun x => g x * Laplacian.laplacian φ x := by
    filter_upwards [hfg'] with x hx
    by_cases hxU : x ∈ U
    · rw [hx hxU]
    · rw [laplacian_eq_zero_of_notMem_tsupport (fun hx' => hxU (hφ.2.2 hx')),
        mul_zero, mul_zero]
  obtain ⟨hα, hβ, he⟩ := hf.2 φ hφ
  exact ⟨hα, hβ, (integral_congr_ae heq).symm.trans he⟩

/-- A locally finite Riesz measure carried by an open set is uniquely
determined by the distributional Laplacian there. -/
theorem rieszMeasure_eq_of_hasLaplacian_ae
    {U : Set ℂ} {f g : ℂ → ℝ} {ν η : Measure ℂ}
    (hU : IsOpen U) (hν : IsLocallyFiniteMeasure ν) (hη : IsLocallyFiniteMeasure η)
    (hνU : ν Uᶜ = 0) (hηU : η Uᶜ = 0)
    (hf : HasLaplacian f ν 0 U) (hg : HasLaplacian g η 0 U)
    (hfg : f =ᵐ[volume.restrict U] g) : ν = η := by
  have hf' := hf.congr_ae_restrict_volume hU.measurableSet hfg
  exact le_antisymm
    (measure_le_of_laplacianGE_hasLaplacian hU hη hνU hf'.laplacianGE hg)
    (measure_le_of_laplacianGE_hasLaplacian hU hν hηU hg.laplacianGE hf')

/-- Agreement with a unit point-source potential forces the local Riesz
measure of the replacement to have a unit atom at that point. -/
theorem rieszMeasure_singleton_eq_one_of_hasLaplacian_ae
    {U : Set ℂ} {f g : ℂ → ℝ} {η : Measure ℂ} {a : ℂ}
    (hU : IsOpen U) (ha : a ∈ U) (hη : IsLocallyFiniteMeasure η)
    (hf : HasLaplacian f (Measure.dirac a) 0 U)
    (hg : HasLaplacian g (η.restrict U) 0 U)
    (hfg : f =ᵐ[volume.restrict U] g) : η {a} = 1 := by
  let : IsLocallyFiniteMeasure η := hη
  have hdirac : Measure.dirac a Uᶜ = 0 := by simp [Measure.dirac_apply, ha]
  have hrestrict : (η.restrict U) Uᶜ = 0 := by simp [Measure.restrict_apply, hU.measurableSet]
  have heq : Measure.dirac a = η.restrict U :=
    rieszMeasure_eq_of_hasLaplacian_ae hU inferInstance inferInstance hdirac hrestrict hf hg hfg
  have hmass := congrArg (fun ν : Measure ℂ => ν {a}) heq
  simpa [Measure.restrict_apply, hU.measurableSet,
    inter_eq_left.mpr (singleton_subset_iff.mpr ha)] using hmass.symm

/-- The negative Newtonian kernel has a unit Dirac Riesz measure on every
open set, in the distributional sense. -/
theorem hasLaplacian_neg_newtonKernel (a : ℂ) (U : Set ℂ) :
    HasLaplacian (-newtonKernel a) (Measure.dirac a) 0 U := by
  refine ⟨((locallyIntegrable_newtonKernel a).neg).locallyIntegrableOn U,
    fun φ hφ => ⟨integrable_dirac enorm_lt_top, integrable_zero_measure, ?_⟩⟩
  simp only [Pi.neg_apply, neg_mul, integral_neg, integral_zero_measure, sub_zero,
    integral_dirac]
  rw [integral_newtonKernel_mul_laplacian (hφ.1.of_le (by norm_num)) hφ.2.1]
  simp

#print axioms HasLaplacian.congr_ae_restrict_volume
#print axioms rieszMeasure_eq_of_hasLaplacian_ae
#print axioms rieszMeasure_singleton_eq_one_of_hasLaplacian_ae
#print axioms hasLaplacian_neg_newtonKernel

/-- A finite positive source which vanishes on an open observation set has an
integrable Green kernel at every point of that set, even for an unbounded
original domain. -/
theorem integrable_greenFunction_of_source_null_on_open
    {O Λ K : Set ℂ} {ν : Measure ℂ} {x : ℂ}
    (hO : IsOpen O) (hΛ : IsOpen Λ) (hΛO : Λ ⊆ O)
    (hx : x ∈ Λ) (hK : IsCompact K) (hKO : K ⊆ O)
    (hν : IsFiniteMeasure ν) (hνK : ν Kᶜ = 0) (hνΛ : ν Λ = 0) :
    Integrable (greenFunction O x) ν := by
  obtain ⟨r, hr, hrΛ⟩ := Metric.isOpen_iff.mp hΛ x hx
  have hνball : ν (ball x r) = 0 := measure_mono_null hrΛ hνΛ
  have hνK' : ν (K \ ball x r)ᶜ = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hνK,
      measure_eq_zero_iff_ae_notMem.mp hνball] with y hyK hyball
    simp only [mem_compl_iff, not_not] at hyK
    simp only [mem_compl_iff, not_not]
    exact ⟨hyK, hyball⟩
  exact greenFunctionIntegrableAwayFromPoleStep_holds O (K \ ball x r) x ν hO
    (hΛO hx) (hK.diff isOpen_ball) (sdiff_subset.trans hKO)
    (fun h => h.2 (mem_ball_self hr)) hν hνK'

#print axioms integrable_greenFunction_of_source_null_on_open

/-- A smooth annular source has constant logarithmic potential in the disc
enclosed by its support. This includes all points of the inner disc, not merely
almost every point for an observation measure. -/
theorem circleDensity_log_potential_eq_center_of_mem_inner_ball
    {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hwidth : δ ≤ r * η)
    {z w : ℂ} (hw : ‖z - w‖ ≤ r - η) :
    (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x *
      Real.log ‖x - w‖) =
    (∫ x, (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x *
      Real.log ‖x - z‖) := by
  rw [integral_normalized_circleDensity_mul_log_norm_sub hr.le hδ,
    integral_normalized_circleDensity_mul_log_norm_sub hr.le hδ]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro ρ hρ
  have hρpos : 0 < ρ := hρ
  by_cases hzero : circleDensityRadialWeight r δ hδ ρ = 0
  · simp only [hzero, zero_mul]
  · have hnear := circleDensityRadialWeight_support_radius hr hδ hwidth hρpos.le hzero
    have hbound : ‖z - w‖ ≤ ρ := by
      rw [abs_lt] at hnear
      linarith [hnear.1]
    simp only [max_eq_left hbound, sub_self, norm_zero, max_eq_left hρpos.le]

#print axioms circleDensity_log_potential_eq_center_of_mem_inner_ball

/-- For a measurable observation set, requiring representatives for every measure is
exactly the pointwise representative problem. Counting measure tests every point. -/
theorem forall_hasBoundedSubharmonicRepresentatives_iff_pointwise
    {Λ : Set ℂ} {z : ℂ} (hΛ : MeasurableSet Λ) :
    (∀ μ : Measure ℂ, HasBoundedSubharmonicRepresentatives μ Λ z) ↔
      ∀ f ∈ subharmonicBallTestClass Λ z,
        ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
          f z = g z ∧ ∀ x ∈ Λ, f x = g x := by
  constructor
  · intro h f hf
    obtain ⟨g, hg, hz, hae⟩ := h Measure.count f hf
    refine ⟨g, hg, hz, ?_⟩
    have hpoint := (Measure.ae_count_iff).1 ((ae_restrict_iff' hΛ).1 hae)
    exact hpoint
  · intro h μ f hf
    obtain ⟨g, hg, hz, hpoint⟩ := h f hf
    exact ⟨g, hg, hz, ae_restrict_of_forall_mem hΛ hpoint⟩

#print axioms forall_hasBoundedSubharmonicRepresentatives_iff_pointwise

/-- Representatives for a dominating observation measure also work for every
absolutely continuous observation measure. -/
theorem hasBoundedSubharmonicRepresentatives_of_absolutelyContinuous
    {μ ν : Measure ℂ} {Λ : Set ℂ} {z : ℂ}
    (hμν : μ.restrict Λ ≪ ν.restrict Λ)
    (hν : HasBoundedSubharmonicRepresentatives ν Λ z) :
    HasBoundedSubharmonicRepresentatives μ Λ z := by
  intro f hf
  obtain ⟨g, hg, hz, hae⟩ := hν f hf
  exact ⟨g, hg, hz, hμν.ae_eq hae⟩

#print axioms hasBoundedSubharmonicRepresentatives_of_absolutelyContinuous

/-- Multiplying a bounded-domain test by a nonnegative constant preserves its
source, support and pole conditions. -/
theorem boundedSubharmonicBallTestClass_smul {Λ : Set ℂ} {z : ℂ} {f : ℂ → ℝ}
    (hf : f ∈ boundedSubharmonicBallTestClass Λ z) (c : ℝ≥0) :
    (c : ℝ) • f ∈ boundedSubharmonicBallTestClass Λ z := by
  obtain ⟨O, K, ν₁, ν₂, q, hO, hOb, hΛ, hK, hKO, hν₁, hν₂,
    hν₁K, hν₂K, hν₁Λ, hq, hν₂z, hi, hf⟩ := hf
  let : IsFiniteMeasure ν₁ := hν₁
  let : IsFiniteMeasure ν₂ := hν₂
  refine ⟨O, K, (c : ℝ≥0∞) • ν₁, (c : ℝ≥0∞) • ν₂, (c : ℝ) • q,
    hO, hOb, hΛ, hK, hKO, ν₁.smul_finite (by simp), ν₂.smul_finite (by simp),
    ?_, ?_, ?_, hq.const_smul, ?_, hi.smul_measure (by simp), ?_⟩
  · simp [hν₁K]
  · simp [hν₂K]
  · simp [hν₁Λ]
  · simp [hν₂z]
  · rw [hf]
    ext x
    simp [greenPotential, smul_eq_mul, NNReal.smul_def, mul_sub, mul_add]

#print axioms boundedSubharmonicBallTestClass_smul

/-- Subtracting a constant preserves bounded-domain subharmonic tests. -/
theorem boundedSubharmonicBallTestClass_sub_const {Λ : Set ℂ} {z : ℂ} {f : ℂ → ℝ}
    (hf : f ∈ boundedSubharmonicBallTestClass Λ z) (c : ℝ) :
    (fun x => f x - c) ∈ boundedSubharmonicBallTestClass Λ z := by
  obtain ⟨O, K, ν₁, ν₂, q, hO, hOb, hΛ, hK, hKO, hν₁, hν₂,
    hν₁K, hν₂K, hν₁Λ, hq, hν₂z, hi, hf⟩ := hf
  refine ⟨O, K, ν₁, ν₂, q - fun _ => c, hO, hOb, hΛ, hK, hKO,
    hν₁, hν₂, hν₁K, hν₂K, hν₁Λ, hq.sub (harmonicOnNhd_const c), hν₂z, hi, ?_⟩
  ext x
  simp only [Pi.sub_apply, hf, Pi.add_apply]
  ring

#print axioms boundedSubharmonicBallTestClass_sub_const

/-- Nonnegative scaling preserves the frozen class of subharmonic tests. -/
theorem subharmonicBallTestClass_smul {Λ : Set ℂ} {z : ℂ} {f : ℂ → ℝ}
    (hf : f ∈ subharmonicBallTestClass Λ z) (c : ℝ≥0) :
    (c : ℝ) • f ∈ subharmonicBallTestClass Λ z := by
  obtain ⟨O, K, ν₁, ν₂, q, hO, hΛ, hK, hKO, hν₁, hν₂,
    hν₁K, hν₂K, hν₁Λ, hq, hν₂z, hi, hf⟩ := hf
  let : IsFiniteMeasure ν₁ := hν₁
  let : IsFiniteMeasure ν₂ := hν₂
  refine ⟨O, K, (c : ℝ≥0∞) • ν₁, (c : ℝ≥0∞) • ν₂, (c : ℝ) • q,
    hO, hΛ, hK, hKO, ν₁.smul_finite (by simp), ν₂.smul_finite (by simp),
    ?_, ?_, ?_, hq.const_smul, ?_, hi.smul_measure (by simp), ?_⟩
  · simp [hν₁K]
  · simp [hν₂K]
  · simp [hν₁Λ]
  · simp [hν₂z]
  · rw [hf]
    ext x
    simp [greenPotential, smul_eq_mul, NNReal.smul_def, mul_sub, mul_add]

#print axioms subharmonicBallTestClass_smul

/-- Nonnegative scaling transports an individual bounded representative, including
its value at the pole and its almost-everywhere observation values. -/
theorem boundedSubharmonicRepresentative_smul
    {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ} {f g : ℂ → ℝ}
    (hg : g ∈ boundedSubharmonicBallTestClass Λ z)
    (hz : f z = g z) (hae : f =ᵐ[μ.restrict Λ] g) (c : ℝ≥0) :
    ∃ g' ∈ boundedSubharmonicBallTestClass Λ z,
      ((c : ℝ) • f) z = g' z ∧ (c : ℝ) • f =ᵐ[μ.restrict Λ] g' := by
  refine ⟨(c : ℝ) • g, boundedSubharmonicBallTestClass_smul hg c, ?_, ?_⟩
  · simp [hz]
  · filter_upwards [hae] with x hx
    simp [hx]

#print axioms boundedSubharmonicRepresentative_smul

/-- A finitely supported observation measure admits bounded representatives for the
whole frozen test class. The real part of a complex interpolating polynomial agrees
with each test at every observation point and at the pole. -/
theorem hasBoundedSubharmonicRepresentatives_of_ae_mem_finset
    {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ} (hΛ : Bornology.IsBounded Λ)
    (S : Finset ℂ) (hS : ∀ᵐ x ∂μ.restrict Λ, x ∈ S) :
    HasBoundedSubharmonicRepresentatives μ Λ z := by
  classical
  intro f hf
  let T := insert z S
  let P : Polynomial ℂ := Lagrange.interpolate T id (fun x => (f x : ℂ))
  let g : ℂ → ℝ := fun x => (P.eval x).re
  have hg : HarmonicOnNhd g univ := by
    intro x hx
    exact (AnalyticOnNhd.eval_polynomial P x (mem_univ x)).harmonicAt_re
  have heval : ∀ x ∈ T, g x = f x := by
    intro x hx
    have hi : Set.InjOn (id : ℂ → ℂ) T := fun _ _ _ _ h => h
    have h := Lagrange.eval_interpolate_at_node (fun x => (f x : ℂ)) hi hx
    simpa only [g, P, id_eq, Complex.ofReal_re] using congrArg Complex.re h
  refine ⟨g, harmonic_mem_boundedSubharmonicBallTestClass hΛ isOpen_univ
    (subset_univ _) hg, ?_, ?_⟩
  · exact (heval z (Finset.mem_insert_self z S)).symm
  · filter_upwards [hS] with x hx
    exact (heval x (Finset.mem_insert_of_mem hx)).symm

#print axioms hasBoundedSubharmonicRepresentatives_of_ae_mem_finset

/-- Every test admits a bounded representative when the observation measure is a
single point mass, independently of the point's location. -/
theorem hasBoundedSubharmonicRepresentatives_dirac {Λ : Set ℂ} {z x : ℂ}
    (hΛ : Bornology.IsBounded Λ) :
    HasBoundedSubharmonicRepresentatives (Measure.dirac x) Λ z := by
  apply hasBoundedSubharmonicRepresentatives_of_ae_mem_finset hΛ {x}
  apply ae_restrict_of_ae
  simp only [ae_dirac_eq, Filter.eventually_pure, Finset.mem_singleton]

#print axioms hasBoundedSubharmonicRepresentatives_dirac

/-- A bounded observation set and a compact source fit in a bounded open subset of
any given open witness. -/
theorem exists_bounded_open_containing_closure_and_compact
    {Λ O K : Set ℂ} (hΛ : Bornology.IsBounded Λ) (hO : IsOpen O)
    (hΛO : closure Λ ⊆ O) (hK : IsCompact K) (hKO : K ⊆ O) :
    ∃ V : Set ℂ, IsOpen V ∧ Bornology.IsBounded V ∧ V ⊆ O ∧
      closure Λ ⊆ V ∧ K ⊆ V := by
  obtain ⟨R, hR⟩ := (hΛ.closure.union hK.isBounded).subset_ball (0 : ℂ)
  refine ⟨O ∩ ball 0 R, hO.inter isOpen_ball,
    isBounded_ball.subset inter_subset_right, inter_subset_left, ?_, ?_⟩
  · exact subset_inter hΛO (subset_union_left.trans hR)
  · exact subset_inter hKO (subset_union_right.trans hR)

/-- Transport a specific witness through two harmonic corrections, provided the old
and new real-valued potentials agree after correction at the pole and almost everywhere.
The two source measures and all their support and sign conditions remain unchanged.
The new negative kernel's pole integrability is a separate hypothesis. -/
theorem bounded_representative_of_source_corrections
    {μ ν₁ ν₂ : Measure ℂ} {Λ O V K : Set ℂ} {z : ℂ}
    {q a b : ℂ → ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVO : V ⊆ O)
    (hΛV : closure Λ ⊆ V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hν₁ : IsFiniteMeasure ν₁) (hν₂ : IsFiniteMeasure ν₂)
    (h₁ : ν₁ Kᶜ = 0) (h₂ : ν₂ Kᶜ = 0) (hΛ₁ : ν₁ Λ = 0)
    (hq : HarmonicOnNhd q O) (ha : HarmonicOnNhd a V) (hb : HarmonicOnNhd b V)
    (hz : ν₂ {z} = 0) (hi : Integrable (greenFunction V z) ν₂)
    (h₁z : greenPotential O ν₁ z = a z + greenPotential V ν₁ z)
    (h₂z : greenPotential O ν₂ z = b z + greenPotential V ν₂ z)
    (h₁ae : ∀ᵐ x ∂μ.restrict Λ,
      greenPotential O ν₁ x = a x + greenPotential V ν₁ x)
    (h₂ae : ∀ᵐ x ∂μ.restrict Λ,
      greenPotential O ν₂ x = b x + greenPotential V ν₂ x) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (q + greenPotential O ν₁ - greenPotential O ν₂) z = g z ∧
      (q + greenPotential O ν₁ - greenPotential O ν₂) =ᵐ[μ.restrict Λ] g := by
  let g := (q + a - b) + greenPotential V ν₁ - greenPotential V ν₂
  refine ⟨g, ⟨V, K, ν₁, ν₂, q + a - b, hV, hVb, hΛV, hK, hKV,
    hν₁, hν₂, h₁, h₂, hΛ₁, ((hq.mono hVO).add ha).sub hb, hz, hi, rfl⟩, ?_, ?_⟩
  · dsimp [g, Pi.add_apply, Pi.sub_apply]
    rw [h₁z, h₂z]
    ring
  · filter_upwards [h₁ae, h₂ae] with x hx₁ hx₂
    dsimp [g, Pi.add_apply, Pi.sub_apply]
    rw [hx₁, hx₂]
    ring

/-- Transport a witness using replacement sources and a single harmonic correction
for the signed potential. The replacement sources must independently satisfy all
compact-support, sign, and pole conditions, and the correction identity is required
both at the pole and almost everywhere on the observation set. -/
theorem bounded_representative_of_changed_sources
    {μ ν₁ ν₂ η₁ η₂ : Measure ℂ} {Λ O V K : Set ℂ} {z : ℂ}
    {q a : ℂ → ℝ}
    (hV : IsOpen V) (hVb : Bornology.IsBounded V) (hVO : V ⊆ O)
    (hΛV : closure Λ ⊆ V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hη₁ : IsFiniteMeasure η₁) (hη₂ : IsFiniteMeasure η₂)
    (h₁ : η₁ Kᶜ = 0) (h₂ : η₂ Kᶜ = 0) (hΛ₁ : η₁ Λ = 0)
    (hq : HarmonicOnNhd q O) (ha : HarmonicOnNhd a V)
    (hz : η₂ {z} = 0) (hi : Integrable (greenFunction V z) η₂)
    (hcorrectz : (greenPotential O ν₁ - greenPotential O ν₂) z =
      (a + greenPotential V η₁ - greenPotential V η₂) z)
    (hcorrectae : (greenPotential O ν₁ - greenPotential O ν₂) =ᵐ[μ.restrict Λ]
      (a + greenPotential V η₁ - greenPotential V η₂)) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (q + greenPotential O ν₁ - greenPotential O ν₂) z = g z ∧
      (q + greenPotential O ν₁ - greenPotential O ν₂) =ᵐ[μ.restrict Λ] g := by
  let g := (q + a) + greenPotential V η₁ - greenPotential V η₂
  refine ⟨g, ⟨V, K, η₁, η₂, q + a, hV, hVb, hΛV, hK, hKV,
    hη₁, hη₂, h₁, h₂, hΛ₁, (hq.mono hVO).add ha, hz, hi, rfl⟩, ?_, ?_⟩
  · dsimp [g, Pi.add_apply, Pi.sub_apply] at hcorrectz ⊢
    linarith
  · filter_upwards [hcorrectae] with x hx
    dsimp [g, Pi.add_apply, Pi.sub_apply] at hx ⊢
    linarith

#print axioms bounded_representative_of_changed_sources

/-- The diagonal convention forces a source-by-source correction for a Dirac mass
    to vanish at its atom, for any two domains. -/
theorem dirac_source_correction_at_atom {O V : Set ℂ} {x : ℂ} {a : ℂ → ℝ}
    (h : greenPotential O (Measure.dirac x) x =
      a x + greenPotential V (Measure.dirac x) x) : a x = 0 := by
  simpa only [greenPotential_dirac_self, add_zero] using h.symm

/-- The logarithmic kernel has no harmonic minorant on the whole plane. -/
theorem not_isHarmonicMinorant_univ_newtonKernel (x : ℂ) (h : ℂ → ℝ) :
    ¬ IsHarmonicMinorant univ (newtonKernelEReal x) h := by
  intro hh
  let r : ℝ := Real.exp (-(2 * Real.pi) * (h x - 1))
  have hr : 0 < r := Real.exp_pos _
  have hb := hh.le_neg_mul_log_radius hr (subset_univ (closedBall x r)) (by simpa using hr)
  dsimp [r] at hb
  rw [Real.log_exp] at hb
  have hp : (2 * Real.pi) ≠ 0 := by positivity
  field_simp at hb
  nlinarith [Real.pi_pos]

/-- The frozen whole-plane kernel is the Newtonian kernel, including its diagonal value. -/
theorem greenFunction_univ_eq_newtonKernel (x y : ℂ) :
    greenFunction univ x y = newtonKernel x y := by
  by_cases hxy : x = y
  · subst y
    simp [greenFunction_self, newtonKernel]
  · have hb : greatestHarmonicMinorant univ (newtonKernelEReal x) y = ⊥ := by
      simp [greatestHarmonicMinorant, not_isHarmonicMinorant_univ_newtonKernel]
    simp [greenFunction, hxy, hb]

#print axioms not_isHarmonicMinorant_univ_newtonKernel
#print axioms greenFunction_univ_eq_newtonKernel

/-- A replacement agreeing almost everywhere with a whole-plane negative
Dirac potential has a unit Riesz atom if its local distributional Laplacian
is represented by the restriction of its negative source. -/
theorem negative_source_unit_atom_of_ae_dirac_and_hasLaplacian
    {U : Set ℂ} {g : ℂ → ℝ} {η : Measure ℂ} {a : ℂ}
    (hU : IsOpen U) (ha : a ∈ U) (hη : IsLocallyFiniteMeasure η)
    (hg : HasLaplacian g (η.restrict U) 0 U)
    (heq : -greenPotential univ (Measure.dirac a) =ᵐ[volume.restrict U] g) :
    η {a} = 1 := by
  apply rieszMeasure_singleton_eq_one_of_hasLaplacian_ae hU ha hη
    (hasLaplacian_neg_newtonKernel a U) hg
  filter_upwards [heq] with x hx
  simpa [greenPotential, greenFunction_univ_eq_newtonKernel, newtonKernel_comm x a] using hx

#print axioms negative_source_unit_atom_of_ae_dirac_and_hasLaplacian

/-- The whole-plane Green potential of a smooth annular source is constant
inside its inner disc, including pointwise values for arbitrary observers. -/
theorem greenPotential_univ_circleDensity_eq_center_of_mem_inner_ball
    {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hwidth : δ ≤ r * η)
    {z w : ℂ} (hw : ‖z - w‖ ≤ r - η) :
    greenPotential univ (volume.withDensity (fun x => ENNReal.ofReal
      ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x))) w =
    greenPotential univ (volume.withDensity (fun x => ENNReal.ofReal
      ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x))) z := by
  let density : ℂ → ℝ := fun x =>
    (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x
  have hd : Continuous density := continuous_const.mul (circleDensity_contDiff r δ hδ z).continuous
  have hnonneg : ∀ x, 0 ≤ density x := fun x =>
    mul_nonneg (inv_nonneg.mpr (circleDensity_integral_pos hr.le hδ 0).le)
      (circleDensity_nonneg r δ hδ z x)
  change greenPotential univ (volume.withDensity (fun x => ENNReal.ofReal (density x))) w =
    greenPotential univ (volume.withDensity (fun x => ENNReal.ofReal (density x))) z
  simp only [greenPotential, greenFunction_univ_eq_newtonKernel]
  rw [integral_withDensity_eq_integral_toReal_smul hd.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _,
    integral_withDensity_eq_integral_toReal_smul hd.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) _]
  simp only [ENNReal.toReal_ofReal (hnonneg _), smul_eq_mul, newtonKernel]
  simp_rw [show ∀ x t : ℝ, x * (-(2 * Real.pi)⁻¹ * t) =
    -(2 * Real.pi)⁻¹ * (x * t) by intros; ring]
  rw [integral_const_mul, integral_const_mul]
  congr 1
  simpa only [norm_sub_rev] using
    circleDensity_log_potential_eq_center_of_mem_inner_ball hr hδ hwidth hw

#print axioms greenPotential_univ_circleDensity_eq_center_of_mem_inner_ball

/-- The whole-plane kernel is integrable against a smooth annular density at
every pole, including poles in the annulus. -/
theorem integrable_greenFunction_univ_circleDensity
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z p : ℂ) :
    Integrable (greenFunction univ p) (volume.withDensity (fun x => ENNReal.ofReal
      ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x))) := by
  let density : ℂ → ℝ := fun x =>
    (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x
  have hd : Continuous density := continuous_const.mul (circleDensity_contDiff r δ hδ z).continuous
  have hn : ∀ x, 0 ≤ density x := fun x =>
    mul_nonneg (inv_nonneg.mpr (circleDensity_integral_pos hr.le hδ 0).le)
      (circleDensity_nonneg r δ hδ z x)
  apply (integrable_withDensity_iff_integrable_smul' hd.measurable.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).2
  have h := (integrable_circleDensity_mul_log_norm_sub hr.le hδ z p).const_mul
    ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * (-(2 * Real.pi)⁻¹))
  convert h using 1
  ext x
  simp only [ENNReal.toReal_ofReal (hn x), smul_eq_mul, greenFunction_univ_eq_newtonKernel,
    newtonKernel, density, norm_sub_rev]
  ring

#print axioms integrable_greenFunction_univ_circleDensity

/-- A whole-plane annular source can be removed entirely when the pole and
observation set lie inside the shell. The observation measure is arbitrary. -/
theorem univ_circleDensity_has_bounded_representative
    {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hwidth : δ ≤ r * η)
    {Λ : Set ℂ} {z p : ℂ} {μ : Measure ℂ}
    (hΛb : Bornology.IsBounded Λ) (hΛm : MeasurableSet Λ)
    (hΛ : ∀ x ∈ Λ, ‖z - x‖ ≤ r - η) (hp : ‖z - p‖ ≤ r - η) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ p,
      (-greenPotential univ (volume.withDensity (fun x => ENNReal.ofReal
        ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x)))) p = g p ∧
      (-greenPotential univ (volume.withDensity (fun x => ENNReal.ofReal
        ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x))))
          =ᵐ[μ.restrict Λ] g := by
  let ν := volume.withDensity (fun x => ENNReal.ofReal
    ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x))
  let g : ℂ → ℝ := fun _ => -greenPotential univ ν z
  refine ⟨g, harmonic_mem_boundedSubharmonicBallTestClass hΛb isOpen_univ
    (subset_univ _) (harmonicOnNhd_const _), ?_, ?_⟩
  · change -greenPotential univ ν p = -greenPotential univ ν z
    rw [greenPotential_univ_circleDensity_eq_center_of_mem_inner_ball hr hδ hwidth hp]
  · apply ae_restrict_of_forall_mem hΛm
    intro x hx
    change -greenPotential univ ν x = -greenPotential univ ν z
    rw [greenPotential_univ_circleDensity_eq_center_of_mem_inner_ball hr hδ hwidth (hΛ x hx)]

#print axioms univ_circleDensity_has_bounded_representative

/-- An existing representative for an arbitrary negative source survives the
addition of an annular source surrounding the observations. Integrability of
the original kernel is required at the pole and almost everywhere, so the
Bochner integral's nonintegrable values are not silently changed. -/
theorem univ_add_circleDensity_has_bounded_representative
    {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hwidth : δ ≤ r * η)
    {μ ν : Measure ℂ} {Λ : Set ℂ} {p z : ℂ}
    (hΛm : MeasurableSet Λ) (hΛ : ∀ x ∈ Λ, ‖z - x‖ ≤ r - η)
    (hp : ‖z - p‖ ≤ r - η)
    (hip : Integrable (greenFunction univ p) ν)
    (hiae : ∀ᵐ x ∂μ.restrict Λ, Integrable (greenFunction univ x) ν)
    (hrep : ∃ g ∈ boundedSubharmonicBallTestClass Λ p,
      (-greenPotential univ ν) p = g p ∧ (-greenPotential univ ν) =ᵐ[μ.restrict Λ] g) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ p,
      (-greenPotential univ (ν + volume.withDensity (fun x => ENNReal.ofReal
        ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x)))) p = g p ∧
      (-greenPotential univ (ν + volume.withDensity (fun x => ENNReal.ofReal
        ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x))))
          =ᵐ[μ.restrict Λ] g := by
  let σ := volume.withDensity (fun x => ENNReal.ofReal
    ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x))
  obtain ⟨g, hg, hgp, hgae⟩ := hrep
  refine ⟨fun x => g x - greenPotential univ σ z,
    boundedSubharmonicBallTestClass_sub_const hg _, ?_, ?_⟩
  · have hsum : greenPotential univ (ν + σ) p =
        greenPotential univ ν p + greenPotential univ σ p :=
      integral_add_measure hip (integrable_greenFunction_univ_circleDensity hr hδ z p)
    simp only [Pi.neg_apply] at hgp ⊢
    rw [hsum, greenPotential_univ_circleDensity_eq_center_of_mem_inner_ball hr hδ hwidth hp]
    linarith
  · have hs : ∀ᵐ x ∂μ.restrict Λ, ‖z - x‖ ≤ r - η :=
      ae_restrict_of_forall_mem hΛm hΛ
    filter_upwards [hiae, hgae, hs] with x hix hgx hx
    have hsum : greenPotential univ (ν + σ) x =
        greenPotential univ ν x + greenPotential univ σ x :=
      integral_add_measure hix (integrable_greenFunction_univ_circleDensity hr hδ z x)
    simp only [Pi.neg_apply] at hgx ⊢
    rw [hsum, greenPotential_univ_circleDensity_eq_center_of_mem_inner_ball hr hδ hwidth hx]
    linarith

#print axioms univ_add_circleDensity_has_bounded_representative

open Classical in
/-- Adding an integrable source has a different effect at points where the
original kernel is not integrable: the totalized Bochner integral is zero. -/
theorem greenPotential_add_integrable_source
    {O : Set ℂ} {ν σ : Measure ℂ} {x : ℂ}
    (hσ : Integrable (greenFunction O x) σ) :
    greenPotential O (ν + σ) x =
      if Integrable (greenFunction O x) ν then
        greenPotential O ν x + greenPotential O σ x
      else 0 := by
  by_cases hν : Integrable (greenFunction O x) ν
  · simp only [hν, ↓reduceIte]
    exact integral_add_measure hν hσ
  · simp only [hν, ↓reduceIte, greenPotential]
    exact integral_undef (fun h => hν h.left_of_add_measure)

/-- A source with zero potential at a point can be added without changing
the totalized potential, even when the original source is not integrable. -/
theorem greenPotential_add_zero_source
    {O : Set ℂ} {ν σ : Measure ℂ} {x : ℂ}
    (hσ : Integrable (greenFunction O x) σ)
    (hz : greenPotential O σ x = 0) :
    greenPotential O (ν + σ) x = greenPotential O ν x := by
  classical
  rw [greenPotential_add_integrable_source hσ]
  by_cases hν : Integrable (greenFunction O x) ν
  · simp [hν, hz]
  · simp only [hν, ↓reduceIte, greenPotential, integral_undef hν]

/-- A zero-potential added source preserves a bounded representative at the
pole and almost everywhere, without requiring integrability of the old source
at any observation point. -/
theorem neg_greenPotential_add_zero_source_has_bounded_representative
    {μ ν σ : Measure ℂ} {Λ O : Set ℂ} {p : ℂ}
    (hσp : Integrable (greenFunction O p) σ)
    (hσae : ∀ᵐ x ∂μ.restrict Λ, Integrable (greenFunction O x) σ)
    (hzp : greenPotential O σ p = 0)
    (hzae : ∀ᵐ x ∂μ.restrict Λ, greenPotential O σ x = 0)
    (hrep : ∃ g ∈ boundedSubharmonicBallTestClass Λ p,
      (-greenPotential O ν) p = g p ∧ (-greenPotential O ν) =ᵐ[μ.restrict Λ] g) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ p,
      (-greenPotential O (ν + σ)) p = g p ∧
        (-greenPotential O (ν + σ)) =ᵐ[μ.restrict Λ] g := by
  obtain ⟨g, hg, hgp, hgae⟩ := hrep
  refine ⟨g, hg, ?_, ?_⟩
  · simpa only [Pi.neg_apply, greenPotential_add_zero_source hσp hzp] using hgp
  · filter_upwards [hσae, hzae, hgae] with x hσx hzx hx
    simpa only [Pi.neg_apply, greenPotential_add_zero_source hσx hzx] using hx

#print axioms greenPotential_add_integrable_source
#print axioms greenPotential_add_zero_source
#print axioms neg_greenPotential_add_zero_source_has_bounded_representative

/-- Angular measure on the unit circle centered at `z`. -/
noncomputable def unitCircleSource (z : ℂ) : Measure ℂ :=
  Measure.map (circleMap z 1) (volume.restrict (Ioc 0 (2 * Real.pi)))

/-- The unit-circle source has an integrable whole-plane kernel at every
point strictly inside the circle. -/
theorem integrable_greenFunction_univ_unitCircleSource {z x : ℂ} (hx : ‖x - z‖ < 1) :
    Integrable (greenFunction univ x) (unitCircleSource z) := by
  have hm : Measurable (newtonKernel x) := by
    unfold newtonKernel
    fun_prop
  have hs : x ∉ sphere z (1 : ℝ) := by
    intro h
    rw [mem_sphere, dist_eq_norm] at h
    linarith
  have hc : CircleIntegrable (newtonKernel x) z 1 :=
    (continuousOn_newtonKernel_sphere hs).circleIntegrable (by norm_num)
  have hi : IntegrableOn (fun θ => newtonKernel x (circleMap z 1 θ))
      (Ioc 0 (2 * Real.pi)) := by
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).1 hc
  have heq : greenFunction univ x = newtonKernel x := by
    funext y
    exact greenFunction_univ_eq_newtonKernel x y
  rw [heq]
  exact (integrable_map_measure hm.aestronglyMeasurable
    (continuous_circleMap z 1).aemeasurable).2 hi

/-- The whole-plane potential of angular measure on a unit circle vanishes
pointwise throughout the circle's interior. -/
theorem greenPotential_univ_unitCircleSource_eq_zero {z x : ℂ} (hx : ‖x - z‖ < 1) :
    greenPotential univ (unitCircleSource z) x = 0 := by
  have hm : Measurable (newtonKernel x) := by
    unfold newtonKernel
    fun_prop
  have hc := circleAverage_newtonKernel (x := x) (y := z) (r := 1) (by norm_num) hx.le
  have hp : (2 * Real.pi : ℝ)⁻¹ ≠ 0 := by positivity
  rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity)] at hc
  simp only [Real.log_one, mul_zero, smul_eq_mul] at hc
  have hz : (∫ θ in Ioc (0 : ℝ) (2 * Real.pi),
      newtonKernel x (circleMap z 1 θ)) = 0 := (mul_eq_zero.mp hc).resolve_left hp
  unfold greenPotential unitCircleSource
  simp_rw [greenFunction_univ_eq_newtonKernel]
  rw [integral_map (continuous_circleMap z 1).aemeasurable hm.aestronglyMeasurable]
  exact hz

/-- The unit-circle source has strictly positive finite total mass. -/
theorem unitCircleSource_apply_univ (z : ℂ) :
    unitCircleSource z univ = ENNReal.ofReal (2 * Real.pi) := by
  rw [unitCircleSource, Measure.map_apply (continuous_circleMap z 1).measurable MeasurableSet.univ]
  simp [Real.volume_Ioc]

/-- Angular measure has finite mass and is concentrated on its unit circle. -/
theorem unitCircleSource_finite_and_concentrated (z : ℂ) :
    IsFiniteMeasure (unitCircleSource z) ∧ unitCircleSource z (sphere z 1)ᶜ = 0 := by
  constructor
  · exact ⟨by rw [unitCircleSource_apply_univ]; exact ENNReal.ofReal_lt_top⟩
  · rw [unitCircleSource, Measure.map_apply (continuous_circleMap z 1).measurable
      (isClosed_sphere.measurableSet.compl)]
    have hempty : circleMap z 1 ⁻¹' (sphere z 1)ᶜ = ∅ := by
      ext θ
      simp
    rw [hempty, measure_empty]

/-- The angular measure does not charge any point in the circle's interior. -/
theorem unitCircleSource_singleton_eq_zero {z p : ℂ} (hp : ‖p - z‖ < 1) :
    unitCircleSource z {p} = 0 := by
  have hpK : p ∈ (sphere z (1 : ℝ))ᶜ := by
    change p ∉ sphere z (1 : ℝ)
    intro h
    rw [mem_sphere, dist_eq_norm] at h
    linarith
  exact measure_mono_null (singleton_subset_iff.2 hpK)
    (unitCircleSource_finite_and_concentrated z).2

/-- The circle source gives an admissible whole-plane negative-source test
at every pole strictly inside the circle. -/
theorem neg_univ_unitCircleSource_mem_subharmonicBallTestClass
    {z p : ℂ} (hp : ‖p - z‖ < 1) (Λ : Set ℂ) :
    -greenPotential univ (unitCircleSource z) ∈ subharmonicBallTestClass Λ p := by
  let K : Set ℂ := sphere z 1
  have hK : IsCompact K := isCompact_sphere z 1
  obtain ⟨hfinite, hsupport⟩ := unitCircleSource_finite_and_concentrated z
  have hnull := unitCircleSource_singleton_eq_zero hp
  refine ⟨univ, K, 0, unitCircleSource z, 0, isOpen_univ, subset_univ _, hK,
    subset_univ _, inferInstance, hfinite, by simp, hsupport, by simp,
    harmonicOnNhd_const 0, hnull, integrable_greenFunction_univ_unitCircleSource hp, ?_⟩
  ext x
  simp [greenPotential]

/-- A compactly supported finite negative source can be augmented by angular
measure while retaining every frozen source and pole condition. -/
theorem neg_univ_add_unitCircleSource_mem_subharmonicBallTestClass
    {ν : Measure ℂ} {K Λ : Set ℂ} {z p : ℂ}
    (hK : IsCompact K) (hν : IsFiniteMeasure ν) (hνK : ν Kᶜ = 0)
    (hνp : ν {p} = 0) (hi : Integrable (greenFunction univ p) ν)
    (hp : ‖p - z‖ < 1) :
    -greenPotential univ (ν + unitCircleSource z) ∈ subharmonicBallTestClass Λ p := by
  obtain ⟨hσ, hσK⟩ := unitCircleSource_finite_and_concentrated z
  let : IsFiniteMeasure ν := hν
  let : IsFiniteMeasure (unitCircleSource z) := hσ
  refine ⟨univ, K ∪ sphere z 1, 0, ν + unitCircleSource z, 0, isOpen_univ,
    subset_univ _, hK.union (isCompact_sphere z 1), subset_univ _, inferInstance,
    inferInstance, by simp, ?_, by simp, harmonicOnNhd_const 0, ?_,
    hi.add_measure (integrable_greenFunction_univ_unitCircleSource hp), ?_⟩
  · rw [Measure.add_apply]
    have hνzero : ν (K ∪ sphere z 1)ᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr (subset_union_left)) hνK
    have hσzero : unitCircleSource z (K ∪ sphere z 1)ᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr (subset_union_right)) hσK
    exact add_eq_zero.mpr ⟨hνzero, hσzero⟩
  · simp [hνp, unitCircleSource_singleton_eq_zero hp]
  · ext x
    simp [greenPotential]

/-- Adding a nonzero unit-circle source preserves an existing representative
without assuming integrability of the original source on the observation set. -/
theorem univ_add_unitCircleSource_has_bounded_representative
    {μ ν : Measure ℂ} {Λ : Set ℂ} {p z : ℂ}
    (hΛm : MeasurableSet Λ) (hΛ : ∀ x ∈ Λ, ‖x - z‖ < 1) (hp : ‖p - z‖ < 1)
    (hrep : ∃ g ∈ boundedSubharmonicBallTestClass Λ p,
      (-greenPotential univ ν) p = g p ∧ (-greenPotential univ ν) =ᵐ[μ.restrict Λ] g) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ p,
      (-greenPotential univ (ν + unitCircleSource z)) p = g p ∧
        (-greenPotential univ (ν + unitCircleSource z)) =ᵐ[μ.restrict Λ] g := by
  apply neg_greenPotential_add_zero_source_has_bounded_representative
    (integrable_greenFunction_univ_unitCircleSource hp) _
    (greenPotential_univ_unitCircleSource_eq_zero hp) _ hrep
  · exact ae_restrict_of_forall_mem hΛm fun x hx =>
      integrable_greenFunction_univ_unitCircleSource (hΛ x hx)
  · exact ae_restrict_of_forall_mem hΛm fun x hx =>
      greenPotential_univ_unitCircleSource_eq_zero (hΛ x hx)

#print axioms integrable_greenFunction_univ_unitCircleSource
#print axioms greenPotential_univ_unitCircleSource_eq_zero
#print axioms unitCircleSource_apply_univ
#print axioms unitCircleSource_finite_and_concentrated
#print axioms unitCircleSource_singleton_eq_zero
#print axioms neg_univ_unitCircleSource_mem_subharmonicBallTestClass
#print axioms neg_univ_add_unitCircleSource_mem_subharmonicBallTestClass
#print axioms univ_add_unitCircleSource_has_bounded_representative

/-- The annular whole-plane potential is a valid frozen test for every pole;
the source is compactly supported, finite, and non-atomic. -/
theorem neg_univ_circleDensity_mem_subharmonicBallTestClass
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z : ℂ) (Λ : Set ℂ) (p : ℂ) :
    -greenPotential univ (volume.withDensity (fun x => ENNReal.ofReal
      ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x))) ∈
      subharmonicBallTestClass Λ p := by
  let density : ℂ → ℝ := fun x =>
    (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x
  let ν := volume.withDensity (fun x => ENNReal.ofReal (density x))
  let K := tsupport (circleDensity r δ hδ z)
  have hd : Continuous density := continuous_const.mul (circleDensity_contDiff r δ hδ z).continuous
  have hdi : Integrable density volume := by
    exact ((circleDensity_contDiff r δ hδ z).continuous.integrable_of_hasCompactSupport
      (circleDensity_hasCompactSupport hr.le hδ z)).const_mul _
  have hν : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hdi.hasFiniteIntegral
  have hK : IsCompact K := circleDensity_hasCompactSupport hr.le hδ z
  have hνK : ν Kᶜ = 0 := by
    rw [withDensity_apply _ hK.isClosed.measurableSet.compl]
    apply (lintegral_eq_zero_iff hd.measurable.ennreal_ofReal).2
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet.compl] with x hx
    have hx0 : circleDensity r δ hδ z x = 0 := by
      by_contra hx'
      exact hx (subset_closure hx')
    simp [density, hx0]
  have hνp : ν {p} = 0 :=
    (withDensity_absolutelyContinuous volume _) (measure_singleton p)
  have hi : Integrable (greenFunction univ p) ν := by
    exact integrable_greenFunction_univ_circleDensity hr hδ z p
  refine ⟨univ, K, 0, ν, 0, isOpen_univ, subset_univ _, hK, subset_univ _,
    inferInstance, hν, by simp, hνK, by simp, harmonicOnNhd_const 0, hνp, hi, ?_⟩
  change -greenPotential univ ν = (0 : ℂ → ℝ) + greenPotential univ 0 - greenPotential univ ν
  ext x
  simp [greenPotential]

#print axioms neg_univ_circleDensity_mem_subharmonicBallTestClass

/-- The annular source used above is a probability measure. -/
theorem circleDensity_source_isProbabilityMeasure
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z : ℂ) :
    IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal
      ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x))) := by
  let density : ℂ → ℝ := fun x =>
    (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x
  have hi : Integrable density volume :=
    ((circleDensity_contDiff r δ hδ z).continuous.integrable_of_hasCompactSupport
      (circleDensity_hasCompactSupport hr.le hδ z)).const_mul _
  have hn : 0 ≤ᵐ[volume] density := Filter.Eventually.of_forall fun x =>
    mul_nonneg (inv_nonneg.mpr (circleDensity_integral_pos hr.le hδ 0).le)
      (circleDensity_nonneg r δ hδ z x)
  refine ⟨?_⟩
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi hn]
  simp only [density, circleDensity_normalized_integral hr.le hδ z, ENNReal.ofReal_one]

#print axioms circleDensity_source_isProbabilityMeasure

/-- The potential of a point mass at the centre of a disc. -/
theorem greenPotential_dirac_zero_ball {R : ℝ} (hR : 0 < R) {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) R) (hx0 : x ≠ 0) :
    greenPotential (ball 0 R) (Measure.dirac 0) x =
      (2 * Real.pi)⁻¹ * (Real.log R - Real.log ‖x‖) := by
  rw [greenPotential, integral_dirac, greenFunction_ball_comm, greenFunction_ball
    (mem_ball_self hR) hx (Ne.symm hx0)]
  unfold greenBall
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
  simp only [map_zero, zero_mul, sub_zero, zero_sub, norm_neg, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hR, norm_pow]
  rw [Real.log_div (pow_ne_zero 2 hR0) (mul_ne_zero hR0 hxnorm),
    Real.log_pow, Real.log_mul hR0 hxnorm]
  ring

/-- The unit disc reproduces the whole-plane potential of a Dirac mass at its centre,
including the real-valued diagonal convention. -/
theorem greenPotential_univ_dirac_zero_eq_unitDisc {x : ℂ}
    (hx : x ∈ ball (0 : ℂ) 1) :
    greenPotential univ (Measure.dirac 0) x =
      greenPotential (ball 0 1) (Measure.dirac 0) x := by
  by_cases hx0 : x = 0
  · subst x
    simp [greenPotential_dirac_self]
  · rw [greenPotential_dirac_zero_ball (by norm_num) hx hx0]
    simp [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel, newtonKernel]

#print axioms greenPotential_univ_dirac_zero_eq_unitDisc

/-- Off the source atom, the disc and whole-plane point potentials differ by
the harmonic minorant, without a condition on its diagonal value. -/
theorem greenPotential_univ_dirac_eq_ball_add_harmonic_of_ne
    {R : ℝ} {a x : ℂ} (hR : 0 < R) (ha : a ∈ ball (0 : ℂ) R)
    (hx : x ∈ ball (0 : ℂ) R) (hxa : x ≠ a) :
    greenPotential univ (Measure.dirac a) x =
      greatestHarmonicMinorantBall R a x + greenPotential (ball 0 R) (Measure.dirac a) x := by
  have hpos := norm_sub_conj_mul_pos hR (mem_ball_zero_iff.1 ha)
    (mem_ball_zero_iff.1 hx).le
  have heq := newtonKernel_sub_greenBall hR (Ne.symm hxa) hpos.ne'
  rw [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel,
    newtonKernel_comm x a, greenPotential, integral_dirac, greenFunction_ball_comm,
    greenFunction_ball ha hx (Ne.symm hxa)]
  linarith

#print axioms greenPotential_univ_dirac_eq_ball_add_harmonic_of_ne

/-- If the disc's harmonic correction vanishes at the source atom, the
whole-plane and disc point potentials agree after harmonic correction even at the
atom, where both kernels use the frozen diagonal value. -/
theorem greenPotential_univ_dirac_eq_ball_add_harmonic
    {R : ℝ} {a x : ℂ} (hR : 0 < R) (ha : a ∈ ball (0 : ℂ) R)
    (hdiag : ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * a‖ = R)
    (hx : x ∈ ball (0 : ℂ) R) :
    greenPotential univ (Measure.dirac a) x =
      greatestHarmonicMinorantBall R a x + greenPotential (ball 0 R) (Measure.dirac a) x := by
  by_cases hxa : x = a
  · subst x
    rw [greenPotential_dirac_self, greenPotential_dirac_self]
    simp [greatestHarmonicMinorantBall, hdiag]
  · have hpos := norm_sub_conj_mul_pos hR (mem_ball_zero_iff.1 ha)
      (mem_ball_zero_iff.1 hx).le
    have heq := newtonKernel_sub_greenBall hR (Ne.symm hxa) hpos.ne'
    rw [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel,
      newtonKernel_comm x a, greenPotential, integral_dirac, greenFunction_ball_comm,
      greenFunction_ball ha hx (Ne.symm hxa)]
    linarith

#print axioms greenPotential_univ_dirac_eq_ball_add_harmonic

/-- The negative whole-plane Dirac potential is a test whenever the pole is distinct
from the source atom. -/
theorem neg_univ_dirac_zero_mem_subharmonicBallTestClass {Λ : Set ℂ} {z : ℂ}
    (hz0 : z ≠ 0) :
    -greenPotential univ (Measure.dirac 0) ∈ subharmonicBallTestClass Λ z := by
  classical
  refine ⟨univ, {0}, 0, Measure.dirac 0, 0, isOpen_univ, subset_univ _,
    isCompact_singleton, subset_univ _, inferInstance, inferInstance, ?_, ?_, ?_,
    harmonicOnNhd_const 0, ?_, integrable_dirac enorm_lt_top, ?_⟩
  · simp
  · simp
  · simp
  · simp [hz0]
  · ext x
    simp [greenPotential]

#print axioms neg_univ_dirac_zero_mem_subharmonicBallTestClass

/-- A whole-plane negative Dirac test has a bounded representative for every
observation measure when the cluster lies strictly inside the unit disc and the pole
is in the cluster away from the source atom. -/
theorem univ_dirac_zero_has_bounded_representative
    {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ}
    (hΛ : closure Λ ⊆ ball (0 : ℂ) 1) (hz : z ∈ Λ) (hz0 : z ≠ 0) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (-greenPotential univ (Measure.dirac 0)) z = g z ∧
      (-greenPotential univ (Measure.dirac 0)) =ᵐ[μ.restrict Λ] g := by
  classical
  let g := -greenPotential (ball 0 1) (Measure.dirac 0)
  have hg : g ∈ boundedSubharmonicBallTestClass Λ z := by
    refine ⟨ball 0 1, {0}, 0, Measure.dirac 0, 0, isOpen_ball, isBounded_ball,
      hΛ, isCompact_singleton, ?_, inferInstance, inferInstance, ?_, ?_, ?_,
      harmonicOnNhd_const 0, ?_, integrable_dirac enorm_lt_top, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · simp [hz0]
    · ext x
      simp [g, greenPotential]
  refine ⟨g, hg, ?_, ?_⟩
  · simp only [g, Pi.neg_apply]
    rw [greenPotential_univ_dirac_zero_eq_unitDisc (hΛ (subset_closure hz))]
  · apply ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hΛ)
    filter_upwards [ae_restrict_mem (isOpen_ball.measurableSet)] with x hx
    simp only [g, Pi.neg_apply]
    rw [greenPotential_univ_dirac_zero_eq_unitDisc hx]

#print axioms univ_dirac_zero_has_bounded_representative

/-- An annular non-atomic source can be removed even when a second negative
source is an observed atom at the centre of the unit disc. -/
theorem univ_circleDensity_add_dirac_has_bounded_representative
    {r δ η : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hwidth : δ ≤ r * η)
    {μ : Measure ℂ} {Λ : Set ℂ} {p z : ℂ}
    (hΛ : closure Λ ⊆ ball (0 : ℂ) 1) (hp : p ∈ Λ) (hp0 : p ≠ 0)
    (hshell : ∀ x ∈ ball (0 : ℂ) 1, ‖z - x‖ ≤ r - η) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ p,
      (-greenPotential univ ((volume.withDensity (fun x => ENNReal.ofReal
        ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x))) +
        Measure.dirac 0)) p = g p ∧
      (-greenPotential univ ((volume.withDensity (fun x => ENNReal.ofReal
        ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x))) +
        Measure.dirac 0)) =ᵐ[μ.restrict Λ] g := by
  let ν := volume.withDensity (fun x => ENNReal.ofReal
    ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x))
  let q : ℂ → ℝ := fun _ => -greenPotential univ ν z
  let g := q - greenPotential (ball 0 1) (Measure.dirac 0)
  have hg : g ∈ boundedSubharmonicBallTestClass Λ p := by
    refine ⟨ball 0 1, {0}, 0, Measure.dirac 0, q, isOpen_ball, isBounded_ball,
      hΛ, isCompact_singleton, ?_, inferInstance, inferInstance, ?_, ?_, ?_,
      harmonicOnNhd_const _, ?_, integrable_dirac enorm_lt_top, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · simp [hp0]
    · ext x
      simp [g, greenPotential]
  have heq : ∀ x ∈ ball (0 : ℂ) 1,
      (-greenPotential univ (ν + Measure.dirac 0)) x = g x := by
    intro x hx
    have hsum : greenPotential univ (ν + Measure.dirac 0) x =
        greenPotential univ ν x + greenPotential univ (Measure.dirac 0) x := by
      exact integral_add_measure (integrable_greenFunction_univ_circleDensity hr hδ z x)
        (integrable_dirac enorm_lt_top)
    simp only [Pi.neg_apply, g, q, Pi.sub_apply]
    rw [hsum, greenPotential_univ_circleDensity_eq_center_of_mem_inner_ball hr hδ hwidth
      (hshell x hx), greenPotential_univ_dirac_zero_eq_unitDisc hx]
    ring
  refine ⟨g, hg, heq p (hΛ (subset_closure hp)), ?_⟩
  apply ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hΛ)
  filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with x hx
  exact heq x hx

#print axioms univ_circleDensity_add_dirac_has_bounded_representative

/-- The mixed annular and atomic negative source is an admissible frozen test
when the pole differs from the atom. -/
theorem neg_univ_circleDensity_add_dirac_mem_subharmonicBallTestClass
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z : ℂ) (Λ : Set ℂ) {p : ℂ}
    (hp0 : p ≠ 0) :
    -greenPotential univ ((volume.withDensity (fun x => ENNReal.ofReal
      ((∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x))) +
      Measure.dirac 0) ∈ subharmonicBallTestClass Λ p := by
  let density : ℂ → ℝ := fun x =>
    (∫ y, circleDensity r δ hδ 0 y)⁻¹ * circleDensity r δ hδ z x
  let ν := volume.withDensity (fun x => ENNReal.ofReal (density x))
  let K := tsupport (circleDensity r δ hδ z)
  have hd : Continuous density := continuous_const.mul (circleDensity_contDiff r δ hδ z).continuous
  have hdi : Integrable density volume :=
    ((circleDensity_contDiff r δ hδ z).continuous.integrable_of_hasCompactSupport
      (circleDensity_hasCompactSupport hr.le hδ z)).const_mul _
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hdi.hasFiniteIntegral
  have hK : IsCompact K := circleDensity_hasCompactSupport hr.le hδ z
  have hνK : ν Kᶜ = 0 := by
    rw [withDensity_apply _ hK.isClosed.measurableSet.compl]
    apply (lintegral_eq_zero_iff hd.measurable.ennreal_ofReal).2
    filter_upwards [ae_restrict_mem hK.isClosed.measurableSet.compl] with x hx
    have hx0 : circleDensity r δ hδ z x = 0 := by
      by_contra hx'
      exact hx (subset_closure hx')
    simp [density, hx0]
  have hνK' : ν (insert 0 K)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr (subset_insert 0 K)) hνK
  have hνp : ν {p} = 0 :=
    (withDensity_absolutelyContinuous volume _) (measure_singleton p)
  refine ⟨univ, insert 0 K, 0, ν + Measure.dirac 0, 0, isOpen_univ,
    subset_univ _, hK.insert 0, subset_univ _, inferInstance, inferInstance,
    by simp, ?_, by simp, harmonicOnNhd_const 0, ?_, ?_, ?_⟩
  · simp [hνK']
  · simp [hνp, hp0]
  · exact (integrable_greenFunction_univ_circleDensity hr hδ z p).add_measure
      (integrable_dirac enorm_lt_top)
  · change -greenPotential univ (ν + Measure.dirac 0) =
      (0 : ℂ → ℝ) + greenPotential univ 0 - greenPotential univ (ν + Measure.dirac 0)
    ext x
    simp [greenPotential]

#print axioms neg_univ_circleDensity_add_dirac_mem_subharmonicBallTestClass

/-- The difference of two whole-plane point potentials is an admissible test
when the positive atom is outside the observation set and the negative atom is
not at the pole. -/
theorem univ_dirac_sub_dirac_mem_subharmonicBallTestClass
    {Λ : Set ℂ} {z a b : ℂ} (hza : z ≠ a) (hb : b ∉ Λ) :
    greenPotential univ (Measure.dirac b) - greenPotential univ (Measure.dirac a) ∈
      subharmonicBallTestClass Λ z := by
  classical
  refine ⟨univ, {b, a}, Measure.dirac b, Measure.dirac a, 0, isOpen_univ,
    subset_univ _, isCompact_singleton.insert b, subset_univ _,
    inferInstance, inferInstance, ?_, ?_, ?_, harmonicOnNhd_const 0, ?_,
    integrable_dirac enorm_lt_top, ?_⟩
  · simp
  · simp
  · simp [Measure.dirac_apply, hb]
  · simp [hza]
  · ext x
    simp

#print axioms univ_dirac_sub_dirac_mem_subharmonicBallTestClass

/-- A whole-plane two-source test has a bounded representative with its positive
source removed, provided the disc correction vanishes at the negative atom. -/
theorem univ_two_dirac_has_bounded_representative_of_zero_diagonal_correction
    {μ : Measure ℂ} {Λ : Set ℂ} {z a b : ℂ} {R : ℝ}
    (hR : 0 < R) (hΛ : closure Λ ⊆ ball (0 : ℂ) R) (hz : z ∈ Λ)
    (hza : z ≠ a) (ha : a ∈ ball (0 : ℂ) R) (hb : b ∉ ball (0 : ℂ) R)
    (hdiag : ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * a‖ = R) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (greenPotential univ (Measure.dirac b) - greenPotential univ (Measure.dirac a)) z = g z ∧
      (greenPotential univ (Measure.dirac b) - greenPotential univ (Measure.dirac a))
        =ᵐ[μ.restrict Λ] g := by
  classical
  let q := greenPotential univ (Measure.dirac b) - greatestHarmonicMinorantBall R a
  have hqeq : greenPotential univ (Measure.dirac b) = newtonKernel b := by
    ext x
    simp only [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel,
      newtonKernel_comm x b]
  have hq : HarmonicOnNhd q (ball 0 R) := by
    apply HarmonicOnNhd.sub
    · rw [hqeq]
      intro x hx
      apply harmonicAt_newtonKernel
      intro hxb
      exact hb (hxb ▸ hx)
    · exact (isHarmonicMinorant_greatestHarmonicMinorantBall ha).1
  let g := q - greenPotential (ball 0 R) (Measure.dirac a)
  have hg : g ∈ boundedSubharmonicBallTestClass Λ z := by
    refine ⟨ball 0 R, {a}, 0, Measure.dirac a, q, isOpen_ball, isBounded_ball,
      hΛ, isCompact_singleton, ?_, inferInstance, inferInstance, ?_, ?_, ?_, hq,
      ?_, integrable_dirac enorm_lt_top, ?_⟩
    · simpa using ha
    · simp
    · simp
    · simp
    · simp [hza]
    · ext x
      simp [g, greenPotential]
  refine ⟨g, hg, ?_, ?_⟩
  · simp only [g, q, Pi.sub_apply]
    rw [greenPotential_univ_dirac_eq_ball_add_harmonic hR ha hdiag (hΛ (subset_closure hz))]
    ring
  · apply ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hΛ)
    filter_upwards [ae_restrict_mem (isOpen_ball.measurableSet)] with x hx
    simp only [g, q, Pi.sub_apply]
    rw [greenPotential_univ_dirac_eq_ball_add_harmonic hR ha hdiag hx]
    ring

#print axioms univ_two_dirac_has_bounded_representative_of_zero_diagonal_correction

/-- A whole-plane two-source test has a bounded representative with its positive
source removed, when the observation measure does not charge the negative atom. -/
theorem univ_two_dirac_has_bounded_representative_of_measure_atom_eq_zero
    {μ : Measure ℂ} {Λ : Set ℂ} {z a b : ℂ} {R : ℝ}
    (hR : 0 < R) (hΛ : closure Λ ⊆ ball (0 : ℂ) R) (hz : z ∈ Λ)
    (hza : z ≠ a) (ha : a ∈ ball (0 : ℂ) R) (hb : b ∉ ball (0 : ℂ) R)
    (hμ : μ.restrict Λ {a} = 0) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (greenPotential univ (Measure.dirac b) - greenPotential univ (Measure.dirac a)) z = g z ∧
      (greenPotential univ (Measure.dirac b) - greenPotential univ (Measure.dirac a))
        =ᵐ[μ.restrict Λ] g := by
  classical
  let q := greenPotential univ (Measure.dirac b) - greatestHarmonicMinorantBall R a
  have hqeq : greenPotential univ (Measure.dirac b) = newtonKernel b := by
    ext x
    simp only [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel,
      newtonKernel_comm x b]
  have hq : HarmonicOnNhd q (ball 0 R) := by
    apply HarmonicOnNhd.sub
    · rw [hqeq]
      intro x hx
      apply harmonicAt_newtonKernel
      intro hxb
      exact hb (hxb ▸ hx)
    · exact (isHarmonicMinorant_greatestHarmonicMinorantBall ha).1
  let g := q - greenPotential (ball 0 R) (Measure.dirac a)
  have hg : g ∈ boundedSubharmonicBallTestClass Λ z := by
    refine ⟨ball 0 R, {a}, 0, Measure.dirac a, q, isOpen_ball, isBounded_ball,
      hΛ, isCompact_singleton, ?_, inferInstance, inferInstance, ?_, ?_, ?_, hq,
      ?_, integrable_dirac enorm_lt_top, ?_⟩
    · simpa using ha
    · simp
    · simp
    · simp
    · simp [hza]
    · ext x
      simp [g, greenPotential]
  refine ⟨g, hg, ?_, ?_⟩
  · simp only [g, q, Pi.sub_apply]
    rw [greenPotential_univ_dirac_eq_ball_add_harmonic_of_ne hR ha (hΛ (subset_closure hz)) hza]
    ring
  · have hne : ∀ᵐ x ∂μ.restrict Λ, x ≠ a := by
      rw [ae_iff]
      simpa only [not_not, ofPred_eq_eq_singleton] using hμ
    have hball : ∀ᵐ x ∂μ.restrict Λ, x ∈ ball (0 : ℂ) R :=
      ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hΛ)
        (ae_restrict_mem (isOpen_ball.measurableSet))
    filter_upwards [hball, hne] with x hx hxa
    simp only [g, q, Pi.sub_apply]
    rw [greenPotential_univ_dirac_eq_ball_add_harmonic_of_ne hR ha hx hxa]
    ring

#print axioms univ_two_dirac_has_bounded_representative_of_measure_atom_eq_zero

/-- The Green potential of two point masses is the sum of their potentials.
Each point-mass integral is integrable, including on the diagonal. -/
theorem greenPotential_add_dirac (O : Set ℂ) (a c x : ℂ) :
    greenPotential O (Measure.dirac a + Measure.dirac c) x =
      greenPotential O (Measure.dirac a) x + greenPotential O (Measure.dirac c) x := by
  exact integral_add_measure (integrable_dirac enorm_lt_top) (integrable_dirac enorm_lt_top)

#print axioms greenPotential_add_dirac

/-- The Green potential of finitely many point masses is the sum of the point
potentials, including at the diagonal under the frozen convention. -/
theorem greenPotential_finset_sum_dirac (O : Set ℂ) (S : Finset ℂ) (x : ℂ) :
    greenPotential O (∑ a ∈ S, Measure.dirac a) x =
      ∑ a ∈ S, greenPotential O (Measure.dirac a) x := by
  classical
  unfold greenPotential
  rw [integral_finsetSum_measure (fun _ _ => integrable_dirac enorm_lt_top)]

#print axioms greenPotential_finset_sum_dirac

/-- Away from finitely many point sources, the difference between the whole-plane
and disc potentials is the sum of the disc harmonic corrections. -/
theorem greenPotential_univ_finset_sum_dirac_eq_ball_add_harmonic_of_not_mem
    {S : Finset ℂ} {R : ℝ} {x : ℂ} (hR : 0 < R)
    (hS : ∀ a ∈ S, a ∈ ball (0 : ℂ) R) (hx : x ∈ ball (0 : ℂ) R)
    (hxs : x ∉ S) :
    greenPotential univ (∑ a ∈ S, Measure.dirac a) x =
      greenPotential (ball 0 R) (∑ a ∈ S, Measure.dirac a) x +
        ∑ a ∈ S, greatestHarmonicMinorantBall R a x := by
  classical
  rw [greenPotential_finset_sum_dirac, greenPotential_finset_sum_dirac, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  simpa only [add_comm] using
    greenPotential_univ_dirac_eq_ball_add_harmonic_of_ne hR (hS a ha) hx
      (fun h => hxs (h ▸ ha))

#print axioms greenPotential_univ_finset_sum_dirac_eq_ball_add_harmonic_of_not_mem

/-- The finite-source correction also holds at a source whose diagonal
harmonic correction vanishes. -/
theorem greenPotential_univ_finset_sum_dirac_eq_ball_add_harmonic_of_diagonal
    {S : Finset ℂ} {R : ℝ} {x : ℂ} (hR : 0 < R)
    (hS : ∀ a ∈ S, a ∈ ball (0 : ℂ) R) (hx : x ∈ ball (0 : ℂ) R)
    (hdiag : ∀ a ∈ S, x = a → ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * a‖ = R) :
    greenPotential univ (∑ a ∈ S, Measure.dirac a) x =
      greenPotential (ball 0 R) (∑ a ∈ S, Measure.dirac a) x +
        ∑ a ∈ S, greatestHarmonicMinorantBall R a x := by
  classical
  rw [greenPotential_finset_sum_dirac, greenPotential_finset_sum_dirac, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  by_cases hxa : x = a
  · simpa only [add_comm] using
      greenPotential_univ_dirac_eq_ball_add_harmonic hR (hS a ha) (hdiag a ha hxa) hx
  · simpa only [add_comm] using
      greenPotential_univ_dirac_eq_ball_add_harmonic_of_ne hR (hS a ha) hx hxa

#print axioms greenPotential_univ_finset_sum_dirac_eq_ball_add_harmonic_of_diagonal

/-- A finite sum of disc harmonic minorants is harmonic when all sources lie
inside the disc. -/
theorem harmonicOnNhd_finset_sum_greatestHarmonicMinorantBall {R : ℝ} (S : Finset ℂ)
    (hS : ∀ a ∈ S, a ∈ ball (0 : ℂ) R) :
    HarmonicOnNhd (∑ a ∈ S, greatestHarmonicMinorantBall R a) (ball 0 R) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change HarmonicOnNhd (fun _ : ℂ => (0 : ℝ)) (ball 0 R)
    exact harmonicOnNhd_const 0
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha]
    exact ((isHarmonicMinorant_greatestHarmonicMinorantBall
      (hS a (Finset.mem_insert_self a S))).1).add
      (ih (fun c hc => hS c (Finset.mem_insert_of_mem hc)))

#print axioms harmonicOnNhd_finset_sum_greatestHarmonicMinorantBall

/-- A whole-plane negative potential of finitely many point sources belongs
to the full test class when the pole avoids those sources. -/
theorem neg_univ_finset_sum_dirac_mem_subharmonicBallTestClass
    {Λ : Set ℂ} {z : ℂ} (S : Finset ℂ) (hzS : z ∉ S) :
    -greenPotential univ (∑ a ∈ S, Measure.dirac a) ∈ subharmonicBallTestClass Λ z := by
  classical
  refine ⟨univ, (↑S : Set ℂ), 0, ∑ a ∈ S, Measure.dirac a, 0, isOpen_univ,
    subset_univ _, S.finite_toSet.isCompact, subset_univ _, inferInstance,
    inferInstance, ?_, ?_, ?_, harmonicOnNhd_const 0, ?_,
    integrable_finsetSum_measure.mpr (fun _ _ => integrable_dirac enorm_lt_top), ?_⟩
  · simp
  · simp
  · simp
  · simp [hzS]
  · ext x
    simp [greenPotential]

#print axioms neg_univ_finset_sum_dirac_mem_subharmonicBallTestClass

/-- A whole-plane potential with finitely many negative point sources admits a
bounded disc representative when the observation measure charges none of the sources. -/
theorem neg_univ_finset_sum_dirac_has_bounded_representative
    {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ} {R : ℝ} (S : Finset ℂ)
    (hR : 0 < R) (hΛ : closure Λ ⊆ ball (0 : ℂ) R) (hz : z ∈ Λ)
    (hzS : z ∉ S) (hS : ∀ a ∈ S, a ∈ ball (0 : ℂ) R)
    (hμ : μ.restrict Λ (↑S : Set ℂ) = 0) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (-greenPotential univ (∑ a ∈ S, Measure.dirac a)) z = g z ∧
      (-greenPotential univ (∑ a ∈ S, Measure.dirac a)) =ᵐ[μ.restrict Λ] g := by
  classical
  let ν : Measure ℂ := ∑ a ∈ S, Measure.dirac a
  let q : ℂ → ℝ := - ∑ a ∈ S, greatestHarmonicMinorantBall R a
  let g := q - greenPotential (ball 0 R) ν
  have hq : HarmonicOnNhd q (ball 0 R) := (harmonicOnNhd_finset_sum_greatestHarmonicMinorantBall S hS).neg
  have hg : g ∈ boundedSubharmonicBallTestClass Λ z := by
    refine ⟨ball 0 R, (↑S : Set ℂ), 0, ν, q, isOpen_ball, isBounded_ball,
      hΛ, S.finite_toSet.isCompact, ?_, inferInstance, inferInstance, ?_, ?_, ?_, hq,
      ?_, ?_, ?_⟩
    · exact hS
    · simp
    · simp [ν]
    · simp
    · simp [ν, hzS]
    · exact integrable_finsetSum_measure.mpr (fun _ _ => integrable_dirac enorm_lt_top)
    · ext x
      simp [g, greenPotential]
  have heq : ∀ x ∈ ball (0 : ℂ) R, x ∉ S →
      (-greenPotential univ ν) x = g x := by
    intro x hx hxS
    simp only [g, q, Pi.neg_apply, Pi.sub_apply, Finset.sum_apply]
    rw [show greenPotential univ ν x = greenPotential (ball 0 R) ν x +
      ∑ a ∈ S, greatestHarmonicMinorantBall R a x from
        greenPotential_univ_finset_sum_dirac_eq_ball_add_harmonic_of_not_mem hR hS hx hxS]
    ring
  refine ⟨g, hg, heq z (hΛ (subset_closure hz)) hzS, ?_⟩
  have hne : ∀ᵐ x ∂μ.restrict Λ, x ∉ S := by
    rw [ae_iff]
    simp only [not_not]
    have hSet : {x : ℂ | x ∈ S} = (↑S : Set ℂ) := by
      ext x
      simp
    rw [hSet]
    exact hμ
  have hball : ∀ᵐ x ∂μ.restrict Λ, x ∈ ball (0 : ℂ) R :=
    ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hΛ)
      (ae_restrict_mem (isOpen_ball.measurableSet))
  filter_upwards [hball, hne] with x hx hxS
  exact heq x hx hxS

#print axioms neg_univ_finset_sum_dirac_has_bounded_representative

/-- A whole-plane test with finitely many negative point sources and one
positive point source satisfies the full frozen class conditions. -/
theorem univ_dirac_sub_finset_sum_dirac_mem_subharmonicBallTestClass
    {Λ : Set ℂ} {z b : ℂ} (S : Finset ℂ) (hzS : z ∉ S) (hb : b ∉ Λ) :
    greenPotential univ (Measure.dirac b) -
        greenPotential univ (∑ a ∈ S, Measure.dirac a) ∈
      subharmonicBallTestClass Λ z := by
  classical
  refine ⟨univ, insert b (↑S : Set ℂ), Measure.dirac b, ∑ a ∈ S, Measure.dirac a,
    0, isOpen_univ, subset_univ _, S.finite_toSet.isCompact.insert b,
    subset_univ _, inferInstance, inferInstance, ?_, ?_, ?_, harmonicOnNhd_const 0,
    ?_, integrable_finsetSum_measure.mpr (fun _ _ => integrable_dirac enorm_lt_top), ?_⟩
  · simp
  · simp; aesop
  · simp [Measure.dirac_apply, hb]
  · simp [hzS]
  · ext x
    simp

#print axioms univ_dirac_sub_finset_sum_dirac_mem_subharmonicBallTestClass

/-- A positive point source outside the disc can be removed from a whole-plane
test with finitely many negative point sources not charged by the observation measure. -/
theorem univ_dirac_sub_finset_sum_dirac_has_bounded_representative
    {μ : Measure ℂ} {Λ : Set ℂ} {z b : ℂ} {R : ℝ} (S : Finset ℂ)
    (hR : 0 < R) (hΛ : closure Λ ⊆ ball (0 : ℂ) R) (hz : z ∈ Λ)
    (hzS : z ∉ S) (hS : ∀ a ∈ S, a ∈ ball (0 : ℂ) R)
    (hb : b ∉ ball (0 : ℂ) R) (hμ : μ.restrict Λ (↑S : Set ℂ) = 0) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (greenPotential univ (Measure.dirac b) -
        greenPotential univ (∑ a ∈ S, Measure.dirac a)) z = g z ∧
      (greenPotential univ (Measure.dirac b) -
        greenPotential univ (∑ a ∈ S, Measure.dirac a)) =ᵐ[μ.restrict Λ] g := by
  classical
  let ν : Measure ℂ := ∑ a ∈ S, Measure.dirac a
  let q : ℂ → ℝ := greenPotential univ (Measure.dirac b) -
    ∑ a ∈ S, greatestHarmonicMinorantBall R a
  let g := q - greenPotential (ball 0 R) ν
  have hb_harm : HarmonicOnNhd (greenPotential univ (Measure.dirac b)) (ball 0 R) := by
    have hqeq : greenPotential univ (Measure.dirac b) = newtonKernel b := by
      ext x
      simp only [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel,
        newtonKernel_comm x b]
    rw [hqeq]
    intro x hx
    apply harmonicAt_newtonKernel
    intro hxb
    exact hb (hxb ▸ hx)
  have hq : HarmonicOnNhd q (ball 0 R) := hb_harm.sub (harmonicOnNhd_finset_sum_greatestHarmonicMinorantBall S hS)
  have hg : g ∈ boundedSubharmonicBallTestClass Λ z := by
    refine ⟨ball 0 R, (↑S : Set ℂ), 0, ν, q, isOpen_ball, isBounded_ball,
      hΛ, S.finite_toSet.isCompact, ?_, inferInstance, inferInstance, ?_, ?_, ?_, hq,
      ?_, ?_, ?_⟩
    · exact hS
    · simp
    · simp [ν]
    · simp
    · simp [ν, hzS]
    · exact integrable_finsetSum_measure.mpr (fun _ _ => integrable_dirac enorm_lt_top)
    · ext x
      simp [g, greenPotential]
  have heq : ∀ x ∈ ball (0 : ℂ) R, x ∉ S →
      (greenPotential univ (Measure.dirac b) - greenPotential univ ν) x = g x := by
    intro x hx hxS
    simp only [g, q, Pi.sub_apply, Finset.sum_apply]
    rw [show greenPotential univ ν x = greenPotential (ball 0 R) ν x +
      ∑ a ∈ S, greatestHarmonicMinorantBall R a x from
        greenPotential_univ_finset_sum_dirac_eq_ball_add_harmonic_of_not_mem hR hS hx hxS]
    ring
  refine ⟨g, hg, heq z (hΛ (subset_closure hz)) hzS, ?_⟩
  have hne : ∀ᵐ x ∂μ.restrict Λ, x ∉ S := by
    rw [ae_iff]
    simp only [not_not]
    have hSet : {x : ℂ | x ∈ S} = (↑S : Set ℂ) := by
      ext x
      simp
    rw [hSet]
    exact hμ
  have hball : ∀ᵐ x ∂μ.restrict Λ, x ∈ ball (0 : ℂ) R :=
    ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hΛ)
      (ae_restrict_mem (isOpen_ball.measurableSet))
  filter_upwards [hball, hne] with x hx hxS
  exact heq x hx hxS

#print axioms univ_dirac_sub_finset_sum_dirac_has_bounded_representative

/-- A positive point source outside the disc can be removed; observation measures
may charge negative source atoms where the diagonal correction vanishes. -/
theorem univ_dirac_sub_finset_sum_dirac_has_bounded_representative_of_diagonal
    {μ : Measure ℂ} {Λ : Set ℂ} {z b : ℂ} {R : ℝ} (S : Finset ℂ)
    (hR : 0 < R) (hΛ : closure Λ ⊆ ball (0 : ℂ) R) (hz : z ∈ Λ)
    (hzS : z ∉ S) (hS : ∀ a ∈ S, a ∈ ball (0 : ℂ) R)
    (hb : b ∉ ball (0 : ℂ) R)
    (hμ : μ.restrict Λ {a | a ∈ S ∧ ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * a‖ ≠ R} = 0) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (greenPotential univ (Measure.dirac b) -
        greenPotential univ (∑ a ∈ S, Measure.dirac a)) z = g z ∧
      (greenPotential univ (Measure.dirac b) -
        greenPotential univ (∑ a ∈ S, Measure.dirac a)) =ᵐ[μ.restrict Λ] g := by
  classical
  let ν : Measure ℂ := ∑ a ∈ S, Measure.dirac a
  let q : ℂ → ℝ := greenPotential univ (Measure.dirac b) -
    ∑ a ∈ S, greatestHarmonicMinorantBall R a
  let g := q - greenPotential (ball 0 R) ν
  have hb_harm : HarmonicOnNhd (greenPotential univ (Measure.dirac b)) (ball 0 R) := by
    have hqeq : greenPotential univ (Measure.dirac b) = newtonKernel b := by
      ext x
      simp only [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel,
        newtonKernel_comm x b]
    rw [hqeq]
    intro x hx
    apply harmonicAt_newtonKernel
    intro hxb
    exact hb (hxb ▸ hx)
  have hq : HarmonicOnNhd q (ball 0 R) := hb_harm.sub (harmonicOnNhd_finset_sum_greatestHarmonicMinorantBall S hS)
  have hg : g ∈ boundedSubharmonicBallTestClass Λ z := by
    refine ⟨ball 0 R, (↑S : Set ℂ), 0, ν, q, isOpen_ball, isBounded_ball,
      hΛ, S.finite_toSet.isCompact, ?_, inferInstance, inferInstance, ?_, ?_, ?_, hq,
      ?_, ?_, ?_⟩
    · exact hS
    · simp
    · simp [ν]
    · simp
    · simp [ν, hzS]
    · exact integrable_finsetSum_measure.mpr (fun _ _ => integrable_dirac enorm_lt_top)
    · ext x
      simp [g, greenPotential]
  have heq : ∀ x ∈ ball (0 : ℂ) R,
      (∀ a ∈ S, x = a → ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * a‖ = R) →
      (greenPotential univ (Measure.dirac b) - greenPotential univ ν) x = g x := by
    intro x hx hxdiag
    simp only [g, q, Pi.sub_apply, Finset.sum_apply]
    rw [show greenPotential univ ν x = greenPotential (ball 0 R) ν x +
      ∑ a ∈ S, greatestHarmonicMinorantBall R a x from
        greenPotential_univ_finset_sum_dirac_eq_ball_add_harmonic_of_diagonal hR hS hx hxdiag]
    ring
  refine ⟨g, hg, heq z (hΛ (subset_closure hz)) ?_, ?_⟩
  · intro a ha hza
    exact (hzS (hza ▸ ha)).elim
  · have hgood : ∀ᵐ x ∂μ.restrict Λ,
        x ∉ {a | a ∈ S ∧ ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * a‖ ≠ R} := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using hμ
    have hball : ∀ᵐ x ∂μ.restrict Λ, x ∈ ball (0 : ℂ) R :=
      ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hΛ)
        (ae_restrict_mem (isOpen_ball.measurableSet))
    filter_upwards [hball, hgood] with x hx hxgood
    apply heq x hx
    intro a ha hxa
    by_contra hdiag
    exact hxgood (by simpa [hxa] using ⟨ha, hdiag⟩)

#print axioms univ_dirac_sub_finset_sum_dirac_has_bounded_representative_of_diagonal

/-- Whole-plane potentials of finite positive and negative point sources are
admissible when positive sources avoid the cluster and negative sources avoid the pole. -/
theorem univ_finset_sum_dirac_sub_finset_sum_dirac_mem_subharmonicBallTestClass
    {Λ : Set ℂ} {z : ℂ} (S T : Finset ℂ) (hzS : z ∉ S)
    (hT : ∀ b ∈ T, b ∉ Λ) :
    greenPotential univ (∑ b ∈ T, Measure.dirac b) -
        greenPotential univ (∑ a ∈ S, Measure.dirac a) ∈
      subharmonicBallTestClass Λ z := by
  classical
  refine ⟨univ, (↑(S ∪ T) : Set ℂ), ∑ b ∈ T, Measure.dirac b,
    ∑ a ∈ S, Measure.dirac a, 0, isOpen_univ, subset_univ _,
    (S ∪ T).finite_toSet.isCompact, subset_univ _, inferInstance, inferInstance,
    ?_, ?_, ?_, harmonicOnNhd_const 0, ?_,
    integrable_finsetSum_measure.mpr (fun _ _ => integrable_dirac enorm_lt_top), ?_⟩
  · simp; aesop
  · simp; aesop
  · simp [Measure.dirac_apply]
    exact hT
  · simp [hzS]
  · ext x
    simp

#print axioms univ_finset_sum_dirac_sub_finset_sum_dirac_mem_subharmonicBallTestClass

/-- A finite positive source outside the disc can be absorbed into the harmonic part. -/
theorem univ_finset_sum_dirac_sub_finset_sum_dirac_has_bounded_representative
    {μ : Measure ℂ} {Λ : Set ℂ} {z : ℂ} {R : ℝ} (S T : Finset ℂ)
    (hR : 0 < R) (hΛ : closure Λ ⊆ ball (0 : ℂ) R) (hz : z ∈ Λ)
    (hzS : z ∉ S) (hS : ∀ a ∈ S, a ∈ ball (0 : ℂ) R)
    (hT : ∀ b ∈ T, b ∉ ball (0 : ℂ) R)
    (hμ : μ.restrict Λ {a | a ∈ S ∧ ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * a‖ ≠ R} = 0) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (greenPotential univ (∑ b ∈ T, Measure.dirac b) -
        greenPotential univ (∑ a ∈ S, Measure.dirac a)) z = g z ∧
      (greenPotential univ (∑ b ∈ T, Measure.dirac b) -
        greenPotential univ (∑ a ∈ S, Measure.dirac a)) =ᵐ[μ.restrict Λ] g := by
  classical
  let ν : Measure ℂ := ∑ a ∈ S, Measure.dirac a
  let q : ℂ → ℝ := greenPotential univ (∑ b ∈ T, Measure.dirac b) -
    ∑ a ∈ S, greatestHarmonicMinorantBall R a
  let g := q - greenPotential (ball 0 R) ν
  have hb_harm : HarmonicOnNhd (greenPotential univ (∑ b ∈ T, Measure.dirac b)) (ball 0 R) := by
    have heq : greenPotential univ (∑ b ∈ T, Measure.dirac b) =
        ∑ b ∈ T, greenPotential univ (Measure.dirac b) := by
      ext x
      simp [greenPotential_finset_sum_dirac]
    rw [heq]
    have hsum : ∀ U : Finset ℂ, (∀ b ∈ U, b ∉ ball (0 : ℂ) R) →
        HarmonicOnNhd (∑ b ∈ U, greenPotential univ (Measure.dirac b)) (ball 0 R) := by
      intro U
      induction U using Finset.induction_on with
      | empty =>
        intro _
        simp only [Finset.sum_empty]
        change HarmonicOnNhd (fun _ : ℂ => (0 : ℝ)) (ball 0 R)
        exact harmonicOnNhd_const 0
      | @insert b U hb ih =>
        intro hU
        rw [Finset.sum_insert hb]
        apply HarmonicOnNhd.add ?_ (ih (fun c hc => hU c (Finset.mem_insert_of_mem hc)))
        have hqeq : greenPotential univ (Measure.dirac b) = newtonKernel b := by
          ext x
          simp only [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel,
            newtonKernel_comm x b]
        rw [hqeq]
        intro x hx
        apply harmonicAt_newtonKernel
        intro hxb
        exact hU b (Finset.mem_insert_self b U) (hxb ▸ hx)
    exact hsum T hT
  have hq : HarmonicOnNhd q (ball 0 R) := hb_harm.sub (harmonicOnNhd_finset_sum_greatestHarmonicMinorantBall S hS)
  have hg : g ∈ boundedSubharmonicBallTestClass Λ z := by
    refine ⟨ball 0 R, (↑S : Set ℂ), 0, ν, q, isOpen_ball, isBounded_ball,
      hΛ, S.finite_toSet.isCompact, ?_, inferInstance, inferInstance, ?_, ?_, ?_, hq,
      ?_, ?_, ?_⟩
    · exact hS
    · simp
    · simp [ν]
    · simp
    · simp [ν, hzS]
    · exact integrable_finsetSum_measure.mpr (fun _ _ => integrable_dirac enorm_lt_top)
    · ext x
      simp [g, greenPotential]
  have heq : ∀ x ∈ ball (0 : ℂ) R,
      (∀ a ∈ S, x = a → ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * a‖ = R) →
      (greenPotential univ (∑ b ∈ T, Measure.dirac b) - greenPotential univ ν) x = g x := by
    intro x hx hxdiag
    simp only [g, q, Pi.sub_apply, Finset.sum_apply]
    rw [show greenPotential univ ν x = greenPotential (ball 0 R) ν x +
      ∑ a ∈ S, greatestHarmonicMinorantBall R a x from
        greenPotential_univ_finset_sum_dirac_eq_ball_add_harmonic_of_diagonal hR hS hx hxdiag]
    ring
  refine ⟨g, hg, heq z (hΛ (subset_closure hz)) ?_, ?_⟩
  · intro a ha hza
    exact (hzS (hza ▸ ha)).elim
  · have hgood : ∀ᵐ x ∂μ.restrict Λ,
        x ∉ {a | a ∈ S ∧ ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * a‖ ≠ R} := by
      rw [ae_iff]
      simpa only [not_not, ofPred_mem_eq] using hμ
    have hball : ∀ᵐ x ∂μ.restrict Λ, x ∈ ball (0 : ℂ) R :=
      ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hΛ)
        (ae_restrict_mem (isOpen_ball.measurableSet))
    filter_upwards [hball, hgood] with x hx hxgood
    apply heq x hx
    intro a ha hxa
    by_contra hdiag
    exact hxgood (by simpa [hxa] using ⟨ha, hdiag⟩)

#print axioms univ_finset_sum_dirac_sub_finset_sum_dirac_has_bounded_representative

/-- If each source has zero diagonal correction, the finite-source construction
works for every observation measure, including measures charging the sources. -/
theorem univ_dirac_sub_finset_sum_dirac_has_bounded_representative_of_zero_diagonal
    {μ : Measure ℂ} {Λ : Set ℂ} {z b : ℂ} {R : ℝ} (S : Finset ℂ)
    (hR : 0 < R) (hΛ : closure Λ ⊆ ball (0 : ℂ) R) (hz : z ∈ Λ)
    (hzS : z ∉ S) (hS : ∀ a ∈ S, a ∈ ball (0 : ℂ) R)
    (hb : b ∉ ball (0 : ℂ) R)
    (hdiag : ∀ a ∈ S, ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * a‖ = R) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (greenPotential univ (Measure.dirac b) -
        greenPotential univ (∑ a ∈ S, Measure.dirac a)) z = g z ∧
      (greenPotential univ (Measure.dirac b) -
        greenPotential univ (∑ a ∈ S, Measure.dirac a)) =ᵐ[μ.restrict Λ] g := by
  have hs : {a | a ∈ S ∧ ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * a‖ ≠ R} = ∅ := by
    ext a
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro ha
    exact not_not.mpr (hdiag a ha)
  apply univ_dirac_sub_finset_sum_dirac_has_bounded_representative_of_diagonal
    S hR hΛ hz hzS hS hb
  simp [hs]

#print axioms univ_dirac_sub_finset_sum_dirac_has_bounded_representative_of_zero_diagonal

/-- The finite-source construction also works with any common nonnegative mass. -/
theorem univ_smul_dirac_sub_finset_sum_dirac_has_bounded_representative
    {μ : Measure ℂ} {Λ : Set ℂ} {z b : ℂ} {R : ℝ} (S : Finset ℂ) (c : ℝ≥0)
    (hR : 0 < R) (hΛ : closure Λ ⊆ ball (0 : ℂ) R) (hz : z ∈ Λ)
    (hzS : z ∉ S) (hS : ∀ a ∈ S, a ∈ ball (0 : ℂ) R)
    (hb : b ∉ ball (0 : ℂ) R)
    (hμ : μ.restrict Λ {a | a ∈ S ∧ ‖(R : ℂ) ^ 2 - starRingEnd ℂ a * a‖ ≠ R} = 0) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      ((c : ℝ) • (greenPotential univ (Measure.dirac b) -
        greenPotential univ (∑ a ∈ S, Measure.dirac a))) z = g z ∧
      (c : ℝ) • (greenPotential univ (Measure.dirac b) -
        greenPotential univ (∑ a ∈ S, Measure.dirac a)) =ᵐ[μ.restrict Λ] g := by
  obtain ⟨g, hg, hz', hae⟩ :=
    univ_dirac_sub_finset_sum_dirac_has_bounded_representative_of_diagonal
      S hR hΛ hz hzS hS hb hμ
  exact boundedSubharmonicRepresentative_smul hg hz' hae c

#print axioms univ_smul_dirac_sub_finset_sum_dirac_has_bounded_representative

/-- A whole-plane potential with two negative point sources is a test when
its positive atom is outside the observation set and its negative atoms avoid the pole. -/
theorem univ_dirac_sub_two_dirac_mem_subharmonicBallTestClass
    {Λ : Set ℂ} {z a c b : ℂ} (hza : z ≠ a) (hzc : z ≠ c) (hb : b ∉ Λ) :
    greenPotential univ (Measure.dirac b) -
        greenPotential univ (Measure.dirac a + Measure.dirac c) ∈
      subharmonicBallTestClass Λ z := by
  classical
  refine ⟨univ, {b, a, c}, Measure.dirac b, Measure.dirac a + Measure.dirac c,
    0, isOpen_univ, subset_univ _, (isCompact_singleton.insert a).insert b,
    subset_univ _, inferInstance, inferInstance, ?_, ?_, ?_, harmonicOnNhd_const 0,
    ?_, (integrable_dirac enorm_lt_top).add_measure (integrable_dirac enorm_lt_top), ?_⟩
  · simp
  · simp
  · simp [Measure.dirac_apply, hb]
  · simp [hza, hzc]
  · ext x
    simp

#print axioms univ_dirac_sub_two_dirac_mem_subharmonicBallTestClass

/-- A whole-plane test with two negative atoms has a bounded representative for
observation measures charging neither atom. The positive source outside the disc
is absorbed into the harmonic part. -/
theorem univ_three_dirac_has_bounded_representative_of_measure_atoms_eq_zero
    {μ : Measure ℂ} {Λ : Set ℂ} {z a c b : ℂ} {R : ℝ}
    (hR : 0 < R) (hΛ : closure Λ ⊆ ball (0 : ℂ) R) (hz : z ∈ Λ)
    (hza : z ≠ a) (hzc : z ≠ c) (ha : a ∈ ball (0 : ℂ) R)
    (hc : c ∈ ball (0 : ℂ) R) (hb : b ∉ ball (0 : ℂ) R)
    (hμa : μ.restrict Λ {a} = 0) (hμc : μ.restrict Λ {c} = 0) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (greenPotential univ (Measure.dirac b) -
        greenPotential univ (Measure.dirac a + Measure.dirac c)) z = g z ∧
      (greenPotential univ (Measure.dirac b) -
        greenPotential univ (Measure.dirac a + Measure.dirac c)) =ᵐ[μ.restrict Λ] g := by
  classical
  let q := greenPotential univ (Measure.dirac b) - greatestHarmonicMinorantBall R a -
    greatestHarmonicMinorantBall R c
  have hqeq : greenPotential univ (Measure.dirac b) = newtonKernel b := by
    ext x
    simp only [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel,
      newtonKernel_comm x b]
  have hq : HarmonicOnNhd q (ball 0 R) := by
    apply HarmonicOnNhd.sub
    · apply HarmonicOnNhd.sub
      · rw [hqeq]
        intro x hx
        apply harmonicAt_newtonKernel
        intro hxb
        exact hb (hxb ▸ hx)
      · exact (isHarmonicMinorant_greatestHarmonicMinorantBall ha).1
    · exact (isHarmonicMinorant_greatestHarmonicMinorantBall hc).1
  let ν := Measure.dirac a + Measure.dirac c
  let g := q - greenPotential (ball 0 R) ν
  have hg : g ∈ boundedSubharmonicBallTestClass Λ z := by
    refine ⟨ball 0 R, {a, c}, 0, ν, q, isOpen_ball, isBounded_ball,
      hΛ, isCompact_singleton.insert a, ?_, inferInstance, inferInstance, ?_, ?_, ?_, hq,
      ?_, ?_, ?_⟩
    · intro x hx
      simp only [mem_insert_iff, mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact ha
      · exact hc
    · simp
    · simp [ν]
    · simp
    · simp [ν, hza, hzc]
    · exact (integrable_dirac enorm_lt_top).add_measure (integrable_dirac enorm_lt_top)
    · ext x
      simp [g, greenPotential]
  have heq : ∀ x ∈ ball (0 : ℂ) R, x ≠ a → x ≠ c →
      (greenPotential univ (Measure.dirac b) - greenPotential univ ν) x = g x := by
    intro x hx hxa hxc
    simp only [g, q, Pi.sub_apply, ν, greenPotential_add_dirac]
    rw [greenPotential_univ_dirac_eq_ball_add_harmonic_of_ne hR ha hx hxa,
      greenPotential_univ_dirac_eq_ball_add_harmonic_of_ne hR hc hx hxc]
    ring
  refine ⟨g, hg, heq z (hΛ (subset_closure hz)) hza hzc, ?_⟩
  have hne_a : ∀ᵐ x ∂μ.restrict Λ, x ≠ a := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hμa
  have hne_c : ∀ᵐ x ∂μ.restrict Λ, x ≠ c := by
    rw [ae_iff]
    simpa only [not_not, ofPred_eq_eq_singleton] using hμc
  have hball : ∀ᵐ x ∂μ.restrict Λ, x ∈ ball (0 : ℂ) R :=
    ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hΛ)
      (ae_restrict_mem (isOpen_ball.measurableSet))
  filter_upwards [hball, hne_a, hne_c] with x hx hxa hxc
  exact heq x hx hxa hxc

#print axioms univ_three_dirac_has_bounded_representative_of_measure_atoms_eq_zero

/-- The two-negative-atom construction applies to observation measures absolutely
continuous with respect to planar area. -/
theorem univ_three_dirac_has_bounded_representative_of_ac_volume
    {μ : Measure ℂ} {Λ : Set ℂ} {z a c b : ℂ} {R : ℝ}
    (hR : 0 < R) (hΛ : closure Λ ⊆ ball (0 : ℂ) R) (hz : z ∈ Λ)
    (hza : z ≠ a) (hzc : z ≠ c) (ha : a ∈ ball (0 : ℂ) R)
    (hc : c ∈ ball (0 : ℂ) R) (hb : b ∉ ball (0 : ℂ) R)
    (hμ : μ ≪ volume) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (greenPotential univ (Measure.dirac b) -
        greenPotential univ (Measure.dirac a + Measure.dirac c)) z = g z ∧
      (greenPotential univ (Measure.dirac b) -
        greenPotential univ (Measure.dirac a + Measure.dirac c)) =ᵐ[μ.restrict Λ] g := by
  have hμa : μ.restrict Λ {a} = 0 :=
    le_antisymm (((Measure.restrict_le_self : μ.restrict Λ ≤ μ) {a}).trans_eq
      (hμ (measure_singleton a))) bot_le
  have hμc : μ.restrict Λ {c} = 0 :=
    le_antisymm (((Measure.restrict_le_self : μ.restrict Λ ≤ μ) {c}).trans_eq
      (hμ (measure_singleton c))) bot_le
  exact univ_three_dirac_has_bounded_representative_of_measure_atoms_eq_zero
    hR hΛ hz hza hzc ha hc hb hμa hμc

#print axioms univ_three_dirac_has_bounded_representative_of_ac_volume

/-- The construction applies to every observation measure absolutely continuous
with respect to area measure. -/
theorem univ_two_dirac_has_bounded_representative_of_ac_volume
    {μ : Measure ℂ} {Λ : Set ℂ} {z a b : ℂ} {R : ℝ}
    (hR : 0 < R) (hΛ : closure Λ ⊆ ball (0 : ℂ) R) (hz : z ∈ Λ)
    (hza : z ≠ a) (ha : a ∈ ball (0 : ℂ) R) (hb : b ∉ ball (0 : ℂ) R)
    (hμ : μ ≪ volume) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (greenPotential univ (Measure.dirac b) - greenPotential univ (Measure.dirac a)) z = g z ∧
      (greenPotential univ (Measure.dirac b) - greenPotential univ (Measure.dirac a))
        =ᵐ[μ.restrict Λ] g := by
  have ha0 : μ {a} = 0 := hμ (measure_singleton a)
  have hrestrict : μ.restrict Λ {a} = 0 :=
    le_antisymm (((Measure.restrict_le_self : μ.restrict Λ ≤ μ) {a}).trans_eq ha0) bot_le
  exact univ_two_dirac_has_bounded_representative_of_measure_atom_eq_zero
    hR hΛ hz hza ha hb hrestrict

#print axioms univ_two_dirac_has_bounded_representative_of_ac_volume

/-- For radius two, the diagonal correction vanishes at the real atom √2. -/
theorem radius_two_sqrt_two_diagonal_correction :
    ‖((2 : ℝ) : ℂ) ^ 2 - starRingEnd ℂ (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)‖ = 2 := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have heq : starRingEnd ℂ (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = (2 : ℂ) := by
    simp only [Complex.conj_ofReal, ← pow_two, ← Complex.ofReal_pow, hs, Complex.ofReal_ofNat]
  rw [heq]
  norm_num

#print axioms radius_two_sqrt_two_diagonal_correction

/-- A non-centred negative atom at √2 admits the radius-two witness, with the
positive atom removed and with arbitrary observation measure. -/
theorem univ_two_dirac_sqrt_two_has_bounded_representative
    {μ : Measure ℂ} {Λ : Set ℂ} {z b : ℂ}
    (hΛ : closure Λ ⊆ ball (0 : ℂ) 2) (hz : z ∈ Λ)
    (hzatom : z ≠ (Real.sqrt 2 : ℂ)) (hb : b ∉ ball (0 : ℂ) 2) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (greenPotential univ (Measure.dirac b) -
        greenPotential univ (Measure.dirac (Real.sqrt 2 : ℂ))) z = g z ∧
      (greenPotential univ (Measure.dirac b) -
        greenPotential univ (Measure.dirac (Real.sqrt 2 : ℂ))) =ᵐ[μ.restrict Λ] g := by
  have ha : (Real.sqrt 2 : ℂ) ∈ ball (0 : ℂ) 2 := by
    rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  exact univ_two_dirac_has_bounded_representative_of_zero_diagonal_correction
    (by norm_num) hΛ hz hzatom ha hb radius_two_sqrt_two_diagonal_correction

#print axioms univ_two_dirac_sqrt_two_has_bounded_representative

/-- The two-source whole-plane function satisfies the frozen test-class conditions. -/
theorem univ_two_dirac_mem_subharmonicBallTestClass
    {Λ : Set ℂ} {z a : ℂ} (hz0 : z ≠ 0) (ha : a ∉ Λ) :
    greenPotential univ (Measure.dirac a) - greenPotential univ (Measure.dirac 0) ∈
      subharmonicBallTestClass Λ z := by
  classical
  refine ⟨univ, {a, 0}, Measure.dirac a, Measure.dirac 0, 0, isOpen_univ,
    subset_univ _, isCompact_singleton.insert a, subset_univ _,
    inferInstance, inferInstance, ?_, ?_, ?_, harmonicOnNhd_const 0, ?_,
    integrable_dirac enorm_lt_top, ?_⟩
  · simp
  · simp
  · simp [Measure.dirac_apply, ha]
  · simp [hz0]
  · ext x
    simp

#print axioms univ_two_dirac_mem_subharmonicBallTestClass

/-- A whole-plane test with a positive point source outside the unit disc and a
negative point source at its centre has a bounded representative obtained by
removing the positive source and incorporating it into the harmonic part. -/
theorem univ_two_dirac_has_bounded_representative
    {μ : Measure ℂ} {Λ : Set ℂ} {z a : ℂ}
    (hΛ : closure Λ ⊆ ball (0 : ℂ) 1) (hz : z ∈ Λ) (hz0 : z ≠ 0)
    (ha : a ∉ ball (0 : ℂ) 1) :
    ∃ g ∈ boundedSubharmonicBallTestClass Λ z,
      (greenPotential univ (Measure.dirac a) - greenPotential univ (Measure.dirac 0)) z = g z ∧
      (greenPotential univ (Measure.dirac a) - greenPotential univ (Measure.dirac 0))
        =ᵐ[μ.restrict Λ] g := by
  classical
  let q := greenPotential univ (Measure.dirac a)
  have hqeq : q = newtonKernel a := by
    ext x
    simp only [q, greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel,
      newtonKernel_comm x a]
  have hq : HarmonicOnNhd q (ball 0 1) := by
    rw [hqeq]
    intro x hx
    apply harmonicAt_newtonKernel
    intro hxa
    exact ha (hxa ▸ hx)
  let g := q - greenPotential (ball 0 1) (Measure.dirac 0)
  have hg : g ∈ boundedSubharmonicBallTestClass Λ z := by
    refine ⟨ball 0 1, {0}, 0, Measure.dirac 0, q, isOpen_ball, isBounded_ball,
      hΛ, isCompact_singleton, ?_, inferInstance, inferInstance, ?_, ?_, ?_, hq,
      ?_, integrable_dirac enorm_lt_top, ?_⟩
    · simp
    · simp
    · simp
    · simp
    · simp [hz0]
    · ext x
      simp [g, greenPotential]
  refine ⟨g, hg, ?_, ?_⟩
  · simp only [g, q, Pi.sub_apply]
    rw [greenPotential_univ_dirac_zero_eq_unitDisc (hΛ (subset_closure hz))]
  · apply ae_restrict_of_ae_restrict_of_subset (subset_closure.trans hΛ)
    filter_upwards [ae_restrict_mem (isOpen_ball.measurableSet)] with x hx
    simp only [g, q, Pi.sub_apply]
    rw [greenPotential_univ_dirac_zero_eq_unitDisc hx]

#print axioms univ_two_dirac_has_bounded_representative

/-- Away from the source atom, a whole-plane point potential has a bounded
witness with zero source measures. The harmonic part itself is unchanged. -/
theorem neg_univ_dirac_mem_bounded_of_source_outside_closure
    {Λ : Set ℂ} {z a : ℂ} (hΛ : Bornology.IsBounded Λ)
    (ha : a ∉ closure Λ) :
    -greenPotential univ (Measure.dirac a) ∈ boundedSubharmonicBallTestClass Λ z := by
  have heq : -greenPotential univ (Measure.dirac a) = -(newtonKernel a) := by
    ext x
    simp only [Pi.neg_apply, greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel,
      newtonKernel_comm x a]
  rw [heq]
  apply harmonic_mem_boundedSubharmonicBallTestClass hΛ isOpen_compl_singleton
  · intro x hx
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hxa
    subst x
    exact ha hx
  · intro x hx
    apply HarmonicAt.neg
    apply harmonicAt_newtonKernel
    simpa only [mem_compl_iff, mem_singleton_iff] using hx

#print axioms neg_univ_dirac_mem_bounded_of_source_outside_closure

/-- The negative Dirac potential used in the obstruction is an admissible frozen test. -/
theorem neg_dirac_disc_mem_subharmonicBallTestClass :
    -greenPotential (ball 0 2) (Measure.dirac 0) ∈
      subharmonicBallTestClass (ball 0 (1 / 2 : ℝ)) (1 / 4 : ℂ) := by
  classical
  refine ⟨ball 0 2, {0}, 0, Measure.dirac 0, 0, isOpen_ball, ?_,
    isCompact_singleton, ?_, inferInstance, inferInstance, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (closure_ball_subset_closedBall.trans (closedBall_subset_ball (by norm_num)))
  · simp only [singleton_subset_iff, mem_ball_self (by norm_num : (0 : ℝ) < 2)]
  · simp
  · simp
  · simp
  · exact harmonicOnNhd_const 0
  · simp
  · exact integrable_dirac enorm_lt_top
  · ext x
    simp [greenPotential]

#print axioms neg_dirac_disc_mem_subharmonicBallTestClass

/-- An atom visible to the observation measure obstructs an unchanged-source harmonic
correction between the two discs. This does not exclude representatives with new sources. -/
theorem no_dirac_harmonic_correction_on_discs :
    ¬ ∃ a : ℂ → ℝ, HarmonicOnNhd a (ball 0 1) ∧
      (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (1 / 2 : ℝ)),
        greenPotential (ball 0 2) (Measure.dirac 0) x =
          a x + greenPotential (ball 0 1) (Measure.dirac 0) x) := by
  classical
  rintro ⟨a, ha, hae⟩
  rw [Measure.restrict_add, ae_add_measure_iff] at hae
  have hzero : a 0 = 0 := by
    have h := hae.2
    rw [restrict_dirac, ite_eq_left (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)),
      ae_dirac_eq] at h
    exact dirac_source_correction_at_atom h
  have hconstant : ∀ᵐ x ∂volume.restrict (ball (0 : ℂ) (1 / 2 : ℝ)),
      a x = (2 * Real.pi)⁻¹ * Real.log 2 := by
    filter_upwards [hae.1, ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with x hx hxb hx0
    have hx1 : x ∈ ball (0 : ℂ) 1 := (ball_subset_ball (by norm_num)) hxb
    have hx2 : x ∈ ball (0 : ℂ) 2 := (ball_subset_ball (by norm_num)) hx1
    rw [greenPotential_dirac_zero_ball (by norm_num) hx2 hx0,
      greenPotential_dirac_zero_ball (by norm_num) hx1 hx0] at hx
    simp only [Real.log_one] at hx
    linarith
  have ha' : ContinuousOn a (ball (0 : ℂ) (1 / 2 : ℝ)) :=
    ha.continuousOn.mono (ball_subset_ball (by norm_num))
  have heq := Measure.eqOn_open_of_ae_eq hconstant isOpen_ball ha' continuousOn_const
  have h := heq (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
  rw [hzero] at h
  have hp : 0 < (2 * Real.pi)⁻¹ * Real.log 2 :=
    mul_pos (by positivity) (Real.log_pos (by norm_num))
  linarith

/-- Except at radius one, no concentric disc containing the observation disc admits
an unchanged-Dirac harmonic correction of the whole-plane potential for this measure. -/
theorem no_dirac_harmonic_correction_univ_to_ball {ρ R : ℝ}
    (hρ : 0 < ρ) (hR : ρ ≤ R) (hR1 : R ≠ 1) :
    ¬ ∃ a : ℂ → ℝ, HarmonicOnNhd a (ball 0 R) ∧
      (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 ρ),
        greenPotential univ (Measure.dirac 0) x =
          a x + greenPotential (ball 0 R) (Measure.dirac 0) x) := by
  classical
  rintro ⟨a, ha, hae⟩
  rw [Measure.restrict_add, ae_add_measure_iff] at hae
  have hzero : a 0 = 0 := by
    have h := hae.2
    rw [restrict_dirac, ite_eq_left (mem_ball_self hρ),
      ae_dirac_eq] at h
    exact dirac_source_correction_at_atom h
  have hRpos : 0 < R := lt_of_lt_of_le hρ hR
  have hconstant : ∀ᵐ x ∂volume.restrict (ball (0 : ℂ) ρ),
      a x = -((2 * Real.pi)⁻¹ * Real.log R) := by
    filter_upwards [hae.1, ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with x hx hxb hx0
    have hxR : x ∈ ball (0 : ℂ) R := (ball_subset_ball hR) hxb
    rw [greenPotential_dirac_zero_ball hRpos hxR hx0] at hx
    simp only [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel,
      newtonKernel, sub_zero] at hx
    linarith
  have ha' : ContinuousOn a (ball (0 : ℂ) ρ) :=
    ha.continuousOn.mono (ball_subset_ball hR)
  have heq := Measure.eqOn_open_of_ae_eq hconstant isOpen_ball ha' continuousOn_const
  have h := heq (mem_ball_self hρ)
  rw [hzero] at h
  have hp : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  have hl := Real.log_ne_zero_of_pos_of_ne_one hRpos hR1
  exact mul_ne_zero hp hl (by linarith)

#print axioms no_dirac_harmonic_correction_univ_to_ball

/-- On any bounded domain containing a disc of radius greater than one, the
unchanged-source correction of the whole-plane Dirac potential cannot be continuous
at the source atom. -/
theorem no_bounded_domain_continuousAt_source_correction_for_large_observation
    {V : Set ℂ} {ρ R : ℝ} (hρ : 0 < ρ) (hR : 1 < R) (hρR : ρ ≤ R)
    (hV : Bornology.IsBounded V) (hsub : ball (0 : ℂ) R ⊆ V) :
    ¬ ∃ a : ℂ → ℝ, ContinuousAt a 0 ∧
      (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 ρ),
        greenPotential univ (Measure.dirac 0) x =
          a x + greenPotential V (Measure.dirac 0) x) := by
  classical
  rintro ⟨a, ha, hae⟩
  rw [Measure.restrict_add, ae_add_measure_iff] at hae
  have hzero : a 0 = 0 := by
    have h := hae.2
    rw [restrict_dirac, ite_eq_left (mem_ball_self hρ),
      ae_dirac_eq] at h
    exact dirac_source_correction_at_atom h
  let c : ℝ := (2 * Real.pi)⁻¹ * Real.log R
  have hc : 0 < c := mul_pos (by positivity) (Real.log_pos hR)
  have hbound : ∀ᵐ x ∂volume.restrict (ball (0 : ℂ) ρ), a x ≤ -c := by
    filter_upwards [hae.1, ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with x hx hxb hx0
    have hxbR : x ∈ ball (0 : ℂ) R := ball_subset_ball hρR hxb
    have hRpos : 0 < R := lt_trans zero_lt_one hR
    have hm := Section6.greenFunction_mono hsub hV hxbR
      (mem_ball_self hRpos) hx0
    have hb := greenPotential_dirac_zero_ball hRpos hxbR hx0
    simp only [greenPotential, integral_dirac] at hb hx
    simp only [greenFunction_univ_eq_newtonKernel, newtonKernel, sub_zero] at hx
    dsimp [c] at *
    linarith
  have hnear : {x | -c < a x} ∈ nhds (0 : ℂ) :=
    ha (Ioi_mem_nhds (by rw [hzero]; linarith))
  obtain ⟨r, hr, hrsub⟩ := Metric.mem_nhds_iff.mp hnear
  let t := min r ρ
  have ht : 0 < t := lt_min hr hρ
  have htsub : ball (0 : ℂ) t ⊆ ball 0 ρ := ball_subset_ball (min_le_right _ _)
  have htnear : ball (0 : ℂ) t ⊆ {x | -c < a x} :=
    (ball_subset_ball (min_le_left _ _)).trans hrsub
  obtain ⟨x, hx, hxa⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    (ne_of_gt (Metric.measure_ball_pos volume (0 : ℂ) ht))
    (ae_restrict_of_ae_restrict_of_subset htsub hbound)
  have hxb : -c < a x := htnear hx
  exact (not_lt_of_ge hxa) hxb

#print axioms no_bounded_domain_continuousAt_source_correction_for_large_observation

/-- Even after adding arbitrary positive and negative residual sources, a
bounded-domain witness cannot match the whole-plane point-source potential on
the large observation disc if both residual potentials are continuous at the
atom and the negative residual kernel is integrable there almost everywhere. -/
theorem no_changed_source_continuous_residual_for_large_observation
    {V : Set ℂ} {η₁ η₂ : Measure ℂ} {q : ℂ → ℝ}
    (hV : Bornology.IsBounded V) (hsub : ball (0 : ℂ) 2 ⊆ V)
    (hq : ContinuousAt q 0)
    (h₁ : ContinuousAt (greenPotential V η₁) 0)
    (h₂ : ContinuousAt (greenPotential V η₂) 0)
    (hi : ∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (2 : ℝ)),
      Integrable (greenFunction V x) η₂) :
    ¬ (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (2 : ℝ)),
      -greenPotential univ (Measure.dirac 0) x =
        q x + greenPotential V η₁ x - greenPotential V (Measure.dirac 0 + η₂) x) := by
  intro heq
  apply no_bounded_domain_continuousAt_source_correction_for_large_observation (ρ := 2) (R := 2)
    (by norm_num) (by norm_num) (by norm_num) hV hsub
  refine ⟨fun x => -q x - greenPotential V η₁ x + greenPotential V η₂ x,
    (hq.neg.sub h₁).add h₂, ?_⟩
  filter_upwards [heq, hi] with x hx hix
  have hd : Integrable (greenFunction V x) (Measure.dirac (0 : ℂ)) :=
    integrable_dirac enorm_lt_top
  have hsum : greenPotential V (Measure.dirac (0 : ℂ) + η₂) x =
      greenPotential V (Measure.dirac 0) x + greenPotential V η₂ x :=
    integral_add_measure hd hix
  rw [hsum] at hx
  linarith

#print axioms no_changed_source_continuous_residual_for_large_observation

/-- A measure with a unit atom splits into that atom and its restriction to
the complement, without any global finiteness assumption. -/
theorem measure_eq_dirac_add_restrict_compl_of_singleton_eq_one
    {ν : Measure ℂ} {a : ℂ} (ha : ν {a} = 1) :
    ν = Measure.dirac a + ν.restrict {a}ᶜ := by
  have h := (Measure.restrict_add_restrict_compl (μ := ν) (measurableSet_singleton a)).symm
  rw [Measure.restrict_singleton, ha, one_smul] at h
  exact h

/-- The changed-source obstruction applies directly to any negative source
with a unit atom, provided its atom-free residual potential is continuous and
the full negative kernel is integrable almost everywhere on the observation
disc. No source decomposition is assumed. -/
theorem no_changed_source_unit_atom_for_large_observation
    {V : Set ℂ} {η₁ η₂ : Measure ℂ} {q : ℂ → ℝ}
    (hV : Bornology.IsBounded V) (hsub : ball (0 : ℂ) 2 ⊆ V)
    (hatom : η₂ {0} = 1) (hq : ContinuousAt q 0)
    (h₁ : ContinuousAt (greenPotential V η₁) 0)
    (h₂ : ContinuousAt (greenPotential V (η₂.restrict {0}ᶜ)) 0)
    (hi : ∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (2 : ℝ)),
      Integrable (greenFunction V x) η₂) :
    ¬ (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (2 : ℝ)),
      -greenPotential univ (Measure.dirac 0) x =
        q x + greenPotential V η₁ x - greenPotential V η₂ x) := by
  have hsplit := measure_eq_dirac_add_restrict_compl_of_singleton_eq_one hatom
  have hirest : ∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (2 : ℝ)),
      Integrable (greenFunction V x) (η₂.restrict {0}ᶜ) := by
    filter_upwards [hi] with x hx
    exact hx.mono_measure Measure.restrict_le_self
  intro heq
  apply no_changed_source_continuous_residual_for_large_observation hV hsub hq h₁ h₂ hirest
  simpa only [← hsplit] using heq

#print axioms measure_eq_dirac_add_restrict_compl_of_singleton_eq_one
#print axioms no_changed_source_unit_atom_for_large_observation

/-- In particular, a correction continuous on the observation disc cannot exist. -/
theorem no_bounded_domain_continuous_source_correction_for_large_observation
    {V : Set ℂ} (hV : Bornology.IsBounded V) (hsub : ball (0 : ℂ) 2 ⊆ V) :
    ¬ ∃ a : ℂ → ℝ, ContinuousOn a (ball 0 2) ∧
      (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (2 : ℝ)),
        greenPotential univ (Measure.dirac 0) x =
          a x + greenPotential V (Measure.dirac 0) x) := by
  rintro ⟨a, ha, hae⟩
  exact no_bounded_domain_continuousAt_source_correction_for_large_observation
    (by norm_num) (by norm_num) (by norm_num) hV hsub ⟨a, (ha 0 (mem_ball_self (by norm_num : (0 : ℝ) < 2))).continuousAt
      (isOpen_ball.mem_nhds (mem_ball_self (by norm_num : (0 : ℝ) < 2))), hae⟩

#print axioms no_bounded_domain_continuous_source_correction_for_large_observation

/-- No bounded domain containing the radius-two observation disc admits an
unchanged-source harmonic correction for the whole-plane Dirac potential. -/
theorem no_bounded_domain_source_correction_for_large_observation
    {V : Set ℂ} (hV : Bornology.IsBounded V) (hsub : ball (0 : ℂ) 2 ⊆ V) :
    ¬ ∃ a : ℂ → ℝ, HarmonicOnNhd a V ∧
      (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (2 : ℝ)),
        greenPotential univ (Measure.dirac 0) x =
          a x + greenPotential V (Measure.dirac 0) x) := by
  rintro ⟨a, ha, hae⟩
  exact no_bounded_domain_continuous_source_correction_for_large_observation hV hsub
    ⟨a, ha.continuousOn.mono hsub, hae⟩

#print axioms no_bounded_domain_source_correction_for_large_observation

/-- The same obstruction holds when equality is required pointwise on the disc,
as it is in the universal-measure representative reduction. -/
theorem no_bounded_domain_pointwise_source_correction_for_large_observation
    {V : Set ℂ} (hV : Bornology.IsBounded V) (hsub : ball (0 : ℂ) 2 ⊆ V) :
    ¬ ∃ a : ℂ → ℝ, ContinuousOn a (ball 0 2) ∧
      (∀ x ∈ ball (0 : ℂ) 2, greenPotential univ (Measure.dirac 0) x =
          a x + greenPotential V (Measure.dirac 0) x) := by
  rintro ⟨a, ha, heq⟩
  exact no_bounded_domain_continuous_source_correction_for_large_observation hV hsub
    ⟨a, ha, ae_restrict_of_forall_mem measurableSet_ball heq⟩

#print axioms no_bounded_domain_pointwise_source_correction_for_large_observation

/-- For the radius-two observation disc, no concentric disc satisfying the actual
closure-containment condition admits an unchanged-source harmonic correction. -/
theorem no_concentric_disc_source_correction_for_large_observation :
    ¬ ∃ (R : ℝ) (a : ℂ → ℝ),
      closure (ball (0 : ℂ) 2) ⊆ ball 0 R ∧ HarmonicOnNhd a (ball 0 R) ∧
      (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (2 : ℝ)),
        greenPotential univ (Measure.dirac 0) x =
          a x + greenPotential (ball 0 R) (Measure.dirac 0) x) := by
  rintro ⟨R, a, hcontain, ha, hae⟩
  have htwo : (2 : ℂ) ∈ closure (ball (0 : ℂ) 2) := by
    rw [closure_ball (0 : ℂ) (by norm_num : (2 : ℝ) ≠ 0)]
    simp [Metric.mem_closedBall, dist_zero_right]
  have hR : (2 : ℝ) < R := by
    have h := hcontain htwo
    simpa [Metric.mem_ball, dist_zero_right] using h
  exact no_dirac_harmonic_correction_univ_to_ball (by norm_num : (0 : ℝ) < 2)
    hR.le (by linarith) ⟨a, ha, hae⟩

#print axioms no_concentric_disc_source_correction_for_large_observation

/-- For a whole-plane point source, replacing the witness by the disc of radius two
cannot be achieved with an unchanged source and a harmonic correction when the
observation measure sees both area and the atom. A different bounded witness may work. -/
theorem no_dirac_harmonic_correction_univ_to_disc :
    ¬ ∃ a : ℂ → ℝ, HarmonicOnNhd a (ball 0 2) ∧
      (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (1 / 2 : ℝ)),
        greenPotential univ (Measure.dirac 0) x =
          a x + greenPotential (ball 0 2) (Measure.dirac 0) x) :=
  no_dirac_harmonic_correction_univ_to_ball (by norm_num) (by norm_num) (by norm_num)

#print axioms no_dirac_harmonic_correction_univ_to_disc

#print axioms no_dirac_harmonic_correction_on_discs
#print axioms greenPotential_dirac_zero_ball
#print axioms dirac_source_correction_at_atom
#print axioms exists_bounded_open_containing_closure_and_compact
#print axioms bounded_representative_of_source_corrections

end HarmonicBalls
