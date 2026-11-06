import HarmonicBalls.Audit.GreenSubharmonicTestClass
import HarmonicBalls.Proofs.Potential.GreenBall
import HarmonicBalls.Proofs.Potential.GreenPositivity
import HarmonicBalls.Proofs.Sec6.GreenMono
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.MeasureTheory.Measure.Count

/-!
# Bounded witnesses for subharmonic tests

A geometric localization and a conditional transport of the two source potentials.
The latter records the separate pointwise and almost-everywhere correction obligations;
it does not establish them. Leonardo Bonanno contributed to this formalization.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace

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
