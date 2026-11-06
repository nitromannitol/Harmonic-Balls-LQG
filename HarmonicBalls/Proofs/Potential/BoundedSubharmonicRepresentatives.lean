import HarmonicBalls.Audit.GreenSubharmonicTestClass
import HarmonicBalls.Proofs.Potential.GreenBall
import HarmonicBalls.Proofs.Potential.GreenPositivity
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Analysis.Analytic.Polynomial

/-!
# Bounded witnesses for subharmonic tests

A geometric localization and a conditional transport of the two source potentials.
The latter records the separate pointwise and almost-everywhere correction obligations;
it does not establish them. Leonardo Bonanno contributed to this formalization.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set InnerProductSpace

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
theorem no_dirac_harmonic_correction_univ_to_ball {R : ℝ}
    (hR : (1 / 2 : ℝ) < R) (hR1 : R ≠ 1) :
    ¬ ∃ a : ℂ → ℝ, HarmonicOnNhd a (ball 0 R) ∧
      (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (1 / 2 : ℝ)),
        greenPotential univ (Measure.dirac 0) x =
          a x + greenPotential (ball 0 R) (Measure.dirac 0) x) := by
  classical
  rintro ⟨a, ha, hae⟩
  rw [Measure.restrict_add, ae_add_measure_iff] at hae
  have hzero : a 0 = 0 := by
    have h := hae.2
    rw [restrict_dirac, ite_eq_left (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2)),
      ae_dirac_eq] at h
    exact dirac_source_correction_at_atom h
  have hRpos : 0 < R := by linarith
  have hconstant : ∀ᵐ x ∂volume.restrict (ball (0 : ℂ) (1 / 2 : ℝ)),
      a x = -((2 * Real.pi)⁻¹ * Real.log R) := by
    filter_upwards [hae.1, ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with x hx hxb hx0
    have hxR : x ∈ ball (0 : ℂ) R := (ball_subset_ball hR.le) hxb
    rw [greenPotential_dirac_zero_ball hRpos hxR hx0] at hx
    simp only [greenPotential, integral_dirac, greenFunction_univ_eq_newtonKernel,
      newtonKernel, sub_zero] at hx
    linarith
  have ha' : ContinuousOn a (ball (0 : ℂ) (1 / 2 : ℝ)) :=
    ha.continuousOn.mono (ball_subset_ball hR.le)
  have heq := Measure.eqOn_open_of_ae_eq hconstant isOpen_ball ha' continuousOn_const
  have h := heq (mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
  rw [hzero] at h
  have hp : (2 * Real.pi)⁻¹ ≠ 0 := by positivity
  have hl := Real.log_ne_zero_of_pos_of_ne_one hRpos hR1
  exact mul_ne_zero hp hl (by linarith)

#print axioms no_dirac_harmonic_correction_univ_to_ball

/-- For a whole-plane point source, replacing the witness by the disc of radius two
cannot be achieved with an unchanged source and a harmonic correction when the
observation measure sees both area and the atom. A different bounded witness may work. -/
theorem no_dirac_harmonic_correction_univ_to_disc :
    ¬ ∃ a : ℂ → ℝ, HarmonicOnNhd a (ball 0 2) ∧
      (∀ᵐ x ∂(volume + Measure.dirac (0 : ℂ)).restrict (ball 0 (1 / 2 : ℝ)),
        greenPotential univ (Measure.dirac 0) x =
          a x + greenPotential (ball 0 2) (Measure.dirac 0) x) :=
  no_dirac_harmonic_correction_univ_to_ball (by norm_num) (by norm_num)

#print axioms no_dirac_harmonic_correction_univ_to_disc

#print axioms no_dirac_harmonic_correction_on_discs
#print axioms greenPotential_dirac_zero_ball
#print axioms dirac_source_correction_at_atom
#print axioms exists_bounded_open_containing_closure_and_compact
#print axioms bounded_representative_of_source_corrections

end HarmonicBalls
