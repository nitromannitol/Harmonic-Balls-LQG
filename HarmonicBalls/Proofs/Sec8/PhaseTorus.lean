import HarmonicBalls.Proofs.Sec8.PhaseScaleTransport
import Mathlib.Dynamics.Ergodic.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-! # A measurable phase torus

Two unit circles encode the lattice phase. The chosen half-open representatives
are measurable and double modulo the lattice with spacing `1 / 100`.
-/

open MeasureTheory

namespace HarmonicBalls

/-- The unit circle used for one coordinate of the lattice phase. -/
abbrev PhaseCircle := AddCircle (1 : ℝ)

/-- The two independent coordinates of a lattice phase. -/
abbrev PhaseTorus := PhaseCircle × PhaseCircle

instance phaseCircleVolumeIsProbability : IsProbabilityMeasure (volume : Measure PhaseCircle) where
  measure_univ := by simp

/-- The unique representative in the half-open unit interval. -/
noncomputable def phaseCircleRep (x : PhaseCircle) : ℝ :=
  ((AddCircle.measurableEquivIco (1 : ℝ) 0) x).val

@[simp] theorem coe_phaseCircleRep (x : PhaseCircle) :
    (phaseCircleRep x : PhaseCircle) = x := by
  exact AddCircle.coe_equivIco

/-- The half-open representative is Borel measurable. -/
theorem measurable_phaseCircleRep : Measurable phaseCircleRep :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

/-- The two representatives, scaled to the period of the outer lattice. -/
noncomputable def torusPhase (p : PhaseTorus) : ℂ :=
  ((phaseCircleRep p.1 / 100 : ℝ) : ℂ) +
    ((phaseCircleRep p.2 / 100 : ℝ) : ℂ) * Complex.I

/-- Dyadic rescaling doubles both circle coordinates. -/
def phaseTorusDouble (p : PhaseTorus) : PhaseTorus := (2 • p.1, 2 • p.2)

/-- The phase representative is Borel measurable. -/
theorem measurable_torusPhase : Measurable torusPhase := by
  have h₁ : Measurable (fun p : PhaseTorus => phaseCircleRep p.1 / 100) :=
    (measurable_phaseCircleRep.comp measurable_fst).div_const 100
  have h₂ : Measurable (fun p : PhaseTorus => phaseCircleRep p.2 / 100) :=
    (measurable_phaseCircleRep.comp measurable_snd).div_const 100
  exact (Complex.continuous_ofReal.measurable.comp h₁).add
    ((Complex.continuous_ofReal.measurable.comp h₂).mul_const Complex.I)

/-- Doubling the circle changes its representative by an integer. -/
theorem phaseCircleRep_double_sub (x : PhaseCircle) :
    ∃ j : ℤ, phaseCircleRep (2 • x) - 2 * phaseCircleRep x = (j : ℝ) := by
  have hzero : ((phaseCircleRep (2 • x) - 2 * phaseCircleRep x : ℝ) : PhaseCircle) = 0 := by
    have hmul : 2 * phaseCircleRep x = (2 : ℕ) • phaseCircleRep x := by simp
    rw [hmul, AddCircle.coe_sub, AddCircle.coe_nsmul,
      coe_phaseCircleRep, coe_phaseCircleRep, sub_self]
  obtain ⟨j, hj⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  refine ⟨j, ?_⟩
  simpa only [zsmul_eq_mul, mul_one] using hj.symm

/-- Doubling the torus doubles the chosen phase modulo the outer lattice. -/
theorem torusPhase_double_sub_mem_lattice (p : PhaseTorus) :
    torusPhase (phaseTorusDouble p) - (2 : ℝ) • torusPhase p ∈
      Section6.scaledLattice ((1 : ℝ) / 100) := by
  obtain ⟨j, hj⟩ := phaseCircleRep_double_sub p.1
  obtain ⟨k, hk⟩ := phaseCircleRep_double_sub p.2
  refine ⟨j, k, ?_⟩
  apply Complex.ext
  · simp [torusPhase, phaseTorusDouble]
    linarith
  · simp [torusPhase, phaseTorusDouble]
    linarith

/-- The torus class of a complex phase, in units of the outer-lattice period. -/
def phaseTorusOfComplex (z : ℂ) : PhaseTorus :=
  (((100 * z.re : ℝ) : PhaseCircle), ((100 * z.im : ℝ) : PhaseCircle))

/-- Passing from a complex phase to its torus class is measurable. -/
theorem measurable_phaseTorusOfComplex : Measurable phaseTorusOfComplex := by
  unfold phaseTorusOfComplex
  exact (AddCircle.measurable_mk'.comp (measurable_const.mul Complex.measurable_re)).prodMk
    (AddCircle.measurable_mk'.comp (measurable_const.mul Complex.measurable_im))

/-- A representative of a real circle class differs from the original real
number by an integer. -/
theorem phaseCircleRep_coe_sub (r : ℝ) :
    ∃ j : ℤ, phaseCircleRep (r : PhaseCircle) - r = (j : ℝ) := by
  have hzero : ((phaseCircleRep (r : PhaseCircle) - r : ℝ) : PhaseCircle) = 0 := by
    rw [AddCircle.coe_sub, coe_phaseCircleRep, sub_self]
  obtain ⟨j, hj⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hzero
  refine ⟨j, ?_⟩
  simpa only [zsmul_eq_mul, mul_one] using hj.symm

/-- The torus representative of an arbitrary complex phase differs from it
by an outer-lattice vector. -/
theorem torusPhase_ofComplex_sub_mem_lattice (z : ℂ) :
    torusPhase (phaseTorusOfComplex z) - z ∈
      Section6.scaledLattice ((1 : ℝ) / 100) := by
  obtain ⟨j, hj⟩ := phaseCircleRep_coe_sub (100 * z.re)
  obtain ⟨k, hk⟩ := phaseCircleRep_coe_sub (100 * z.im)
  refine ⟨j, k, ?_⟩
  apply Complex.ext
  · simp [torusPhase, phaseTorusOfComplex]
    linarith
  · simp [torusPhase, phaseTorusOfComplex]
    linarith

/-- Taking a torus class commutes with dyadic doubling. -/
theorem phaseTorusOfComplex_double (z : ℂ) :
    phaseTorusOfComplex ((2 : ℝ) • z) = phaseTorusDouble (phaseTorusOfComplex z) := by
  apply Prod.ext
  · simp only [phaseTorusOfComplex, phaseTorusDouble, Complex.smul_re]
    rw [← AddCircle.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring
  · simp only [phaseTorusOfComplex, phaseTorusDouble, Complex.smul_im]
    rw [← AddCircle.coe_nsmul]
    congr 1
    simp only [nsmul_eq_mul]
    ring

/-- The normalized phase of a fixed centre follows the dyadic torus orbit. -/
theorem phaseTorusOfComplex_normalizedPhase (z : ℂ) (n : ℕ) :
    phaseTorusOfComplex (-((dyadicScale n)⁻¹ • z)) =
      (phaseTorusDouble^[n]) (phaseTorusOfComplex (-z)) := by
  induction n with
  | zero => simp [dyadicScale]
  | succ n ih =>
    rw [normalizedPhase_dyadic_succ, phaseTorusOfComplex_double, ih,
      Function.iterate_succ_apply']

/-- Replacing a phase by its torus representative preserves the full shifted
event at every dyadic scale. -/
theorem phaseVeryGoodAnnulus_torusPhase_ofComplex (μ : Measure ℂ) (β : ℝ)
    (n N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) (z : ℂ) :
    PhaseVeryGoodAnnulus μ β (dyadicScale n) 0 N a b C₁m C₁p C₂m C₂p C₃
        (torusPhase (phaseTorusOfComplex z)) ↔
      PhaseVeryGoodAnnulus μ β (dyadicScale n) 0 N a b C₁m C₁p C₂m C₂p C₃ z := by
  have h : torusPhase (phaseTorusOfComplex z) - z ∈
      Section6.scaledLattice (dyadicScale n / 100) := by
    simpa only [mul_one] using
      scaledLattice_outer_subset_dyadic 1 n (torusPhase_ofComplex_sub_mem_lattice z)
  have heq : z + (torusPhase (phaseTorusOfComplex z) - z) =
      torusPhase (phaseTorusOfComplex z) := by abel
  have hperiod := phaseVeryGoodAnnulus_outer_period μ β (dyadicScale n) 0 N
    a b C₁m C₁p C₂m C₂p C₃ z h
  rw [heq] at hperiod
  exact hperiod.symm

/-- A very-good annulus at a translated centre has exactly the normalized
unit-scale event with the corresponding torus phase. -/
theorem isVeryGoodAnnulus_iff_normalized_torus_phase (μ : Measure ℂ)
    (hcirc : ℝ → ℂ → ℝ) (γ α β : ℝ) {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ)
    (N : ℕ) (a b C₁m C₁p C₂m C₂p C₃ : ℝ) :
    IsVeryGoodAnnulus μ β ρ z N a b C₁m C₁p C₂m C₂p C₃ ↔
      PhaseVeryGoodAnnulus
        (normalizedPullbackMeasure γ α ρ hcirc (μ.map (fun w : ℂ => w - z)))
        β 1 0 N a b C₁m C₁p C₂m C₂p C₃
        (torusPhase (phaseTorusOfComplex (-(ρ⁻¹ • z)))) := by
  rw [isVeryGoodAnnulus_iff_normalized_shifted_phase μ hcirc γ α β hρ z N
    a b C₁m C₁p C₂m C₂p C₃]
  simpa only [dyadicScale, pow_zero] using
    (phaseVeryGoodAnnulus_torusPhase_ofComplex
      (normalizedPullbackMeasure γ α ρ hcirc (μ.map (fun w : ℂ => w - z)))
      β 0 N a b C₁m C₁p C₂m C₂p C₃ (-(ρ⁻¹ • z))).symm

/-- Haar measure on each circle is preserved by doubling. -/
theorem measurePreserving_phaseTorusDouble :
    MeasurePreserving phaseTorusDouble
      ((volume : Measure PhaseCircle).prod volume) ((volume : Measure PhaseCircle).prod volume) := by
  exact (AddCircle.ergodic_nsmul (T := (1 : ℝ)) (n := 2) (by norm_num)).toMeasurePreserving.prod
    (AddCircle.ergodic_nsmul (T := (1 : ℝ)) (n := 2) (by norm_num)).toMeasurePreserving

end HarmonicBalls
