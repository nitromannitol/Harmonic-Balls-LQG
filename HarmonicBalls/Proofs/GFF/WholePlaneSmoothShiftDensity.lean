import HarmonicBalls.Proofs.Sec8.WholePlaneSmoothShift
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.Polar

/-! # Radon–Nikodym density of smooth shifts of the whole-plane GFF

Miller–Sheffield, *Imaginary Geometry IV*, arXiv:1302.4738v2, Proposition 2.9 (first sentence,
printed p. 49): for a whole-plane GFF `h` defined up to a global additive constant in `ℝ` and a
fixed `g`, the laws of `h + g` and `h` are mutually absolutely continuous, with Radon–Nikodym
derivative `Z⁻¹ e^{(h, g)_∇}`, where `Z` is a normalization constant.

We prove this for the frozen whole-plane GFF `IsWholePlaneGFF P hC hcirc` and every smooth
compactly supported `g` (`LQGMetric.TestC`). The field modulo additive constants is represented
by its pairings with mean-zero test functions, `Section6.pairingProc hC : Ω → (TestC0 → ℝ)`,
and its law is the law on `TestC0 → ℝ` with the product σ-algebra; the shifted field `h + g` has
pairings `(h, φ) + ∫ φ g`. Events of the field are therefore the preimages under
`Section6.pairingProc hC` of measurable subsets of `TestC0 → ℝ`.

The Dirichlet inner product of the source (printed p. 47) is `(f, g)_∇ = (2π)⁻¹ ∫ ∇f · ∇g`. For a
smooth compactly supported `g`, integration by parts gives `(h, g)_∇ = (h, -Δg/(2π))`, the pairing
of `h` with the mean-zero test function `LQGMetric.cmTest g = -Δg/(2π)`. The source states that
`((h, f)_∇)_f` is centered with covariance `(f, g)_∇`; this normalization is checked here
(`IsWholePlaneGFF.covariance_dirichletPairing`), so `Z = E e^{(h, g)_∇} = e^{(g, g)_∇ / 2}`.

## Main results

For `hh : IsWholePlaneGFF P hC hcirc` and smooth compactly supported `f`, `g`:
* `IsWholePlaneGFF.integral_dirichletPairing` : `E (h, g)_∇ = 0`;
* `IsWholePlaneGFF.covariance_pairing_dirichletPairing` : `Cov((h, φ), (h, g)_∇) = ∫ φ g` for
  mean-zero `φ`;
* `IsWholePlaneGFF.covariance_dirichletPairing` : `Cov((h, f)_∇, (h, g)_∇) = (f, g)_∇`;
* `IsWholePlaneGFF.variance_dirichletPairing` : `Var (h, g)_∇ = (g, g)_∇ = (2π)⁻¹ ∫ |∇g|²`;
* `IsWholePlaneGFF.integral_exp_dirichletPairing` : `E e^{(h, g)_∇} = e^{(g, g)_∇ / 2}`;
* `IsWholePlaneGFF.map_smooth_shift_eq_withDensity` : `law(h + g) = Z⁻¹ e^{(h, g)_∇} · law(h)`;
* `IsWholePlaneGFF.rnDeriv_map_smooth_shift` : the same as a Radon–Nikodym derivative;
* `IsWholePlaneGFF.smooth_shift_density` : Proposition 2.9 for field events, with
  `Z = E e^{(h, g)_∇} = e^{(g, g)_∇ / 2} > 0` and mutual absolute continuity;
* `IsWholePlaneGFF.smooth_shift_density_of_isTestFunction` : the same for `IsTestFunction univ g`,
  with `-Δg/(2π)` and `(2π)⁻¹ ∫ |∇g|²` written out.

The proof applies the Gaussian-process Cameron–Martin theorem
`QuantumZipper.CameronMartin.map_tiltMeasure_path` and the Green identities
`LQGMetric.logCov_cmTest_right`, `LQGMetric.logCov_cmTest_cmTest` from Leonardo Bonanno's
formalization.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Laplacian
open scoped ENNReal Real

namespace HarmonicBalls

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The Dirichlet pairing `(h, g)_∇ = (h, -Δg/(2π))` of the whole-plane GFF is centered. -/
theorem IsWholePlaneGFF.integral_dirichletPairing (hh : IsWholePlaneGFF P hC hcirc)
    (g : LQGMetric.TestC) : ∫ ω, hC ω (LQGMetric.cmTest g) ∂P = 0 :=
  hh.integral_eq_zero (.pairing (LQGMetric.cmTest g))
    (Section6.isTestFunction_of_testC (LQGMetric.cmTest g))

/-- The covariance of a mean-zero pairing `(h, φ)` with the Dirichlet pairing `(h, g)_∇` is the
`L²` pairing `∫ φ g`. -/
theorem IsWholePlaneGFF.covariance_pairing_dirichletPairing (hh : IsWholePlaneGFF P hC hcirc)
    (g : LQGMetric.TestC) (φ : LQGMetric.TestC0) :
    cov[fun ω => hC ω φ.1, fun ω => hC ω (LQGMetric.cmTest g); P] = ∫ x, φ.1 x * g x := by
  have hc := hh.covariance_eq (.pairing φ.1) (.pairing (LQGMetric.cmTest0 g).1)
    (Section6.isTestFunction_of_testC φ.1)
    (Section6.isTestFunction_of_testC (LQGMetric.cmTest0 g).1)
  change cov[fun ω => hC ω φ.1, fun ω => hC ω (LQGMetric.cmTest g); P] = _ at hc
  exact hc.trans ((Section6.wholePlaneGFFCov_pairing_eq_logCov _ _).trans
    (LQGMetric.logCov_cmTest_right g φ.1))

/-- The Dirichlet pairings of the whole-plane GFF have covariance the Dirichlet inner product
`(f, g)_∇ = (2π)⁻¹ ∫ ∇f · ∇g`, the gradient written in the orthonormal basis `1, i` of `ℂ`. -/
theorem IsWholePlaneGFF.covariance_dirichletPairing (hh : IsWholePlaneGFF P hC hcirc)
    (f g : LQGMetric.TestC) :
    cov[fun ω => hC ω (LQGMetric.cmTest f), fun ω => hC ω (LQGMetric.cmTest g); P] =
      (2 * π)⁻¹ * ∫ z, (fderiv ℝ (f : ℂ → ℝ) z 1 * fderiv ℝ (g : ℂ → ℝ) z 1 +
        fderiv ℝ (f : ℂ → ℝ) z Complex.I * fderiv ℝ (g : ℂ → ℝ) z Complex.I) := by
  refine (hh.covariance_pairing_dirichletPairing g (LQGMetric.cmTest0 f)).trans ?_
  have hibp := QuantumZipper.K3.integral_gradInner_eq_neg_integral_mul_laplacian
    ((LQGMetric.contDiff_two_testC g).of_le (by norm_num)) (LQGMetric.contDiff_two_testC f)
    f.hasCompactSupport
  calc ∫ x, (LQGMetric.cmTest0 f).1 x * g x
      = -(2 * π)⁻¹ * ∫ x, g x * Δ (⇑f) x := by
        rw [← integral_const_mul]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        change LQGMetric.cmTest f x * g x = _
        rw [LQGMetric.cmTest_apply]
        ring
    _ = (2 * π)⁻¹ * ∫ z, QuantumZipper.K3.gradInner g f z := by
        rw [hibp]
        ring
    _ = _ := by
        congr 1
        refine integral_congr_ae (ae_of_all _ fun z => ?_)
        simp only [QuantumZipper.K3.gradInner]
        ring

/-- The variance of the Dirichlet pairing `(h, g)_∇` is the Dirichlet energy
`(g, g)_∇ = (2π)⁻¹ ∫ |∇g|²`. -/
theorem IsWholePlaneGFF.variance_dirichletPairing (hh : IsWholePlaneGFF P hC hcirc)
    (g : LQGMetric.TestC) :
    Var[fun ω => hC ω (LQGMetric.cmTest g); P] = LQGMetric.gradEnergy g := by
  have hm : AEMeasurable (fun ω => hC ω (LQGMetric.cmTest g)) P :=
    (hh.measurable_pairing _ (Section6.isTestFunction_of_testC (LQGMetric.cmTest g))).aemeasurable
  rw [← covariance_self hm]
  refine (hh.covariance_pairing_dirichletPairing g (LQGMetric.cmTest0 g)).trans ?_
  rw [← LQGMetric.logCov_cmTest_right]
  exact LQGMetric.logCov_cmTest_cmTest g

/-- The mean-zero pairings of a whole-plane GFF form a centered Gaussian process. -/
private theorem IsWholePlaneGFF.pairingProcess (hh : IsWholePlaneGFF P hC hcirc) :
    IsGaussianProcess (fun (φ : LQGMetric.TestC0) ω => hC ω φ.1) P ∧
      (∀ φ : LQGMetric.TestC0, Measurable fun ω => hC ω φ.1) ∧
      ∀ φ : LQGMetric.TestC0, P[fun ω => hC ω φ.1] = 0 :=
  ⟨hh.isGaussianProcess.comp_right fun φ : LQGMetric.TestC0 =>
      (⟨.pairing φ.1, Section6.isTestFunction_of_testC φ.1⟩ : GFFObservable.Admissible),
    fun φ => hh.measurable_pairing φ.1 (Section6.isTestFunction_of_testC φ.1),
    fun φ => hh.integral_eq_zero (.pairing φ.1) (Section6.isTestFunction_of_testC φ.1)⟩

/-- The normalization constant: `e^{(h, g)_∇}` is integrable and
`E e^{(h, g)_∇} = e^{(g, g)_∇ / 2}`. -/
theorem IsWholePlaneGFF.integral_exp_dirichletPairing (hh : IsWholePlaneGFF P hC hcirc)
    (g : LQGMetric.TestC) :
    Integrable (fun ω => Real.exp (hC ω (LQGMetric.cmTest g))) P ∧
      ∫ ω, Real.exp (hC ω (LQGMetric.cmTest g)) ∂P = Real.exp (LQGMetric.gradEnergy g / 2) := by
  obtain ⟨hgauss, -, hcent⟩ := hh.pairingProcess
  obtain ⟨hi, he⟩ := QuantumZipper.CameronMartin.gauss_exp hgauss hcent
    (hgauss.hasGaussianLaw_eval (LQGMetric.cmTest0 g)) (hcent (LQGMetric.cmTest0 g))
  refine ⟨hi, he.trans ?_⟩
  change Real.exp (Var[fun ω => hC ω (LQGMetric.cmTest g); P] / 2) = _
  rw [hh.variance_dirichletPairing g]

private theorem measurable_dirichletDensity (g : LQGMetric.TestC) (c : ℝ) :
    Measurable fun F : LQGMetric.TestC0 → ℝ =>
      ENNReal.ofReal (Real.exp (F (LQGMetric.cmTest0 g)) / c) :=
  ENNReal.measurable_ofReal.comp
    ((Real.measurable_exp.comp (measurable_pi_apply (LQGMetric.cmTest0 g))).div_const c)

private theorem IsWholePlaneGFF.measurable_smoothShift (hh : IsWholePlaneGFF P hC hcirc)
    (g : LQGMetric.TestC) :
    Measurable fun ω (φ : LQGMetric.TestC0) => hC ω φ.1 + ∫ x, φ.1 x * g x :=
  measurable_pi_iff.mpr fun φ =>
    (hh.measurable_pairing φ.1 (Section6.isTestFunction_of_testC φ.1)).add_const _

/-- **Smooth-shift density of the whole-plane GFF.** On the mean-zero pairings, the law of
`h + g` has density `Z⁻¹ e^{(h, g)_∇}` with respect to the law of `h`, where `Z = e^{(g, g)_∇ / 2}`
and `(h, g)_∇` is the coordinate of index `-Δg/(2π)`. -/
theorem IsWholePlaneGFF.map_smooth_shift_eq_withDensity (hh : IsWholePlaneGFF P hC hcirc)
    (g : LQGMetric.TestC) :
    P.map (fun ω (φ : LQGMetric.TestC0) => hC ω φ.1 + ∫ x, φ.1 x * g x) =
      (P.map (Section6.pairingProc hC)).withDensity fun F =>
        ENNReal.ofReal
          (Real.exp (F (LQGMetric.cmTest0 g)) / Real.exp (LQGMetric.gradEnergy g / 2)) := by
  obtain ⟨hgauss, hmeas, hcent⟩ := hh.pairingProcess
  set X : LQGMetric.TestC0 → Ω → ℝ := fun φ ω => hC ω φ.1 with hX
  have hshift (φ : LQGMetric.TestC0) :
      QuantumZipper.CameronMartin.covShift X P (Finsupp.single (LQGMetric.cmTest0 g) 1) φ =
        ∫ x, φ.1 x * g x := by
    simp only [QuantumZipper.CameronMartin.covShift, QuantumZipper.CameronMartin.covK,
      Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same, one_mul]
    exact hh.covariance_pairing_dirichletPairing g φ
  have hnorm :
      QuantumZipper.CameronMartin.covNorm X P (Finsupp.single (LQGMetric.cmTest0 g) 1) =
        LQGMetric.gradEnergy g := by
    simp only [QuantumZipper.CameronMartin.covNorm,
      Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same, one_mul]
    rw [hshift, ← LQGMetric.logCov_cmTest_right]
    exact LQGMetric.logCov_cmTest_cmTest g
  have hdens (ω : Ω) :
      QuantumZipper.CameronMartin.tiltDensity X P (Finsupp.single (LQGMetric.cmTest0 g) 1) ω =
        Real.exp (Section6.pairingProc hC ω (LQGMetric.cmTest0 g)) /
          Real.exp (LQGMetric.gradEnergy g / 2) := by
    rw [QuantumZipper.CameronMartin.tiltDensity, hnorm, Real.exp_sub]
    simp only [QuantumZipper.CameronMartin.comb, Finsupp.support_single _ one_ne_zero,
      Finset.sum_singleton, Finsupp.single_eq_same, one_mul]
    rfl
  have hpath : Measurable (Section6.pairingProc hC) := Section6.measurable_pairingProc hh
  have hmap := QuantumZipper.CameronMartin.map_tiltMeasure_path hgauss hmeas hcent
    (Finsupp.single (LQGMetric.cmTest0 g) 1)
  have hfun : (fun ω (φ : LQGMetric.TestC0) => hC ω φ.1 + ∫ x, φ.1 x * g x) =
      fun ω j => X j ω +
        QuantumZipper.CameronMartin.covShift X P (Finsupp.single (LQGMetric.cmTest0 g) 1) j := by
    funext ω j
    rw [hshift]
  rw [hfun, ← hmap]
  change Measure.map (Section6.pairingProc hC) _ = _
  ext s hs
  rw [Measure.map_apply hpath hs, QuantumZipper.CameronMartin.tiltMeasure,
    withDensity_apply _ (hpath hs), withDensity_apply _ hs,
    setLIntegral_map hs (measurable_dirichletDensity g _) hpath]
  refine setLIntegral_congr_fun (hpath hs) fun ω _ => ?_
  rw [hdens]
  rfl

/-- The Radon–Nikodym derivative of the law of `h + g` with respect to the law of `h`, on the
mean-zero pairings, is `Z⁻¹ e^{(h, g)_∇}` with `Z = e^{(g, g)_∇ / 2}`. -/
theorem IsWholePlaneGFF.rnDeriv_map_smooth_shift (hh : IsWholePlaneGFF P hC hcirc)
    (g : LQGMetric.TestC) :
    (P.map (fun ω (φ : LQGMetric.TestC0) => hC ω φ.1 + ∫ x, φ.1 x * g x)).rnDeriv
        (P.map (Section6.pairingProc hC)) =ᵐ[P.map (Section6.pairingProc hC)] fun F =>
      ENNReal.ofReal
        (Real.exp (F (LQGMetric.cmTest0 g)) / Real.exp (LQGMetric.gradEnergy g / 2)) := by
  have := hh.isProbabilityMeasure
  rw [hh.map_smooth_shift_eq_withDensity g]
  exact Measure.rnDeriv_withDensity _ (measurable_dirichletDensity g _)

/-- **Miller–Sheffield, Imaginary Geometry IV, Proposition 2.9, first sentence**, for the
whole-plane GFF modulo additive constants and a smooth compactly supported shift `g`. The
normalization constant is `Z = E e^{(h, g)_∇} = e^{(g, g)_∇ / 2} > 0`; for every event `A` of the
mean-zero pairings, `P(h + g ∈ A) = E[Z⁻¹ e^{(h, g)_∇} ; h ∈ A]`, and `h + g ∈ A` is null exactly
when `h ∈ A` is null. -/
theorem IsWholePlaneGFF.smooth_shift_density (hh : IsWholePlaneGFF P hC hcirc)
    (g : LQGMetric.TestC) :
    ∃ Z : ℝ, Z = ∫ ω, Real.exp (hC ω (LQGMetric.cmTest g)) ∂P ∧
      Z = Real.exp (LQGMetric.gradEnergy g / 2) ∧ 0 < Z ∧
      ∀ A : Set (LQGMetric.TestC0 → ℝ), MeasurableSet A →
        P ((fun ω (φ : LQGMetric.TestC0) => hC ω φ.1 + ∫ x, φ.1 x * g x) ⁻¹' A) =
            ∫⁻ ω in Section6.pairingProc hC ⁻¹' A,
              ENNReal.ofReal (Real.exp (hC ω (LQGMetric.cmTest g)) / Z) ∂P ∧
          (P ((fun ω (φ : LQGMetric.TestC0) => hC ω φ.1 + ∫ x, φ.1 x * g x) ⁻¹' A) = 0 ↔
            P (Section6.pairingProc hC ⁻¹' A) = 0) := by
  have hpath : Measurable (Section6.pairingProc hC) := Section6.measurable_pairingProc hh
  have hs := hh.measurable_smoothShift g
  refine ⟨_, (hh.integral_exp_dirichletPairing g).2.symm, rfl, Real.exp_pos _,
    fun A hA => ⟨?_, ?_⟩⟩
  · rw [← Measure.map_apply hs hA, hh.map_smooth_shift_eq_withDensity g, withDensity_apply _ hA,
      setLIntegral_map hA (measurable_dirichletDensity g _) hpath]
    rfl
  · rw [← Measure.map_apply hs hA, ← Measure.map_apply hpath hA]
    have hac := hh.smooth_shift_pairing_laws g
    exact ⟨fun h => hac.2 h, fun h => hac.1 h⟩

/-- `IsWholePlaneGFF.smooth_shift_density` for a test function `g` in the sense of
`IsTestFunction`, with `(h, g)_∇ = (h, -Δg/(2π))` and `(g, g)_∇ = (2π)⁻¹ ∫ |∇g|²` written out. -/
theorem IsWholePlaneGFF.smooth_shift_density_of_isTestFunction
    (hh : IsWholePlaneGFF P hC hcirc) {g : ℂ → ℝ} (hg : IsTestFunction univ g) :
    ∃ Z : ℝ, Z = ∫ ω, Real.exp (hC ω fun z => -(2 * π)⁻¹ * Δ g z) ∂P ∧
      Z = Real.exp ((2 * π)⁻¹ * (∫ z, ‖fderiv ℝ g z‖ ^ 2) / 2) ∧ 0 < Z ∧
      ∀ A : Set (LQGMetric.TestC0 → ℝ), MeasurableSet A →
        P ((fun ω (φ : LQGMetric.TestC0) => hC ω φ.1 + ∫ x, φ.1 x * g x) ⁻¹' A) =
            ∫⁻ ω in Section6.pairingProc hC ⁻¹' A,
              ENNReal.ofReal (Real.exp (hC ω fun z => -(2 * π)⁻¹ * Δ g z) / Z) ∂P ∧
          (P ((fun ω (φ : LQGMetric.TestC0) => hC ω φ.1 + ∫ x, φ.1 x * g x) ⁻¹' A) = 0 ↔
            P (Section6.pairingProc hC ⁻¹' A) = 0) :=
  hh.smooth_shift_density ⟨g, hg.1, hg.2.1, subset_univ _⟩

end HarmonicBalls
