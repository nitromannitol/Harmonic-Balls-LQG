import HarmonicBalls.FirstPass.S11i.MixingCanonical
import HarmonicBalls.FirstPass.S11i.CylinderFactor
import HarmonicBalls.FirstPass.S11i.GFFFamily

/-!
# The canonical law of a whole-plane GFF does not depend on the model (fp-S11i-11-13)

Two whole-plane GFF models (possibly on different probability spaces) have the same canonical law
`P.map (ω ↦ (φ ↦ hC ω φ)_{φ mean-zero test})`: the finite-dimensional marginals are centred Gaussian with the same
covariance `wholePlaneGFFCov` (`IsWholePlaneGFF.covariance_eq`, `cov_pairing_eq`), and a centred Gaussian law is
determined by its covariance. Consequently the probability `P{alphaCanon γ hC ∈ E}` of a fixed canonical event is a
constant of the GFF, which is what lets the constant `δ` of Lemma 11.13 be chosen before the probability space.

`map_eq_of_gaussian_cov` (`MixingCanonical.lean:31`) is stated on one probability space; `map_eq_of_gaussian_cov_two` is
the same proof (charFun uniqueness, `Measure.ext_of_charFun`) with the two vectors on two spaces.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ProbabilityTheory

/-- Two-space version of `map_eq_of_gaussian_cov` (`MixingCanonical.lean:31`): centred jointly Gaussian vectors with
equal covariance have equal laws, even when they live on two different probability spaces. -/
theorem map_eq_of_gaussian_cov_two {ι : Type*} [Fintype ι] {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {Y : ι → Ω → ℝ} {Y' : ι → Ω' → ℝ}
    (hm : ∀ j, Measurable (Y j)) (hm' : ∀ j, Measurable (Y' j))
    (hY : HasGaussianLaw (fun ω (j : ι) => Y j ω) P) (hY' : HasGaussianLaw (fun ω (j : ι) => Y' j ω) P')
    (h0 : ∀ j, ∫ ω, Y j ω ∂P = 0) (h0' : ∀ j, ∫ ω, Y' j ω ∂P' = 0)
    (hcov : ∀ j l, cov[Y j, Y l; P] = cov[Y' j, Y' l; P']) :
    P.map (fun ω (j : ι) => Y j ω) = P'.map (fun ω (j : ι) => Y' j ω) := by
  have hV : Measurable (fun ω => (WithLp.toLp 2 (fun j => Y j ω) : EuclideanSpace ℝ ι)) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 hm)
  have hV' : Measurable (fun ω => (WithLp.toLp 2 (fun j => Y' j ω) : EuclideanSpace ℝ ι)) :=
    (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 hm')
  have hchar : charFun (P.map (fun ω => (WithLp.toLp 2 (fun j => Y j ω) : EuclideanSpace ℝ ι))) =
      charFun (P'.map (fun ω => (WithLp.toLp 2 (fun j => Y' j ω) : EuclideanSpace ℝ ι))) := by
    funext t
    rw [charFun_apply, charFun_apply,
      integral_map hV.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop)),
      integral_map hV'.aemeasurable (Continuous.aestronglyMeasurable (by fun_prop))]
    simp only [inner_toLp_fun]
    rw [integral_exp_linComb_eq hY h0 (WithLp.ofLp t), integral_exp_linComb_eq hY' h0' (WithLp.ofLp t)]
    simp only [hcov]
  have hmeas := Measure.ext_of_charFun hchar
  calc P.map (fun ω (j : ι) => Y j ω)
      = ((P.map (fun ω => (WithLp.toLp 2 (fun j => Y j ω) : EuclideanSpace ℝ ι))).map
          (WithLp.ofLp)) := by
        rw [Measure.map_map (WithLp.measurable_ofLp 2 _) hV]; rfl
    _ = ((P'.map (fun ω => (WithLp.toLp 2 (fun j => Y' j ω) : EuclideanSpace ℝ ι))).map
          (WithLp.ofLp)) := by rw [hmeas]
    _ = P'.map (fun ω (j : ι) => Y' j ω) := by
        rw [Measure.map_map (WithLp.measurable_ofLp 2 _) hV']; rfl

/-- The canonical law of a whole-plane GFF is the same for all models: if `(P, hC, hcirc)` and `(P', hC', hcirc')` are
whole-plane GFFs, then `P.map (ω ↦ (φ ↦ hC ω φ))` and `P'.map (ω ↦ (φ ↦ hC' ω φ))` agree on the mean-zero test
functions. -/
theorem canonicalLaw_eq_of_isWholePlaneGFF {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hh' : IsWholePlaneGFF P' hC' hcirc') :
    P.map (fun ω (i : CanonIdx) => hC ω i.1) = P'.map (fun ω (i : CanonIdx) => hC' ω i.1) := by
  refine MeasureTheory.ext_of_generate_finite (measurableCylinders fun _ : CanonIdx => ℝ)
    generateFrom_measurableCylinders.symm isPiSystem_measurableCylinders ?_ ?_
  · intro s hs
    simp only [measurableCylinders, mem_iUnion, mem_singleton_iff, exists_prop] at hs
    obtain ⟨J, B, hB, rfl⟩ := hs
    have hY0 : Measurable (fun ω (j : J) => hC ω j.1.1) :=
      measurable_pi_iff.2 fun j => hh.measurable_pairing _ j.1.2.1
    have hY0' : Measurable (fun ω (j : J) => hC' ω j.1.1) :=
      measurable_pi_iff.2 fun j => hh'.measurable_pairing _ j.1.2.1
    have hJ := map_eq_of_gaussian_cov_two (ι := J) (Y := fun j ω => hC ω j.1.1)
      (Y' := fun j ω => hC' ω j.1.1)
      (fun j => hh.measurable_pairing _ j.1.2.1) (fun j => hh'.measurable_pairing _ j.1.2.1)
      (hasGaussianLaw_pairing_family hh (fun j : J => j.1.1) (fun j => j.1.2.1))
      (hasGaussianLaw_pairing_family hh' (fun j : J => j.1.1) (fun j => j.1.2.1))
      (fun j => integral_pairing_eq_zero hh j.1.2.1) (fun j => integral_pairing_eq_zero hh' j.1.2.1)
      (fun j l => (cov_pairing_eq hh j.1.2.1 l.1.2.1).trans (cov_pairing_eq hh' j.1.2.1 l.1.2.1).symm)
    have hm1 : Measurable (fun ω (i : CanonIdx) => hC ω i.1) := measurable_canonical hh
    have hm1' : Measurable (fun ω (i : CanonIdx) => hC' ω i.1) := measurable_canonical hh'
    have hg : Measurable (fun (f : CanonIdx → ℝ) (i : J) => f i.1) :=
      measurable_pi_iff.2 fun i => measurable_pi_apply i.1
    have hcyl : MeasurableSet (cylinder J B) := hg hB
    rw [Measure.map_apply hm1 hcyl, Measure.map_apply hm1' hcyl]
    show P ((fun ω (j : J) => hC ω j.1.1) ⁻¹' B) = P' ((fun ω (j : J) => hC' ω j.1.1) ⁻¹' B)
    rw [← Measure.map_apply hY0 hB, ← Measure.map_apply hY0' hB, hJ]
  · simp

end HarmonicBalls
