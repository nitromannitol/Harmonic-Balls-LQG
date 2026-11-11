import HarmonicBalls.Steps.Sec11.GaussianProcessLaw
import HarmonicBalls.FirstPass.Frozen.S11aj

/-!
# The joint law of the whole-plane GFF and its circle-average process

`IsWholePlaneGFF P hC hcirc` constrains `hC ω φ` only for test functions `φ` and `hcirc ω r z` only for `r > 0`
(`measurable_pairing`, `measurable_circle`). The full product map `ω ↦ (hC ω, hcirc ω)` into the Pi σ-algebras
of `(ℂ → ℝ) → ℝ` and `ℝ → ℂ → ℝ` is therefore not known to be measurable, and `Measure.map` of a
non-AE-measurable map is `0`. The joint law is stated on the constrained index sets instead:

* `jointSample hC hcirc ω = (φ ↦ hC ω φ on test functions, (r, z) ↦ hcirc ω r z on r > 0)`;
* the observable family `obsFamily hC hcirc ω o = o.eval (hC ω) (hcirc ω)` over `GFFObservable.Admissible`,
  the index set of `IsGaussianProcess` in `IsWholePlaneGFF`.

The law of a centered Gaussian family with covariance `wholePlaneGFFCov` is fixed by the definition, so the
two laws agree (`isWholePlaneGFF_observableLaw_map_eq`), and the pair law follows by `Measure.map_map` through the
measurable coordinate map `pairOfFamily` (`isWholePlaneGFF_jointLaw_map_eq`). The Cameron-Martin corollary is
conditional on the named input `CameronMartinGFFReweighting` (`FirstPass/Frozen/S11aj.lean:33`).
-/

namespace HarmonicBalls.GFFJointLaw

open MeasureTheory ProbabilityTheory

universe u v

/-- The observable family of a sample `(hC, hcirc)` indexed by the admissible observables
(pairings with test functions and circle averages with positive radius). -/
noncomputable def obsFamily {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) :
    GFFObservable.Admissible → ℝ :=
  fun o => o.1.eval (hC ω) (hcirc ω)

/-- The joint sample `(hC ω, hcirc ω)` restricted to the constrained index sets: test functions and positive radii. -/
noncomputable def jointSample {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) :
    ({φ : ℂ → ℝ // IsTestFunction Set.univ φ} → ℝ) × ({p : ℝ × ℂ // 0 < p.1} → ℝ) :=
  (fun φ => hC ω φ.1, fun p => hcirc ω p.1.1 p.1.2)

/-- The coordinate map from an observable family to the joint sample on the constrained index sets. -/
noncomputable def pairOfFamily (g : GFFObservable.Admissible → ℝ) :
    ({φ : ℂ → ℝ // IsTestFunction Set.univ φ} → ℝ) × ({p : ℝ × ℂ // 0 < p.1} → ℝ) :=
  (fun φ => g ⟨GFFObservable.pairing φ.1, φ.2⟩, fun p => g ⟨GFFObservable.circle p.1.1 p.1.2, p.2⟩)

theorem measurable_pairOfFamily :
    Measurable (pairOfFamily : (GFFObservable.Admissible → ℝ) →
      ({φ : ℂ → ℝ // IsTestFunction Set.univ φ} → ℝ) × ({p : ℝ × ℂ // 0 < p.1} → ℝ)) := by
  unfold pairOfFamily
  exact Measurable.prodMk (Measurable.of_eval fun φ => measurable_pi_apply _)
    (Measurable.of_eval fun p => measurable_pi_apply _)

theorem jointSample_eq_pairOfFamily {Ω : Type*} (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    jointSample hC hcirc = pairOfFamily ∘ obsFamily hC hcirc := by
  funext ω
  rfl

/-- Each admissible observable of a whole-plane GFF is a random variable. -/
theorem measurable_obsFamily {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hP : IsWholePlaneGFF P hC hcirc) (o : GFFObservable.Admissible) :
    Measurable fun ω => obsFamily hC hcirc ω o := by
  obtain ⟨o, ho⟩ := o
  cases o with
  | pairing φ => exact hP.measurable_pairing φ ho
  | circle r z => exact hP.measurable_circle r z ho

theorem measurable_obsFamily_map {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
    {hcirc : Ω → ℝ → ℂ → ℝ} (hP : IsWholePlaneGFF P hC hcirc) :
    Measurable (obsFamily hC hcirc) :=
  Measurable.of_eval fun o => measurable_obsFamily hP o

/-- **Law of the observable family.** Two whole-plane GFFs (with their circle-average processes) have the same law
as a family indexed by the admissible observables: both are centered Gaussian families with covariance
`wholePlaneGFFCov` (`IsWholePlaneGFF`, fields `integral_eq_zero` and `covariance_eq`). -/
theorem isWholePlaneGFF_observableLaw_map_eq {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ)
    (hP : IsWholePlaneGFF P hC hcirc) (hQ : IsWholePlaneGFF Q hC' hcirc') :
    P.map (obsFamily hC hcirc) = Q.map (obsFamily hC' hcirc') :=
  gaussian_process_map_eq_of_mean_covariance P Q
    (fun (o : GFFObservable.Admissible) (ω : Ω) => o.1.eval (hC ω) (hcirc ω))
    (fun (o : GFFObservable.Admissible) (ω : Ω') => o.1.eval (hC' ω) (hcirc' ω))
    hP.isGaussianProcess hQ.isGaussianProcess
    (measurable_obsFamily hP) (measurable_obsFamily hQ)
    (fun (t : GFFObservable.Admissible) =>
      (hP.integral_eq_zero t.1 t.2).trans (hQ.integral_eq_zero t.1 t.2).symm)
    (fun (s t : GFFObservable.Admissible) =>
      (hP.covariance_eq s.1 t.1 s.2 t.2).trans (hQ.covariance_eq s.1 t.1 s.2 t.2).symm)

/-- **Joint law of the GFF and its circle-average process** (pairings with test functions and circle averages with
positive radius, on the Pi σ-algebras of these index sets). See the module docstring for why the index sets are
restricted. -/
theorem isWholePlaneGFF_jointLaw_map_eq {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (P : Measure Ω) (Q : Measure Ω') [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hC' : Ω' → (ℂ → ℝ) → ℝ) (hcirc' : Ω' → ℝ → ℂ → ℝ)
    (hP : IsWholePlaneGFF P hC hcirc) (hQ : IsWholePlaneGFF Q hC' hcirc') :
    P.map (jointSample hC hcirc) = Q.map (jointSample hC' hcirc') := by
  rw [jointSample_eq_pairOfFamily, jointSample_eq_pairOfFamily,
    ← Measure.map_map measurable_pairOfFamily (measurable_obsFamily_map hP),
    ← Measure.map_map measurable_pairOfFamily (measurable_obsFamily_map hQ),
    isWholePlaneGFF_observableLaw_map_eq P Q hC hcirc hC' hcirc' hP hQ]

/-- **Cameron-Martin profile law**. Conditional on the
named input `CameronMartinGFFReweighting` (`FirstPass/Frozen/S11aj.lean:33`): for the Cameron-Martin measure `P'`
(equivalent to `P`) under which `(hC + f, hcirc + Av f)` is a whole-plane GFF, the law of the shifted profile under
`P'` equals the law of `(hC, hcirc)` under `P`. -/
theorem cameronMartin_profileLaw_map_eq (hCMRew : HarmonicBalls.S11aj.CameronMartinGFFReweighting.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hP : IsWholePlaneGFF P hC hcirc)
    (f : ℂ → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hf0 : Real.circleAverage f 0 1 = 0) :
    ∃ P' : Measure Ω, P' ≪ P ∧ P ≪ P' ∧
      P'.map (fun ω => (fun φ : {φ : ℂ → ℝ // IsTestFunction Set.univ φ} => addFunPairing (hC ω) f φ.1,
        fun p : {p : ℝ × ℂ // 0 < p.1} => hcirc ω p.1.1 p.1.2 + Real.circleAverage f p.1.2 p.1.1))
        = P.map (jointSample hC hcirc) := by
  obtain ⟨P', hac1, hac2, hGFF'⟩ := hCMRew Ω P hC hcirc hP f hf hfc hf0
  have : IsProbabilityMeasure P' := hGFF'.isGaussianProcess.isProbabilityMeasure
  exact ⟨P', hac1, hac2, isWholePlaneGFF_jointLaw_map_eq P' P (fun ω => addFunPairing (hC ω) f)
    (fun ω r z => hcirc ω r z + Real.circleAverage f z r) hC hcirc hGFF' hP⟩

end HarmonicBalls.GFFJointLaw
