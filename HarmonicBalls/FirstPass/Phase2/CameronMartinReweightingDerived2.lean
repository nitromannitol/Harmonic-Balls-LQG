import HarmonicBalls.FirstPass.Phase2.CameronMartinReweightingDerived

/-!
# Derivation of the frozen Cameron-Martin reweighting input, part 2

Second part of `CameronMartinReweightingDerived.lean`: the finite-dimensional law of the tilted family
(`law_shift`), the assembly of `IsWholePlaneGFF` under the tilt, and the theorem
`cameronMartinGFFReweighting_derived : CameronMartinGFFReweighting.{u}` (`FirstPass/Frozen/S11aj.lean:33`).
-/

namespace HarmonicBalls.S11aj

open MeasureTheory ProbabilityTheory Metric Set Laplacian
open scoped ENNReal ContDiff

universe u

/-! ### Finite-dimensional law of the tilted Gaussian family -/

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem clm_apply_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι] (L : (ι → ℝ) →L[ℝ] ℝ) (z : ι → ℝ) :
    L z = ∑ i, z i * L (fun j => if i = j then 1 else 0) := by
  conv_lhs => rw [pi_eq_sum_univ z]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, smul_eq_mul]

/-- The shifted family and the tilt: for every continuous linear functional `L` on the coordinates of a finite
family `I`, the characteristic functional of the tilted shifted family equals that of the original family. -/
theorem law_shift_charFun {T : Type*} {Y : T → Ω → ℝ} (hY : IsGaussianProcess Y P)
    (hYm : ∀ t, Measurable (Y t)) (hcen : ∀ t, P[Y t] = 0) (q : T) (a : T → ℝ)
    (hcov : ∀ t, cov[Y t, Y q; P] = a t) (I : Finset T) (L : StrongDual ℝ (I → ℝ)) :
    ∫ x, Complex.exp (L (fun t : I => Y t x + a t) * Complex.I)
        ∂(P.withDensity (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2))))
      = ∫ x, Complex.exp (L (fun t : I => Y t x) * Complex.I) ∂P := by
  classical
  have hXG : HasGaussianLaw (Y q) P := hY.hasGaussianLaw_eval q
  have hXm : MemLp (Y q) 2 P := hXG.memLp_two
  have hv0 : 0 ≤ Var[Y q; P] := variance_nonneg _ _
  -- Gaussian family on J = insert q I, and the two linear functionals
  set J : Finset T := insert q I with hJ
  have hZJ : HasGaussianLaw (fun x (t : J) => Y t x) P := hY.hasGaussianLaw J
  have hqJ : q ∈ J := Finset.mem_insert_self q I
  let ℓ₁ : (J → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj ⟨q, hqJ⟩
  let R : (J → ℝ) →L[ℝ] (I → ℝ) :=
    ContinuousLinearMap.pi (fun t : I => ContinuousLinearMap.proj ⟨(t : T), Finset.mem_insert_of_mem t.2⟩)
  let ℓ₂ : (J → ℝ) →L[ℝ] ℝ := L.comp R
  have hpair : HasGaussianLaw (fun x => (Y q x, L (fun t : I => Y t x))) P := hZJ.map (ℓ₁.prod ℓ₂)
  have hW : HasGaussianLaw (fun x => L (fun t : I => Y t x)) P := hpair.map (ContinuousLinearMap.snd ℝ ℝ ℝ)
  -- coefficients of the functional
  set c : I → ℝ := fun i => L (fun j => if i = j then 1 else 0) with hc_def
  have hαsum : L (fun t : I => a t) = ∑ i : I, c i * a i := by
    rw [clm_apply_eq_sum L]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hWsum : (fun x => L (fun t : I => Y t x)) = ∑ i : I, c i • Y i := by
    funext x
    rw [clm_apply_eq_sum L, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.smul_apply, smul_eq_mul, mul_comm]
  have hMem : ∀ i : I, MemLp (Y i) 2 P := fun i => (hY.hasGaussianLaw_eval (i : T)).memLp_two
  have hW0 : P[fun x => L (fun t : I => Y t x)] = 0 := by
    rw [hWsum]
    show ∫ x, (∑ i : I, c i • Y i) x ∂P = 0
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_finsetSum _ (fun i _ => ((hMem i).integrable one_le_two).const_mul (c i))]
    simp [integral_const_mul, hcen]
  have hcovWX : cov[fun x => L (fun t : I => Y t x), Y q; P] = L (fun t : I => a t) := by
    rw [hWsum, covariance_sum_left (X := fun i : I => c i • Y i) (fun i => (hMem i).const_smul (c i)) hXm]
    simp only [covariance_smul_left, hcov]
    rw [hαsum]
  have hXlaw : HasLaw (Y q) (gaussianReal 0 (Var[Y q; P]).toNNReal) P := by
    refine ⟨(hYm q).aemeasurable, ?_⟩
    have h := (hXG).map_eq_gaussianReal
    rwa [hcen q] at h
  have hWlaw : HasLaw (fun x => L (fun t : I => Y t x))
      (gaussianReal 0 (Var[fun x => L (fun t : I => Y t x); P]).toNNReal) P := by
    refine ⟨hW.aemeasurable, ?_⟩
    have h := hW.map_eq_gaussianReal
    rwa [hW0] at h
  have hDmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hYm q).neg.sub_const _))
  rw [integral_withDensity_eq_integral_toReal_smul₀ hDmeas.aemeasurable
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top))]
  have hlhs : ∀ x : Ω, (ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2))).toReal
      • Complex.exp (L (fun t : I => Y t x + a t) * Complex.I)
      = Complex.exp (L (fun t : I => a t) * Complex.I)
        * (((Real.exp (-Y q x - Var[Y q; P] / 2) : ℝ) : ℂ)
          * Complex.exp (Complex.I * ((L (fun t : I => Y t x) : ℝ) : ℂ))) := by
    intro x
    have e : (fun t : I => Y t x + a t) = (fun t : I => Y t x) + (fun t : I => a t) := rfl
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul, e, map_add, Complex.ofReal_add,
      add_mul, Complex.exp_add, mul_comm (((L (fun t : I => Y t x)) : ℝ) : ℂ) Complex.I, Complex.ofReal_exp]
    ring
  rw [integral_congr_ae (ae_of_all _ hlhs), integral_const_mul]
  rw [tilt_core hpair (hcen q) hW0, hcovWX]
  have hR : ∫ x, Complex.exp (L (fun t : I => Y t x) * Complex.I) ∂P
      = Complex.exp (-((Var[fun x => L (fun t : I => Y t x); P] : ℝ) : ℂ) / 2) := by
    have h1 : ∫ x, Complex.exp (L (fun t : I => Y t x) * Complex.I) ∂P
        = charFun (P.map (fun x => L (fun t : I => Y t x))) 1 := by
      rw [charFun_apply_real, integral_map hW.aemeasurable (by fun_prop)]
      apply integral_congr_ae
      filter_upwards with x
      push_cast
      ring_nf
    rw [h1, hWlaw.map_eq, charFun_gaussianReal]
    congr 1
    simp [Real.coe_toNNReal _ (variance_nonneg _ _)]
    ring
  rw [hR, ← Complex.exp_add]
  congr 1
  ring

/-- **Shift of the finite-dimensional law (Cameron-Martin tilt).** Under the tilt `dP'/dP = exp(-X - v/2)`, `X = Y q`,
the family `Y + a` (with `a t = Cov(Y t, X)`) has the same finite-dimensional law as `Y` under `P`. -/
theorem law_shift {T : Type*} {Y : T → Ω → ℝ} (hY : IsGaussianProcess Y P)
    (hYm : ∀ t, Measurable (Y t)) (hcen : ∀ t, P[Y t] = 0) (q : T) (a : T → ℝ)
    (hcov : ∀ t, cov[Y t, Y q; P] = a t) (I : Finset T) :
    (P.withDensity (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2)))).map
        (fun x (t : I) => Y t x + a t)
      = P.map (fun x (t : I) => Y t x) := by
  have hint : Integrable (fun x => Real.exp (-Y q x)) P := by
    have hXlaw : HasLaw (Y q) (gaussianReal 0 (Var[Y q; P]).toNNReal) P := by
      refine ⟨(hYm q).aemeasurable, ?_⟩
      have h := (hY.hasGaussianLaw_eval q).map_eq_gaussianReal
      rwa [hcen q] at h
    have h1 : Integrable (fun y : ℝ => Real.exp (-1 * y)) (gaussianReal 0 (Var[Y q; P]).toNNReal) :=
      integrable_exp_mul_gaussianReal (-1)
    have h2 : Integrable (fun y : ℝ => Real.exp (-y)) (gaussianReal 0 (Var[Y q; P]).toNNReal) := by
      simpa using h1
    have h3 : Integrable (fun y : ℝ => Real.exp (-y)) (P.map (Y q)) := by
      rw [hXlaw.map_eq]; exact h2
    exact (integrable_map_measure (Real.measurable_exp.comp measurable_neg).aestronglyMeasurable
      (hYm q).aemeasurable).1 h3
  have hDint : Integrable (fun x => Real.exp (-Y q x - Var[Y q; P] / 2)) P := by
    have e : (fun x => Real.exp (-Y q x - Var[Y q; P] / 2))
        = fun x => Real.exp (-Y q x) * Real.exp (-(Var[Y q; P] / 2)) := by
      funext x
      rw [← Real.exp_add]
      ring_nf
    rw [e]
    exact hint.mul_const _
  have : IsFiniteMeasure (P.withDensity (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2)))) :=
    isFiniteMeasure_withDensity_ofReal hDint.hasFiniteIntegral
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_apply, charFunDual_apply]
  have hZ' : Measurable (fun x (t : I) => Y t x + a t) :=
    Measurable.of_eval (fun t => (hYm t).add_const _)
  have hZ : Measurable (fun x (t : I) => Y t x) := Measurable.of_eval (fun t => hYm t)
  have hcont : Continuous (fun z : I → ℝ => Complex.exp (L z * Complex.I)) := by fun_prop
  rw [integral_map hZ'.aemeasurable hcont.aestronglyMeasurable,
    integral_map hZ.aemeasurable hcont.aestronglyMeasurable]
  exact law_shift_charFun hY hYm hcen q a hcov I L

end Law


/-! ### Assembly helpers -/

section Assembly

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- Evaluation of a shifted observable: the pairing is shifted by `∫ f φ`, the circle average by `Av f`. -/
theorem eval_addFunPairing (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (f : ℂ → ℝ) (o : GFFObservable) :
    o.eval (addFunPairing hC f) (fun r z => hcirc r z + Real.circleAverage f z r)
      = o.eval hC hcirc + o.smear f := by
  cases o with
  | pairing φ =>
    simp only [GFFObservable.eval, GFFObservable.smear, addFunPairing]
    congr 1
    refine integral_congr_ae (ae_of_all _ (fun x => ?_))
    ring
  | circle r z => simp [GFFObservable.eval, GFFObservable.smear]

omit [MeasurableSpace Ω] in
/-- The circle average `(r, z) ↦ Av_{∂B_r(z)} f` is continuous for continuous `f`. -/
theorem continuous_realCircleAverage {f : ℂ → ℝ} (hf : Continuous f) :
    Continuous (fun p : ℝ × ℂ => Real.circleAverage f p.2 p.1) := by
  have h : Continuous fun p : ℝ × ℂ => ∫ t in (0 : ℝ)..2 * Real.pi, f (circleMap p.2 p.1 t) := by
    refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous (f := fun p : ℝ × ℂ => fun t : ℝ => f (circleMap p.2 p.1 t)) ?_ continuous_const
    refine hf.comp ?_
    have hc : Continuous fun q : (ℝ × ℂ) × ℝ => circleMap q.1.2 q.1.1 q.2 := by
      unfold circleMap
      fun_prop
    exact hc
  have e : (fun p : ℝ × ℂ => Real.circleAverage f p.2 p.1)
      = fun p : ℝ × ℂ => (2 * Real.pi)⁻¹ * ∫ t in (0 : ℝ)..2 * Real.pi, f (circleMap p.2 p.1 t) := by
    funext p
    rw [Real.circleAverage_def, smul_eq_mul]
  rw [e]
  exact continuous_const.mul h

/-- Covariances are determined by the joint law of the two variables. -/
theorem cov_eq_of_map_eq {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {X Y : Ω → ℝ} {X' Y' : Ω' → ℝ}
    (hXY : μ.map (fun x => (X x, Y x)) = ν.map (fun x => (X' x, Y' x)))
    (hX : MemLp X 2 μ) (hY : MemLp Y 2 μ) (hX' : MemLp X' 2 ν) (hY' : MemLp Y' 2 ν) :
    cov[X, Y; μ] = cov[X', Y'; ν] := by
  have hpair : AEMeasurable (fun x => (X x, Y x)) μ :=
    hX.aestronglyMeasurable.aemeasurable.prodMk hY.aestronglyMeasurable.aemeasurable
  have hpair' : AEMeasurable (fun x => (X' x, Y' x)) ν :=
    hX'.aestronglyMeasurable.aemeasurable.prodMk hY'.aestronglyMeasurable.aemeasurable
  have hI : ∀ g : ℝ × ℝ → ℝ, Continuous g →
      ∫ x, g (X x, Y x) ∂μ = ∫ x, g (X' x, Y' x) ∂ν := by
    intro g hg
    rw [← integral_map hpair hg.aestronglyMeasurable, ← integral_map hpair' hg.aestronglyMeasurable, hXY]
  rw [covariance_eq_sub hX hY, covariance_eq_sub hX' hY']
  have e1 := hI (fun p => p.1 * p.2) (by fun_prop)
  have e2 := hI (fun p => p.1) continuous_fst
  have e3 := hI (fun p => p.2) continuous_snd
  simp only at e1 e2 e3
  simp only [Pi.mul_apply]
  rw [e1, e2, e3]

/-- The tilt `exp(-X - v/2)` of a centered Gaussian `X` with variance `v` is a probability density. -/
theorem isProbabilityMeasure_tilt {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}
    (hX : HasLaw X (gaussianReal 0 (Var[X; P]).toNNReal) P) (hv0 : 0 ≤ Var[X; P]) :
    IsProbabilityMeasure (P.withDensity (fun x => ENNReal.ofReal (Real.exp (-X x - Var[X; P] / 2)))) := by
  have hint : Integrable (fun x => Real.exp (-X x)) P := by
    have h1 : Integrable (fun y : ℝ => Real.exp (-1 * y)) (gaussianReal 0 (Var[X; P]).toNNReal) :=
      integrable_exp_mul_gaussianReal (-1)
    have h2 : Integrable (fun y : ℝ => Real.exp (-y)) (gaussianReal 0 (Var[X; P]).toNNReal) := by
      simpa using h1
    have h3 : Integrable (fun y : ℝ => Real.exp (-y)) (P.map X) := by
      rw [hX.map_eq]; exact h2
    exact (integrable_map_measure (Real.measurable_exp.comp measurable_neg).aestronglyMeasurable
      hX.aemeasurable).1 h3
  have hmgf : ∫ x, Real.exp (-X x) ∂P = Real.exp (Var[X; P] / 2) := by
    have h := mgf_gaussianReal hX (-1)
    unfold mgf at h
    simp only [neg_one_mul, zero_mul, zero_add, Real.coe_toNNReal _ hv0] at h
    rw [h]
    congr 1
    ring
  have e : (fun x => Real.exp (-X x - Var[X; P] / 2))
      = fun x => Real.exp (-X x) * Real.exp (-(Var[X; P] / 2)) := by
    funext x
    rw [← Real.exp_add]
    ring_nf
  have hmass : ∫ x, Real.exp (-X x - Var[X; P] / 2) ∂P = 1 := by
    rw [e, integral_mul_const, hmgf, ← Real.exp_add]
    simp
  have hDint : Integrable (fun x => Real.exp (-X x - Var[X; P] / 2)) P := by
    rw [e]
    exact hint.mul_const _
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hDint (ae_of_all _ (fun x => (Real.exp_pos _).le)), hmass]
  simp

end Assembly


/-! ### The derived Cameron-Martin reweighting -/

section Main

/-- **Cameron-Martin reweighting of the whole-plane GFF, derived.** For every whole-plane GFF `(P, hC, hcirc)` and
every smooth compactly supported `f` with zero unit-circle average, the measure `P' = exp(-X - Var X / 2) · P`, with
`X = hC(-(2π)⁻¹ Δ f)`, is equivalent to `P` and under `P'` the shifted pairings and circle averages form a whole-plane
GFF. This is the frozen input `CameronMartinGFFReweighting` (`FirstPass/Frozen/S11aj.lean:33`), exactly as typed. -/
theorem cameronMartinGFFReweighting_derived : CameronMartinGFFReweighting.{u} := by
  intro Ω _ P _ hC hcirc hGFF f hf hc hAv
  -- the observables as a Gaussian process indexed by the admissible observables
  let Y : GFFObservable.Admissible → Ω → ℝ := fun o x => o.1.eval (hC x) (hcirc x)
  have hYG : IsGaussianProcess Y P := hGFF.isGaussianProcess
  have hYm : ∀ o : GFFObservable.Admissible, Measurable (Y o) := by
    rintro ⟨o, ho⟩
    cases o with
    | pairing φ => exact hGFF.measurable_pairing φ ho
    | circle r z => exact hGFF.measurable_circle r z ho
  have hcen : ∀ o : GFFObservable.Admissible, P[Y o] = 0 := fun o => hGFF.integral_eq_zero o.1 o.2
  -- the Gaussian variable `X = hC(q_f)` and the shifts `a_o = o.smear f`
  let q : GFFObservable.Admissible := ⟨GFFObservable.pairing (cmTestFn f), cmTestFn_isTestFunction hf hc⟩
  let a : GFFObservable.Admissible → ℝ := fun o => o.1.smear f
  have hcov : ∀ o : GFFObservable.Admissible, cov[Y o, Y q; P] = a o := by
    intro o
    have hfun : (fun x => (GFFObservable.pairing (cmTestFn f)).smear (fun y => wholePlaneCov x y)) = f := by
      funext x
      have h2 := integral_wholePlaneCov_mul_cmTestFn hf hc x
      rw [hAv, sub_zero] at h2
      simp only [GFFObservable.smear]
      rw [← h2]
      exact integral_congr_ae (ae_of_all _ (fun y => mul_comm _ _))
    have h := hGFF.covariance_eq o.1 q.1 o.2 q.2
    refine h.trans ?_
    unfold wholePlaneGFFCov
    change o.1.smear (fun x => (GFFObservable.pairing (cmTestFn f)).smear (fun y => wholePlaneCov x y))
      = o.1.smear f
    rw [hfun]
  have hXlaw : HasLaw (Y q) (gaussianReal 0 (Var[Y q; P]).toNNReal) P := by
    refine ⟨(hYm q).aemeasurable, ?_⟩
    have h := (hYG.hasGaussianLaw_eval q).map_eq_gaussianReal
    rwa [hcen q] at h
  -- the tilted measure
  set P' := P.withDensity (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2))) with hP'
  have : IsProbabilityMeasure P' := isProbabilityMeasure_tilt hXlaw (variance_nonneg _ _)
  have hshift := law_shift hYG hYm hcen q a hcov
  have hevalEq : ∀ (x : Ω) (o : GFFObservable.Admissible),
      o.1.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r) = Y o x + a o := by
    intro x o
    rw [eval_addFunPairing]
  have hYG' : IsGaussianProcess (fun (o : GFFObservable.Admissible) (x : Ω) =>
      o.1.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r)) P' := by
    refine ⟨fun I => ?_⟩
    have hfun : (fun x => I.restrict (fun o : GFFObservable.Admissible =>
        o.1.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r)))
        = fun x (t : I) => Y t x + a t := by
      funext x t
      exact hevalEq x t
    rw [hfun]
    refine ⟨(Measurable.of_eval (fun t : I => (hYm t).add_const (a t))).aemeasurable, ?_⟩
    rw [hshift I]
    exact (hYG.hasGaussianLaw I).isGaussian_map
  have hDmeas : Measurable (fun x => ENNReal.ofReal (Real.exp (-Y q x - Var[Y q; P] / 2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((hYm q).neg.sub_const _))
  refine ⟨P', withDensity_absolutelyContinuous P _,
    withDensity_absolutelyContinuous' hDmeas.aemeasurable
      (ae_of_all _ (fun x => (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')), ?_⟩
  refine
    { measurable_pairing := fun φ hφ => (hGFF.measurable_pairing φ hφ).add_const _
      measurable_circle := fun r z hr => (hGFF.measurable_circle r z hr).add_const _
      isGaussianProcess := hYG'
      integral_eq_zero := ?_
      covariance_eq := ?_
      ae_continuousOn_circle := ?_ }
  · -- the mean of each shifted observable is zero
    intro o ho
    let oa : GFFObservable.Admissible := ⟨o, ho⟩
    have hfun : (fun x => o.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r))
        = fun x => Y oa x + a oa := funext (fun x => hevalEq x oa)
    show ∫ x, o.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r) ∂P' = 0
    rw [hfun]
    have hs : (⟨oa, Finset.mem_singleton_self oa⟩ : ({oa} : Finset GFFObservable.Admissible)) = ⟨oa, Finset.mem_singleton_self oa⟩ := rfl
    have hmeasEv : Measurable (fun g : ({oa} : Finset GFFObservable.Admissible) → ℝ =>
        g ⟨oa, Finset.mem_singleton_self oa⟩) := measurable_pi_apply _
    have hZ1 : Measurable (fun x (t : ({oa} : Finset GFFObservable.Admissible)) => Y t x + a t) :=
      Measurable.of_eval (fun t => (hYm t).add_const (a t))
    have hZ0 : Measurable (fun x (t : ({oa} : Finset GFFObservable.Admissible)) => Y t x) :=
      Measurable.of_eval (fun t => hYm t)
    have h1 : P'.map (fun x => Y oa x + a oa) = P.map (Y oa) := by
      have h := congrArg (Measure.map (fun g : ({oa} : Finset GFFObservable.Admissible) → ℝ =>
        g ⟨oa, Finset.mem_singleton_self oa⟩)) (hshift {oa})
      rw [Measure.map_map hmeasEv hZ1, Measure.map_map hmeasEv hZ0] at h
      exact h
    have hmeas : Measurable (fun x => Y oa x + a oa) := (hYm oa).add_const _
    have hint : ∫ x, Y oa x + a oa ∂P' = ∫ y, y ∂(P'.map (fun x => Y oa x + a oa)) := by
      rw [integral_map (f := fun y : ℝ => y) hmeas.aemeasurable (by fun_prop)]
    rw [hint, h1, integral_map (f := fun y : ℝ => y) (hYm oa).aemeasurable (by fun_prop)]
    simpa using hcen oa
  · -- the covariances are those of the original process
    intro o o' ho ho'
    let oa : GFFObservable.Admissible := ⟨o, ho⟩
    let ob : GFFObservable.Admissible := ⟨o', ho'⟩
    have hfun1 : (fun x => o.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r))
        = fun x => Y oa x + a oa := funext (fun x => hevalEq x oa)
    have hfun2 : (fun x => o'.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r))
        = fun x => Y ob x + a ob := funext (fun x => hevalEq x ob)
    show cov[fun x => o.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r),
      fun x => o'.eval (addFunPairing (hC x) f) (fun r z => hcirc x r z + Real.circleAverage f z r); P'] = _
    rw [hfun1, hfun2]
    classical
    have hmeasPair : Measurable (fun g : ({oa, ob} : Finset GFFObservable.Admissible) → ℝ =>
        (g ⟨oa, Finset.mem_insert_self _ _⟩, g ⟨ob, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)) :=
      (measurable_pi_apply _).prodMk (measurable_pi_apply _)
    have hZ1 : Measurable (fun x (t : ({oa, ob} : Finset GFFObservable.Admissible)) => Y t x + a t) :=
      Measurable.of_eval (fun t => (hYm t).add_const (a t))
    have hZ0 : Measurable (fun x (t : ({oa, ob} : Finset GFFObservable.Admissible)) => Y t x) :=
      Measurable.of_eval (fun t => hYm t)
    have hJ : P'.map (fun x => (Y oa x + a oa, Y ob x + a ob)) = P.map (fun x => (Y oa x, Y ob x)) := by
      have h := congrArg (Measure.map (fun g : ({oa, ob} : Finset GFFObservable.Admissible) → ℝ =>
        (g ⟨oa, Finset.mem_insert_self _ _⟩, g ⟨ob, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩)))
        (hshift {oa, ob})
      rw [Measure.map_map hmeasPair hZ1, Measure.map_map hmeasPair hZ0] at h
      exact h
    have hMX' : MemLp (fun x => Y oa x + a oa) 2 P' := by
      rw [← hfun1]; exact (hYG'.hasGaussianLaw_eval oa).memLp_two
    have hMY' : MemLp (fun x => Y ob x + a ob) 2 P' := by
      rw [← hfun2]; exact (hYG'.hasGaussianLaw_eval ob).memLp_two
    have hMX : MemLp (Y oa) 2 P := (hYG.hasGaussianLaw_eval oa).memLp_two
    have hMY : MemLp (Y ob) 2 P := (hYG.hasGaussianLaw_eval ob).memLp_two
    rw [cov_eq_of_map_eq hJ hMX' hMY' hMX hMY]
    exact hGFF.covariance_eq o o' ho ho'
  · -- continuity of the circle average process transfers along `P' ≪ P`
    have h0 := hGFF.ae_continuousOn_circle
    have h1 := (withDensity_absolutelyContinuous P (fun x => ENNReal.ofReal
      (Real.exp (-Y q x - Var[Y q; P] / 2)))).ae_le h0
    filter_upwards [h1] with x hx
    exact hx.add (continuous_realCircleAverage hf.continuous).continuousOn

end Main


end HarmonicBalls.S11aj
