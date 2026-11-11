import HarmonicBalls.Defs.GFF
import HarmonicBalls.Defs.Laplacian
import HarmonicBalls.Defs.LQGMetric
import HarmonicBalls.Defs.LQG
import HarmonicBalls.Defs.Notation
import HarmonicBalls.Proofs.GFF.MeasurableContinuousCircleVersion
import HarmonicBalls.Proofs.GFF.CommonContinuousCircleLQGVersion
import HarmonicBalls.Proofs.Sec11.ModConstPairingLaw
import LatticeProb.Gauss.GFF

/-!
# Bridge to the staged whole-plane GFF definitions (module M1)

Each definition of `LatticeProb.Gauss` in `HarmonicBalls/LPStage/GFF.lean` is the same object as the corresponding
`HarmonicBalls` definition. For the definitions whose bodies do not mention the observable type, the bridge is `rfl`:
`fieldPairing`, `fieldCircleAverage`, `fieldSigmaAlgebra`, `wholePlaneCov`, `IsTestFunction`, `addFunPairing`,
`affinePullbackPairing`, `distributionMeasurableSpace`, `pairingSigmaAlgebra`, `addCircleAverage`, `PolyHighProb`,
`CircleParameter`, `circleProfile`, `LocalZeroMeanTest`, `localModConstPairings`.

The observable type `GFFObservable` is an inductive type and each copy is a different type, so no `rfl` relates the
two copies. The bridge is then an explicit equivalence `observableEquiv`, with the observable-level statements
(`isAdmissible_iff`, `eval_eq`, `smear_eq`, `wholePlaneGFFCov_eq`) proved by case analysis, each by `rfl`, and the
structure `IsWholePlaneGFF` bridged by the `iff` `isWholePlaneGFF_iff`, transporting the Gaussian family along the
equivalence (`IsGaussianProcess.comp_right`).
-/

namespace HarmonicBalls.LPBridge

open MeasureTheory ProbabilityTheory

theorem isTestFunction_eq : HarmonicBalls.IsTestFunction = LatticeProb.Gauss.IsTestFunction := rfl

theorem circleParameter_eq : HarmonicBalls.CircleParameter = LatticeProb.Gauss.CircleParameter := rfl

theorem wholePlaneCov_eq (z w : ℂ) :
    HarmonicBalls.wholePlaneCov z w = LatticeProb.Gauss.wholePlaneCov z w := rfl

theorem fieldPairing_eq (α₀ : ℝ) (hC : (ℂ → ℝ) → ℝ) (φ : ℂ → ℝ) :
    HarmonicBalls.fieldPairing α₀ hC φ = LatticeProb.Gauss.fieldPairing α₀ hC φ := rfl

theorem fieldCircleAverage_eq (α₀ : ℝ) (hcirc : ℝ → ℂ → ℝ) (r : ℝ) (z : ℂ) :
    HarmonicBalls.fieldCircleAverage α₀ hcirc r z = LatticeProb.Gauss.fieldCircleAverage α₀ hcirc r z := rfl

theorem fieldSigmaAlgebra_eq {Ω : Type*} (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) :
    HarmonicBalls.fieldSigmaAlgebra α₀ hC U = LatticeProb.Gauss.fieldSigmaAlgebra α₀ hC U := rfl

theorem addFunPairing_eq (T : (ℂ → ℝ) → ℝ) (f : ℂ → ℝ) :
    HarmonicBalls.addFunPairing T f = LatticeProb.Gauss.addFunPairing T f := rfl

theorem affinePullbackPairing_eq (T : (ℂ → ℝ) → ℝ) (r : ℝ) (z : ℂ) :
    HarmonicBalls.affinePullbackPairing T r z = LatticeProb.Gauss.affinePullbackPairing T r z := rfl

theorem distributionMeasurableSpace_eq :
    HarmonicBalls.distributionMeasurableSpace = LatticeProb.Gauss.distributionMeasurableSpace := rfl

theorem pairingSigmaAlgebra_eq {Ω : Type*} (h : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) :
    HarmonicBalls.pairingSigmaAlgebra h U = LatticeProb.Gauss.pairingSigmaAlgebra h U := rfl

theorem addCircleAverage_eq (hε : ℝ → ℂ → ℝ) (f : ℂ → ℝ) :
    HarmonicBalls.addCircleAverage hε f = LatticeProb.Gauss.addCircleAverage hε f := rfl

theorem polyHighProb_eq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (E : ℝ → Set Ω) :
    HarmonicBalls.PolyHighProb P E = LatticeProb.Gauss.PolyHighProb P E := rfl

theorem circleProfile_eq (F : C(LatticeProb.Gauss.CircleParameter, ℝ)) (r : ℝ) (z : ℂ) :
    HarmonicBalls.circleProfile F r z = LatticeProb.Gauss.circleProfile F r z := rfl

theorem localZeroMeanTest_eq (U : Set ℂ) :
    HarmonicBalls.LocalZeroMeanTest U = LatticeProb.Gauss.LocalZeroMeanTest U := rfl

theorem localModConstPairings_eq {Ω : Type*} (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (U : Set ℂ) (ω : Ω) :
    HarmonicBalls.localModConstPairings α hC U ω = LatticeProb.Gauss.localModConstPairings α hC U ω := rfl

/-- The equivalence between the observables of `HarmonicBalls` and of `LatticeProb.Gauss` (the pairings and the
circle averages correspond constructor by constructor). -/
def observableEquiv : HarmonicBalls.GFFObservable ≃ LatticeProb.Gauss.GFFObservable where
  toFun
    | .pairing φ => .pairing φ
    | .circle r z => .circle r z
  invFun
    | .pairing φ => .pairing φ
    | .circle r z => .circle r z
  left_inv o := by cases o <;> rfl
  right_inv o := by cases o <;> rfl

/-- The admissible observables correspond under `observableEquiv`. -/
theorem isAdmissible_iff (o : HarmonicBalls.GFFObservable) :
    LatticeProb.Gauss.GFFObservable.IsAdmissible (observableEquiv o) ↔ o.IsAdmissible := by
  cases o <;> exact Iff.rfl

theorem eval_eq (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (o : HarmonicBalls.GFFObservable) :
    LatticeProb.Gauss.GFFObservable.eval hC hcirc (observableEquiv o) = o.eval hC hcirc := by
  cases o <;> rfl

theorem smear_eq (o : HarmonicBalls.GFFObservable) (f : ℂ → ℝ) :
    LatticeProb.Gauss.GFFObservable.smear (observableEquiv o) f = o.smear f := by
  cases o <;> rfl

theorem wholePlaneGFFCov_eq (o o' : HarmonicBalls.GFFObservable) :
    LatticeProb.Gauss.wholePlaneGFFCov (observableEquiv o) (observableEquiv o') =
      HarmonicBalls.wholePlaneGFFCov o o' := by
  cases o <;> cases o' <;> rfl

/-- The admissible observables of the two copies, as a subtype equivalence. -/
def admissibleEquiv : HarmonicBalls.GFFObservable.Admissible ≃ LatticeProb.Gauss.GFFObservable.Admissible :=
  Equiv.subtypeEquiv observableEquiv fun o => (isAdmissible_iff o).symm

theorem admissibleEquiv_val (o : HarmonicBalls.GFFObservable.Admissible) :
    (admissibleEquiv o).1 = observableEquiv o.1 := rfl

theorem evalAdm_eq (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (o : HarmonicBalls.GFFObservable.Admissible) :
    (admissibleEquiv o).1.eval hC hcirc = o.1.eval hC hcirc := by
  rw [admissibleEquiv_val]
  exact eval_eq hC hcirc o.1

theorem evalAdm_symm (hC : (ℂ → ℝ) → ℝ) (hcirc : ℝ → ℂ → ℝ) (o' : LatticeProb.Gauss.GFFObservable.Admissible) :
    (admissibleEquiv.symm o').1.eval hC hcirc = o'.1.eval hC hcirc := by
  have h := admissibleEquiv_val (admissibleEquiv.symm o')
  rw [Equiv.apply_symm_apply] at h
  rw [← eval_eq hC hcirc (admissibleEquiv.symm o').1, ← h]

/-- The structure `IsWholePlaneGFF` of `HarmonicBalls` and of `LatticeProb.Gauss` are equivalent: the two copies
differ only in the observable type, transported by `observableEquiv`. -/
theorem isWholePlaneGFF_iff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) :
    HarmonicBalls.IsWholePlaneGFF P hC hcirc ↔ LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc := by
  constructor
  · intro h
    refine ⟨h.measurable_pairing, h.measurable_circle, ?_, ?_, ?_, h.ae_continuousOn_circle⟩
    · have hproc : (fun (o' : LatticeProb.Gauss.GFFObservable.Admissible) ω =>
          o'.1.eval (hC ω) (hcirc ω)) =
          (fun (o : HarmonicBalls.GFFObservable.Admissible) ω => o.1.eval (hC ω) (hcirc ω)) ∘
            admissibleEquiv.symm := by
        funext o' ω
        exact (evalAdm_symm (hC ω) (hcirc ω) o').symm
      rw [hproc]
      exact h.isGaussianProcess.comp_right admissibleEquiv.symm
    · intro o' ho'
      have hadm : (observableEquiv.symm o').IsAdmissible := by
        rw [← isAdmissible_iff, Equiv.apply_symm_apply]
        exact ho'
      have := h.integral_eq_zero (observableEquiv.symm o') hadm
      simp only [← eval_eq, Equiv.apply_symm_apply] at this
      exact this
    · intro o' o'' ho' ho''
      have h1 : (observableEquiv.symm o').IsAdmissible := by
        rw [← isAdmissible_iff, Equiv.apply_symm_apply]
        exact ho'
      have h2 : (observableEquiv.symm o'').IsAdmissible := by
        rw [← isAdmissible_iff, Equiv.apply_symm_apply]
        exact ho''
      have := h.covariance_eq (observableEquiv.symm o') (observableEquiv.symm o'') h1 h2
      simp only [← eval_eq, ← wholePlaneGFFCov_eq, Equiv.apply_symm_apply] at this
      exact this
  · intro h
    refine ⟨h.measurable_pairing, h.measurable_circle, ?_, ?_, ?_, h.ae_continuousOn_circle⟩
    · have hproc : (fun (o : HarmonicBalls.GFFObservable.Admissible) ω => o.1.eval (hC ω) (hcirc ω)) =
          (fun (o' : LatticeProb.Gauss.GFFObservable.Admissible) ω => o'.1.eval (hC ω) (hcirc ω)) ∘
            admissibleEquiv := by
        funext o ω
        exact (evalAdm_eq (hC ω) (hcirc ω) o).symm
      rw [hproc]
      exact h.isGaussianProcess.comp_right admissibleEquiv
    · intro o ho
      have := h.integral_eq_zero (observableEquiv o) ((isAdmissible_iff o).mpr ho)
      simp only [eval_eq] at this
      exact this
    · intro o o' ho ho'
      have := h.covariance_eq (observableEquiv o) (observableEquiv o')
        ((isAdmissible_iff o).mpr ho) ((isAdmissible_iff o').mpr ho')
      simp only [eval_eq, wholePlaneGFFCov_eq] at this
      exact this

end HarmonicBalls.LPBridge
