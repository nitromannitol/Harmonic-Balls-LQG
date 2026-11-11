import HarmonicBalls.Proofs.SecA.Basic
import HarmonicBalls.FirstPass.Phase2.CameronMartinMutualDerived
import HarmonicBalls.FirstPass.Phase2.CameronMartinReweightingDerived2

/-!
# Derived inputs, batch 9

Binder-free restatements `<propName>_derived : <Prop>` of frozen/FP Props that an existing
theorem already proves. The Prop is written exactly as in its declaration; the proof is glue.

* `superharmonicOfLaplacianLEStep_derived : SuperharmonicOfLaplacianLEStep`
  (`HarmonicBalls/Steps/SecA/Basic.lean:80`; triage name `FPSuperharmonicOfLaplacianLE`).
  Discharged by `superharmonicOfLaplacianLEStep_holds` (`HarmonicBalls/Proofs/SecA/Basic.lean:468`).

* `cameronMartinGFFMutualAbsCont_derived : CameronMartinGFFMutualAbsCont.{u}`
  (`HarmonicBalls/FirstPass/Frozen/S11d.lean:74`). The theorem
  `HarmonicBalls.cameronMartinGFFMutualAbsCont_derived` (`FirstPass/Phase2/CameronMartinMutualDerived.lean:56`)
  takes the input `CameronMartinGFFReweighting`; that input is discharged binder-free by
  `HarmonicBalls.S11aj.cameronMartinGFFReweighting_derived`
  (`FirstPass/Phase2/CameronMartinReweightingDerived2.lean:267`). The root name is taken by the
  binder form, so this copy lives in the namespace `HarmonicBalls.DerivedInputs9`.
-/

universe u

namespace HarmonicBalls.DerivedInputs9

open HarmonicBalls

/-- Superharmonicity from a continuous function with `Δw ≤ 0` (triage `FPSuperharmonicOfLaplacianLE`).
Glue for `superharmonicOfLaplacianLEStep_holds`. -/
theorem superharmonicOfLaplacianLEStep_derived : SuperharmonicOfLaplacianLEStep :=
  superharmonicOfLaplacianLEStep_holds

/-- Cameron–Martin mutual absolute continuity of the whole-plane GFF (triage `CameronMartinGFFMutualAbsCont`).
Glue: the reweighting input is itself derived. -/
theorem cameronMartinGFFMutualAbsCont_derived : CameronMartinGFFMutualAbsCont.{u} :=
  HarmonicBalls.cameronMartinGFFMutualAbsCont_derived
    HarmonicBalls.S11aj.cameronMartinGFFReweighting_derived

end HarmonicBalls.DerivedInputs9
