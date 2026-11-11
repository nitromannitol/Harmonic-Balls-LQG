import HarmonicBalls.FirstPass.S11i.Step8CorrectedMarked
import HarmonicBalls.FirstPass.S11at.Producers

/-! # Cylinder π-system for the joint law of (field, circle profile, root) (MQ-lh-30, steps J1–J3)

Steps J1–J3 of the Lean plan for MQ-lh-30 (a) (`notes/fp-gaps/MATH-ANSWERS.md`, lines 948–972).

On the joint sample space `DMSJointX := ((ℂ → ℝ) → ℝ) × (CircleParameter → ℝ) × ℂ` (a field `T`, a circle-average profile,
and a root `z`), `mX` is the product of the pairing σ-algebra on the field factor (the σ-algebra of the test-function
evaluations, `pairingSigmaAlgebra (fun T => T) univ`) with the product σ-algebra on the profile and root factors.

* `obs φ c` evaluates the field at finitely many test functions `φ i`, the profile at finitely many circle parameters `c k`,
  and keeps the root.
* `cyl` is the family of cylinders `obs φ c ⁻¹' E` with `E` measurable and every `φ i` a test function on `univ`.
  It contains the whole space (`univ_mem_cyl`), is a π-system (`isPiSystem_cyl`), and generates `mX` (`generateFrom_cyl`).

Terminology: pairing σ-algebra and test-function evaluations (Duplantier-Miller-Sheffield, arXiv:1409.7055, Appendix A),
circle averages of the whole-plane field (Armitage-Gardiner), rooted LQG measures (Duplantier-Sheffield, arXiv:0808.1560, §3.3).
-/

open MeasureTheory Set Function
open HarmonicBalls.FirstPassS11iStep8Corrected

namespace HarmonicBalls.DMSJointPosCylinder

/-- The joint sample space: a field `T : (ℂ → ℝ) → ℝ`, a circle-average profile `CircleParameter → ℝ`, and a root `ℂ`. -/
abbrev DMSJointX : Type := ((ℂ → ℝ) → ℝ) × (CircleParameter → ℝ) × ℂ

/-- The σ-algebra `mX` on `DMSJointX`: the pairing σ-algebra on the field factor, times the product σ-algebra on the
profile and root factors. -/
noncomputable abbrev mX : MeasurableSpace DMSJointX :=
  (pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ).prod inferInstance

/-- The observation map: the field at the test functions `φ i`, the profile at the parameters `c k`, and the root. -/
def obs {n m : ℕ} (φ : Fin n → ℂ → ℝ) (c : Fin m → CircleParameter) (x : DMSJointX) :
    (Fin n → ℝ) × (Fin m → ℝ) × ℂ :=
  (fun i => x.1 (φ i), fun k => x.2.1 (c k), x.2.2)

/-- The cylinder sets: preimages under `obs φ c` of measurable sets, for finitely many test functions `φ i`. -/
def cyl : Set (Set DMSJointX) :=
  {S | ∃ (n m : ℕ) (φ : Fin n → ℂ → ℝ) (c : Fin m → CircleParameter)
      (E : Set ((Fin n → ℝ) × (Fin m → ℝ) × ℂ)),
      (∀ i, IsTestFunction Set.univ (φ i)) ∧ MeasurableSet E ∧ S = obs φ c ⁻¹' E}

/-- **J1.** The observation map is `mX`-measurable when every `φ i` is a test function on `univ`. -/
theorem measurable_obs {n m : ℕ} {φ : Fin n → ℂ → ℝ} {c : Fin m → CircleParameter}
    (hφ : ∀ i, IsTestFunction Set.univ (φ i)) : Measurable[mX] (obs φ c) := by
  let _ : MeasurableSpace ((ℂ → ℝ) → ℝ) := pairingSigmaAlgebra (fun T : (ℂ → ℝ) → ℝ => T) Set.univ
  unfold obs
  refine Measurable.prodMk (measurable_pi_iff.2 fun i => ?_)
    (Measurable.prodMk (measurable_pi_iff.2 fun k => ?_) (measurable_snd.comp measurable_snd))
  · exact (measurable_eval_pairingSigmaAlgebra (φ i) (hφ i)).comp measurable_fst
  · exact (measurable_pi_apply (c k)).comp (measurable_fst.comp measurable_snd)

/-- **J1.** The whole space is a cylinder (`n = m = 0`, `E = univ`). -/
theorem univ_mem_cyl : (Set.univ : Set DMSJointX) ∈ cyl :=
  ⟨0, 0, Fin.elim0, Fin.elim0, Set.univ, fun i => Fin.elim0 i, MeasurableSet.univ, Set.preimage_univ.symm⟩

end HarmonicBalls.DMSJointPosCylinder
