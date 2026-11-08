import Mathlib

/-! # Finite families of a Gaussian process as Gaussian vectors (Route (A), Palm identity)

Mathlib's `IsGaussianProcess X P` says that every restriction `I.restrict (X · ω)` to a finite index set `I` is a
Gaussian vector. For a finite family `t : ι → T` of indices this gives the Gaussian vector `ω ↦ (X (t i) ω)_{i}`, and for
`ι = Option κ` the pair `((X (t (some j)) ω)_{j : κ}, X (t none) ω)` in `(κ → ℝ) × ℝ`. The second form is the joint
law of `((hC φ_j)_j, hcirc ε z)` that `integral_gaussian_exp_tilt` requires.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HarmonicBalls

variable {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A finite family of a real Gaussian process is a Gaussian vector. -/
theorem hasGaussianLaw_family {X : T → Ω → ℝ} (hX : IsGaussianProcess X P) {ι : Type*} [Fintype ι]
    (t : ι → T) : HasGaussianLaw (fun ω (i : ι) => X (t i) ω) P := by
  have h := (hX.comp_right t).hasGaussianLaw (Finset.univ : Finset ι)
  let L : (↥(Finset.univ : Finset ι) → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i : ι => ContinuousLinearMap.proj (⟨i, Finset.mem_univ i⟩ : (Finset.univ : Finset ι))
  exact h.map L

/-- The pair `((X (t (some j)))_{j : κ}, X (t none))` of a finite family of a real Gaussian process is a Gaussian vector
in `(κ → ℝ) × ℝ`. -/
theorem hasGaussianLaw_pair_family {X : T → Ω → ℝ} (hX : IsGaussianProcess X P) {κ : Type*} [Fintype κ]
    (t : Option κ → T) :
    HasGaussianLaw (fun ω => ((fun j : κ => X (t (some j)) ω), X (t none) ω)) P := by
  have h := hasGaussianLaw_family hX t
  let L : (Option κ → ℝ) →L[ℝ] ((κ → ℝ) × ℝ) :=
    (ContinuousLinearMap.pi fun j : κ => ContinuousLinearMap.proj (some j : Option κ)).prod
      (ContinuousLinearMap.proj (none : Option κ))
  exact h.map L

end HarmonicBalls

end
