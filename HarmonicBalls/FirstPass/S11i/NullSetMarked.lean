import Mathlib

/-!
# Null sets from a vanishing marked expectation (Lemma 11.13, Fubini step)

NEW step of Lemma 11.13 (`lemma:mu_h-pinch-bad`, corrected proof, paper lines 3884-3889): "Fubini and the marked identity
show `E ∫_{B_1} 1_{certificate frequency fails at z} μ_g(dz) = 0`. Hence almost surely failure occurs at no more than a
`μ_g`-null set of points." The marked identity that produces the zero expectation is a separate (EXTERNAL) input and is
not used here. This module proves the deterministic Fubini part: if the expected `μ ω`-integral of a measurable
nonnegative marked function vanishes, then almost surely the function vanishes `μ ω`-almost everywhere.
-/

open MeasureTheory ProbabilityTheory

namespace FirstPassS11i

/-- Fubini step: a vanishing expected integral against an s-finite kernel `κ : Ω → Measure X` forces, almost surely,
`F ω = 0` `κ ω`-almost everywhere. The s-finiteness of the LQG measure family `ω ↦ μ ω` on `ℂ` is a caller's
obligation (it holds for a measurable family of locally finite measures); it is needed for measurability of
`ω ↦ ∫⁻ F ω dκ ω`. -/
theorem ae_ae_eq_zero_of_lintegral_eq_zero {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (κ : Kernel Ω X) [IsSFiniteKernel κ] (F : Ω → X → ENNReal)
    (hF : Measurable (Function.uncurry F))
    (h : ∫⁻ ω, ∫⁻ x, F ω x ∂(κ ω) ∂P = 0) :
    ∀ᵐ ω ∂P, ∀ᵐ x ∂(κ ω), F ω x = 0 := by
  have hg : Measurable fun ω => ∫⁻ x, F ω x ∂(κ ω) := hF.lintegral_kernel_prod_right
  have hg0 : (fun ω => ∫⁻ x, F ω x ∂(κ ω)) =ᵐ[P] 0 := (lintegral_eq_zero_iff hg).1 h
  filter_upwards [hg0] with ω hω
  have hω' : ∫⁻ x, F ω x ∂(κ ω) = 0 := hω
  have hmeas : Measurable (F ω) := hF.comp measurable_prodMk_left
  exact (lintegral_eq_zero_iff hmeas).1 hω'

end FirstPassS11i
