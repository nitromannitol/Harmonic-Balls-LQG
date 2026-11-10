import Mathlib

/-!
# Campbell-to-null step of Lemma 11.13 (write-up sec. 5.3, identities (23)-(25))

Pure measure theory. The frozen local Campbell statement `LocalCampbellMarkedRestrictionFrozen` (Frozen/S11c.lean)
yields a vanishing mixed expectation `E[(μ_ω U)⁻¹ · μ_ω (U ∩ B)] = 0` for the bad marked set `B`. This file turns it
into `μ_ω (U ∩ B) = 0` almost surely, provided `μ_ω U < ∞` almost surely (write-up (24)-(25)).
-/

namespace HarmonicBalls.CampbellNull

open MeasureTheory

/-- **Write-up (23)-(25).** If `E[(μ_ω U)⁻¹ · μ_ω (U ∩ B)] = 0`, the integrand is measurable (almost everywhere),
and `μ_ω U ≠ ∞` almost surely, then `μ_ω (U ∩ B) = 0` almost surely. Case split: if `μ_ω U = 0` the mass of
`U ∩ B` vanishes by monotonicity; otherwise `(μ_ω U)⁻¹ ≠ 0`, so the vanishing product forces `μ_ω (U ∩ B) = 0`. -/
theorem ae_measure_inter_eq_zero_of_lintegral_inv_mul {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {μ : Ω → Measure ℂ} {U B : Set ℂ}
    (hfin : ∀ᵐ ω ∂P, μ ω U ≠ ⊤)
    (hmeas : AEMeasurable (fun ω => (μ ω U)⁻¹ * μ ω (U ∩ B)) P)
    (h0 : ∫⁻ ω, (μ ω U)⁻¹ * μ ω (U ∩ B) ∂P = 0) :
    ∀ᵐ ω ∂P, μ ω (U ∩ B) = 0 := by
  have hzero : ∀ᵐ ω ∂P, (μ ω U)⁻¹ * μ ω (U ∩ B) = 0 :=
    (lintegral_eq_zero_iff' hmeas).1 h0
  filter_upwards [hfin, hzero] with ω hωfin hωz
  by_cases hU : μ ω U = 0
  · exact measure_mono_null Set.inter_subset_left hU
  · have hinv : (μ ω U)⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hωfin
    exact (mul_eq_zero.1 hωz).resolve_left hinv

end HarmonicBalls.CampbellNull
