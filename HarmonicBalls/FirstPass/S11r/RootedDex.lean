import HarmonicBalls.FirstPass.S11ai.RootedTransfer
import HarmonicBalls.FirstPass.Frozen.S11j

/-!
# Existence of the translated LQG metric (fp-S11r-hDex-source)

The binder `hDex` of the rooted assembly (RootedBuffer.lean, `ae_rootedLocalIdent_assembled`):
for every `z : ℂ` there is a function `D` with `IsLQGMetricOfField P γ ξ γ (translatedPairing hC hcirc z) D`,
that is, the γ-LQG metric of the translated whole-plane field with the log singularity `-γ log |·|` (Fact 2.2 of
Bou-Rabee-Gwynne, arXiv:2208.11795, p. 9, eq. (2.7)).

Derivation (no new input):
* `hAff : AffineInvarianceAll Ω` (Proposed `WholePlaneGFFAffineInvariance`, `Proposed/LQG.lean:53`; already a
  consumer input of `RootedAssembly.lean`) gives that the translated pairing and circle averages form a whole-plane
  GFF (`isWholePlaneGFF_translatedPairing`, `S11ai/RootedTransfer.lean`).
* `hField : LQGMetricFieldAxiomsUnivFrozen` (frozen, `Frozen/S11j.lean`), item I of Fact 2.2, gives a.s. finiteness
  `weylScaling (𝔇 (hC' ω)) ξ (-γ log|·|) u v < ∞` for all `u v`, for any `𝔇` with `IsLQGMetric γ ξ 𝔇`, under
  `γ < lqgQ γ` (true for `0 < γ < 2`).
* `D ω u v := (weylScaling (𝔇 (hC' ω)) ξ (-γ log|·|) u v).toReal` then satisfies the defining equation of
  `IsLQGMetricOfField` with the same `𝔇`, by `ENNReal.ofReal_toReal` on the finite values.
-/

universe u

namespace HarmonicBalls

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

/-- **Translated LQG metric exists** (the binder `hDex` of the rooted assembly). For `0 < γ < 2`, a whole-plane GFF
`hC`, a γ-LQG metric `𝔇` with Weyl exponent `ξ`, and the affine invariance of the whole-plane GFF, every translate
`z` carries a γ-LQG metric of the field with the log singularity `-γ log |·|` at `0`, in the sense of
`IsLQGMetricOfField`. -/
theorem exists_isLQGMetricOfField_translatedPairing {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {γ ξ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ}
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hAff : FirstPassS11ai.AffineInvarianceAll Ω)
    (hG : IsWholePlaneGFF P hC hcirc) (h𝔇 : IsLQGMetric γ ξ 𝔇) (hField : LQGMetricFieldAxiomsUnivFrozen.{u})
    (z : ℂ) :
    ∃ D : Ω → ℂ → ℂ → ℝ, IsLQGMetricOfField P γ ξ γ (S11c.translatedPairing hC hcirc z) D := by
  have hγQ : γ < lqgQ γ := by
    have h1 : γ / 2 < 2 / γ := by
      rw [div_lt_div_iff₀ two_pos hγ0]
      nlinarith
    unfold lqgQ
    linarith
  have hT : IsWholePlaneGFF P (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z) :=
    FirstPassS11ai.isWholePlaneGFF_translatedPairing hAff hG z
  have hfin := hField Ω P γ ξ γ (S11c.translatedPairing hC hcirc z) (S11c.translatedCircle hcirc z) hT hγ0 hγ2
    hγQ 𝔇 h𝔇
  refine ⟨fun ω u v => (weylScaling (𝔇 (S11c.translatedPairing hC hcirc z ω)) ξ
    (fun x => -γ * Real.log ‖x‖) u v).toReal, ?_⟩
  unfold IsLQGMetricOfField
  refine ⟨𝔇, h𝔇, ?_⟩
  filter_upwards [hfin.1] with ω hω
  intro u v
  exact ⟨ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (hω.1 u v).ne⟩

#print axioms exists_isLQGMetricOfField_translatedPairing

end HarmonicBalls
