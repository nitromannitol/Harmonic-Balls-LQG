import HarmonicBalls.FirstPass.Phase2.CanonicalDecodersCanonXi
import HarmonicBalls.FirstPass.S11ak.BaseComparison
import HarmonicBalls.FirstPass.S11i.Final11_13
import HarmonicBalls.FirstPass.S11r.FrozenCanonDecoders

/-! # Canonical-exponent decoder consumers

The first declaration, `lqgCanonicalDecodersExist_of_measurable_canonXi`, is the canonical-exponent form of `lqgCanonicalDecodersExist_of_measurable` (`FirstPass/S11i/Final11_13.lean:150`), the projection of the measurable canonical-exponent decoder existence. The second, `canonDecoderData_of_frozen_canonXi`, extracts `CanonDecoderData γ (lqgXi γ) α₀` for `0 < γ < 2` and `α₀ < lqgQ γ` from the same measurable statement.
-/

namespace HarmonicBalls.FirstPassS11iFinal11_13

/-- Canonical-exponent form of `lqgCanonicalDecodersExist_of_measurable` (`FirstPass/S11i/Final11_13.lean:150`):
the projection of the measurable canonical-exponent decoder existence. -/
theorem lqgCanonicalDecodersExist_of_measurable_canonXi
    (h : HarmonicBalls.LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0}) :
    HarmonicBalls.LQGCanonicalDecodersExistCanonXiStmt.{0} :=
  HarmonicBalls.lqgCanonicalDecodersExistCanonXi_of_measurableCanonXi h

end HarmonicBalls.FirstPassS11iFinal11_13

namespace HarmonicBalls.FirstPassS11rFrozenCanonDecoders
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal
theorem canonDecoderData_of_frozen_canonXi (hEx : HarmonicBalls.LQGCanonicalDecodersMeasurableExistCanonXiStmt.{0})
    {γ α₀ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ) : Nonempty (CanonDecoderData γ (lqgXi γ) α₀) := by
  obtain ⟨K, d, hK, hKf, hd, hid, G, hGm, hGa, hGs⟩ := hEx γ α₀ hγ0 hγ2 hα
  exact ⟨⟨K, d, hK, hKf, hd, hid, G, hGm, hGa, hGs⟩⟩
end HarmonicBalls.FirstPassS11rFrozenCanonDecoders
