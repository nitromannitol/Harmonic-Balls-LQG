import HarmonicBalls.FirstPass.Frozen.S8d

/-! # FIRST-PASS helper (fp-S8d, owner n4): uniqueness of the vague limit defining the LQG measure

`IsLQGLimit γ h m` (Defs/LQG.lean:49) says that `m` is a Radon measure and the vague limit of the approximations of the
profile `h`. The limit is unique: its integrals of continuous compactly supported functions are limits of the same
sequence, hence agree, and `RadonIntegralUniqueFrozen` (Rudin RCA Thm 2.14) identifies the measures. -/

open MeasureTheory Filter Topology

namespace HarmonicBalls

/-- The vague limit of the approximations is unique, given the uniqueness of Radon measures from their integrals. -/
theorem s8d_isLQGLimit_unique (hU : RadonIntegralUniqueFrozen) {γ : ℝ} {h : ℝ → ℂ → ℝ} {m m' : Measure ℂ}
    (H : IsLQGLimit γ h m) (H' : IsLQGLimit γ h m') : m = m' := by
  refine hU m m' H.isLocallyFiniteMeasure H'.isLocallyFiniteMeasure fun f hf hc => ?_
  exact tendsto_nhds_unique (H.tendsto_integral f hf hc) (H'.tendsto_integral f hf hc)

#print axioms s8d_isLQGLimit_unique

end HarmonicBalls
