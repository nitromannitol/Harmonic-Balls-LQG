import Mathlib
import HarmonicBalls.Proofs.Sec11.ClosureScales.UniversalRealization

/-!
# The shifted circle-average map `Γ_z`

For a canonical
profile `c` and a point `z`, the paper defines the continuous circle-average function

  `(Γ_z c)(r,w) = c(r,w) - γ log max(r,|w-z|) + γ ∫ log max(1,|v|) σ_{r,w}(dv)`,

where `σ_{r,w}` is the normalized measure on the circle `∂B_r(w)`, and states that `(c,z) ↦ Γ_z c` is a jointly Borel map
into the canonical space. This file proves that `Γ_z c` is continuous on `J = (0,∞) × ℂ` (so it is a `CanonicalProfile`)
and that `(c,z) ↦ Γ_z c` is measurable. The marked Palm identity, which uses this map, is NOT formalized here:
its source is [DMS] Lemma A.10 (whole plane) and its marked version is only sketched in the paper (lines 1150-1156).
-/

namespace HarmonicBalls

open MeasureTheory Set Filter Topology

/-- The logarithmic weight `v ↦ log max(1,|v|)` whose circle averages enter `Γ_z`. -/
noncomputable def logMaxOne (v : ℂ) : ℝ :=
  Real.log (max 1 ‖v‖)

theorem continuous_logMaxOne : Continuous logMaxOne := by
  unfold logMaxOne
  exact (continuous_const.max continuous_norm).log fun v => (lt_max_of_lt_left zero_lt_one).ne'

/-- The circle averages of `logMaxOne` depend continuously on the centre and the radius. -/
theorem continuous_circleAverage_logMaxOne :
    Continuous fun p : ℂ × ℝ => Real.circleAverage logMaxOne p.1 p.2 := by
  unfold Real.circleAverage
  refine continuous_const.mul ?_
  have hu : Continuous fun q : (ℂ × ℝ) × ℝ => logMaxOne (circleMap q.1.1 q.1.2 q.2) :=
    continuous_logMaxOne.comp (by unfold circleMap; fun_prop)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : ℂ × ℝ) (θ : ℝ) => logMaxOne (circleMap p.1 p.2 θ)) hu 0 (2 * Real.pi)

/-- The shifted circle-average function `Γ_z`, applied to a function `f` on `ℝ × ℂ` (paper r7 1160-1168). -/
noncomputable def shiftedCircleFun (γ : ℝ) (z : ℂ) (f : ℝ × ℂ → ℝ) : ℝ × ℂ → ℝ :=
  fun p => f p - γ * Real.log (max p.1 ‖p.2 - z‖) + γ * Real.circleAverage logMaxOne p.2 p.1

/-- The shifted function is continuous on `J` when `f` is. -/
theorem continuousOn_shiftedCircleFun (γ : ℝ) (z : ℂ) {f : ℝ × ℂ → ℝ} (hf : ContinuousOn f circleIndexSet) :
    ContinuousOn (shiftedCircleFun γ z f) circleIndexSet := by
  unfold shiftedCircleFun
  have hlog : ContinuousOn (fun p : ℝ × ℂ => Real.log (max p.1 ‖p.2 - z‖)) circleIndexSet :=
    ((continuous_fst.max (continuous_snd.sub continuous_const).norm).continuousOn).log
      fun p hp => (lt_max_of_lt_left hp.1).ne'
  have hav : Continuous fun p : ℝ × ℂ => Real.circleAverage logMaxOne p.2 p.1 :=
    continuous_circleAverage_logMaxOne.comp (continuous_snd.prodMk continuous_fst)
  exact ((hf.sub (continuousOn_const.mul hlog)).add (continuousOn_const.mul hav.continuousOn))

/-- The shifted canonical profile `Γ_z c` (paper r7 1160-1168). -/
noncomputable def shiftedProfile (γ : ℝ) (z : ℂ) (c : CanonicalProfile) : CanonicalProfile :=
  ⟨shiftedCircleFun γ z c.1, continuousOn_shiftedCircleFun γ z c.2⟩

/-- **Joint measurability of `(c,z) ↦ Γ_z c`** ("a jointly Borel map of `(c,z)`"). -/
theorem measurable_shiftedProfile (γ : ℝ) :
    Measurable fun q : CanonicalProfile × ℂ => shiftedProfile γ q.2 q.1 := by
  have hfun : Measurable fun q : CanonicalProfile × ℂ => shiftedCircleFun γ q.2 q.1.1 := by
    refine Measurable.of_eval fun p => ?_
    have h1 : Measurable fun q : CanonicalProfile × ℂ => q.1.1 p :=
      (measurable_pi_apply p).comp (measurable_subtype_coe.comp measurable_fst)
    have h2 : Measurable fun q : CanonicalProfile × ℂ => Real.log (max p.1 ‖p.2 - q.2‖) :=
      Real.measurable_log.comp (measurable_const.max ((measurable_const.sub measurable_snd).norm))
    exact (h1.sub (measurable_const.mul h2)).add measurable_const
  exact Measurable.subtype_mk hfun

end HarmonicBalls
