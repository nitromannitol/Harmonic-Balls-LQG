import HarmonicBalls.FirstPass.S11r.RootedRootFinite
import HarmonicBalls.FirstPass.S11r.Frozen

/-!
# Producers of `hLen` and `hμ` for the rooted certificate (task fp-S11at-hLen-hmu-producers, q1)

Route of `notes/fp-gaps/CHATGPT-211-hb-11-13-q1-hLen-hmu-PRO.md`, section 1 (`hLen`). The rooted insertion weight is
`rootedWeight α₀ γ z w = -α₀ log|w| - γ log|w - z| + γ log max(1,|w|)` (the weight of `rootedWeylMetric`, `S11at.lean`).
Term-by-term: the weight is continuous off `{0, z}`; its Weyl scaling is finite on the punctured plane `{0}ᶜ` by the
root-finite lemma `finite_on_disk_root` (Armitage-Gardiner-style connectedness; Duplantier-Sheffield Fact 2.2 (I) and (III)
in the form of Bou-Rabee-Gwynne arXiv:2208.11795). The point `0` is handled separately (not yet in this file).
-/

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal NNReal
open HarmonicBalls

namespace FirstPassS11atProducers

/-- The rooted insertion weight `w ↦ -α₀ log|w| - γ log|w - z| + γ log max(1,|w|)` (log-singular at `0` with strength
`α₀` and at the root `z` with strength `γ`; Duplantier-Sheffield, Berestycki-Powell convention). -/
noncomputable def rootedWeight (α₀ γ : ℝ) (z : ℂ) : ℂ → ℝ :=
  fun w => -α₀ * Real.log ‖w‖ - γ * Real.log ‖w - z‖ + γ * Real.log (max 1 ‖w‖)

/-- The rooted weight is continuous off `{0, z}`. -/
theorem rootedWeight_continuousOn_compl_zero_root (α₀ γ : ℝ) {z : ℂ} :
    ContinuousOn (rootedWeight α₀ γ z) ({0}ᶜ \ {z}) := by
  intro w hw
  have hw0 : w ≠ 0 := by simpa using hw.1
  have hwz : w ≠ z := by simpa using hw.2
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
  have hnz : ‖w - z‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hwz)
  have hm : max 1 ‖w‖ ≠ 0 := (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  have c1 : ContinuousAt (fun v : ℂ => Real.log ‖v‖) w :=
    (by fun_prop : Continuous fun v : ℂ => ‖v‖).continuousAt.log hn
  have c2 : ContinuousAt (fun v : ℂ => Real.log ‖v - z‖) w :=
    (by fun_prop : Continuous fun v : ℂ => ‖v - z‖).continuousAt.log hnz
  have c3 : ContinuousAt (fun v : ℂ => Real.log (max 1 ‖v‖)) w :=
    (by fun_prop : Continuous fun v : ℂ => max 1 ‖v‖).continuousAt.log hm
  exact (((continuousAt_const.mul c1).sub (continuousAt_const.mul c2)).add
    (continuousAt_const.mul c3)).continuousWithinAt

/-- **Finiteness of the rooted Weyl scaling on the punctured plane** (`hLen`, Steps 2-3 of Chat 211 section 1).
For a Euclidean length metric `d` and a root `z ≠ 0` at which the Weyl scaling of the rooted weight tends to `0`
in `ENNReal` (the frozen rooted insertion continuity, `RootedPhysicalMetricContinuousAtInsertionFrozen`), the rooted
Weyl scaling is finite on `{0}ᶜ`. Proof: `finite_on_disk_root` on the connected open set `{0}ᶜ`. -/
theorem weylScaling_rootedWeight_ne_top_punctured {d : ℂ → ℂ → ℝ} (hd : IsEuclideanLengthMetric d) (ξ α₀ γ : ℝ)
    {z : ℂ} (hz : z ≠ 0)
    (hW : Tendsto (fun x => weylScaling d ξ (rootedWeight α₀ γ z) x z) (𝓝 z) (𝓝 0)) :
    ∀ x ∈ ({0}ᶜ : Set ℂ), ∀ y ∈ ({0}ᶜ : Set ℂ), weylScaling d ξ (rootedWeight α₀ γ z) x y ≠ ⊤ := by
  have hconn : IsConnected ({0}ᶜ : Set ℂ) := isConnected_compl_singleton_of_one_lt_rank (by simp) 0
  have hzD : z ∈ ({0}ᶜ : Set ℂ) := by simpa using hz
  exact (finite_on_disk_root hd ξ isOpen_compl_singleton hconn hzD
    (rootedWeight_continuousOn_compl_zero_root α₀ γ) hW).1

end FirstPassS11atProducers
