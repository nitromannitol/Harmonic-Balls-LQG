import HarmonicBalls.FirstPass.S11j.CertificateTransfer
import HarmonicBalls.FirstPass.Frozen.S11c
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Cameron-Martin shift of the log insertion, for the unrooted identity (18) (fp-S11r, owner n2)

Three proved tools for CHATGPT-n3-B1-B2.md section 4.1 (eq. (18)), the reduction of `h^α = h^ℂ - α log|·|` to a
whole-plane GFF plus a smooth compactly supported function:

* `exists_negLog_cutoff`: for a disk `D = ball c r` with `0 ∉ closedBall c r` there is a smooth compactly supported
  `f` with zero unit-circle average and `f = -α log|·|` on `D`. The paper's sentence "since `D̄` avoids `0`, a smooth
  compactly supported function can equal `-α log|·|` near `D̄`" is realised as `f = χ · (-α log|·|)` with `χ` a
  `ContDiffBump` equal to one on `D̄` and vanishing near `0`. The circle average vanishes because `log 1 = 0`.
* `localMeanZeroObs_eq_addFunPairing`: on test functions supported in `D`, the observation of `h^α` equals the
  observation (at `α = 0`) of `h + f`, since `f = -α log|·|` on `D`.
* `ae_mem_addFunPairing_of_ae_mem`: Cameron-Martin transfer of an almost-sure membership in a measurable set of
  distributions, from `cameronMartinFieldCertificateTransfer` (S11j/CertificateTransfer.lean) and the frozen
  `CameronMartinGFFMutualAbsCont` (Miller-Sheffield, arXiv:1302.4738v2, Proposition 2.9).
-/

namespace HarmonicBalls

open MeasureTheory Set Metric Complex

universe u

/-- A smooth compactly supported cut-off with zero unit-circle average that equals `-α log|·|` on `ball c r`, for a
disk `ball c r` with `0 < r` and `0 ∉ closedBall c r` (paper section 4.1; Cameron-Martin shift of `h^α`). -/
theorem exists_negLog_cutoff (α : ℝ) {c : ℂ} {r : ℝ} (hr : 0 < r) (h0 : (0 : ℂ) ∉ closedBall c r) :
    ∃ f : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧ HasCompactSupport f ∧ Real.circleAverage f 0 1 = 0 ∧
      ∀ x ∈ ball c r, f x = -α * Real.log ‖x‖ := by
  have hc : r < ‖c‖ := by
    have h := h0
    simp only [mem_closedBall, dist_zero_left, not_le] at h
    exact h
  -- the bump: equal to one on `closedBall c r`, supported in `ball c rOut` with `rOut < ‖c‖`
  let B : ContDiffBump c :=
    { rIn := r, rOut := (r + ‖c‖) / 2, rIn_pos := hr, rIn_lt_rOut := by linarith }
  have hrOut : (r + ‖c‖) / 2 < ‖c‖ := by linarith
  have hzero : ∀ y : ℂ, ‖y‖ < ‖c‖ - (r + ‖c‖) / 2 → B y = 0 := by
    intro y hy
    apply B.zero_of_le_dist
    have h1 : ‖c‖ - ‖y‖ ≤ ‖y - c‖ := by
      have := norm_sub_norm_le c y
      rw [norm_sub_rev] at this
      linarith [norm_sub_rev c y]
    show (r + ‖c‖) / 2 ≤ dist y c
    rw [dist_eq_norm]
    linarith
  refine ⟨fun x => B x * (-α * Real.log ‖x‖), ?_, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst hx
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (sub_pos.2 hrOut)] with y hy
      rw [mem_ball, dist_zero_right] at hy
      simp [hzero y hy]
    · apply ContDiffAt.mul B.contDiff.contDiffAt
      exact contDiffAt_const.mul ((Real.contDiffAt_log.2 (norm_ne_zero_iff.2 hx)).comp x (contDiffAt_norm ℝ hx))
  · exact B.hasCompactSupport.mul_right
  · unfold Real.circleAverage
    simp [norm_circleMap_zero]
  · intro x hx
    have hB1 : B x = 1 := B.one_of_mem_closedBall (ball_subset_closedBall hx)
    simp [hB1]

/-- On test functions supported in `D`, the observation of `h^α` is the observation of `h + f` at `α = 0`, whenever
`f = -α log|·|` on `D`. -/
theorem localMeanZeroObs_eq_addFunPairing (α : ℝ) {D : Set ℂ} {f : ℂ → ℝ}
    (hf : ∀ x ∈ D, f x = -α * Real.log ‖x‖) (T : (ℂ → ℝ) → ℝ)
    (φ : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0}) :
    localMeanZeroObs α D T φ = localMeanZeroObs 0 D (addFunPairing T f) φ := by
  have hpt : ∀ x, f x * φ.1 x = -α * (φ.1 x * Real.log ‖x‖) := by
    intro x
    by_cases hx : x ∈ D
    · rw [hf x hx]; ring
    · have hφ : φ.1 x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (φ.2.1.2.2 h))
      simp [hφ]
  have hint : ∫ x, f x * φ.1 x = -α * ∫ x, φ.1 x * Real.log ‖x‖ := by
    rw [← integral_const_mul]
    congr 1
    funext x
    exact hpt x
  unfold localMeanZeroObs fieldPairing addFunPairing
  rw [hint]
  ring

/-- Cameron-Martin transfer of an almost-sure membership: if `h^ℂ ∈ B` almost surely for a measurable set `B` of
distributions, then `h^ℂ + f ∈ B` almost surely for a smooth compactly supported `f` with zero unit-circle average. -/
theorem ae_mem_addFunPairing_of_ae_mem (hCM : CameronMartinGFFMutualAbsCont.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (f : ℂ → ℝ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hsm : ContDiff ℝ (⊤ : ℕ∞) f) (hcomp : HasCompactSupport f)
    (hcirc0 : Real.circleAverage f 0 1 = 0)
    (B : Set ((ℂ → ℝ) → ℝ)) (hB : MeasurableSet[distributionMeasurableSpace] B)
    (h : ∀ᵐ ω ∂P, hC ω ∈ B) :
    ∀ᵐ ω ∂P, addFunPairing (hC ω) f ∈ B := by
  have hBc : MeasurableSet[distributionMeasurableSpace] Bᶜ := hB.compl
  obtain ⟨-, -, hiff, -⟩ := cameronMartinFieldCertificateTransfer hCM Ω P hC hcirc f hGFF hsm hcomp hcirc0
    {ω | hC ω ∈ Bᶜ} {ω | addFunPairing (hC ω) f ∈ Bᶜ}
    ⟨Bᶜ, hBc, Filter.Eventually.of_forall fun ω => Iff.rfl, Filter.Eventually.of_forall fun ω => Iff.rfl⟩
  have h0 : P {ω | hC ω ∈ Bᶜ} = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [h] with ω hω hmem
    have hmem' : hC ω ∈ Bᶜ := hmem
    exact (Set.mem_compl_iff _ _).1 hmem' hω
  have h1 : P {ω | addFunPairing (hC ω) f ∈ Bᶜ} = 0 := hiff.2 h0
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h1] with ω hω
  simpa using hω

#print axioms HarmonicBalls.exists_negLog_cutoff
#print axioms HarmonicBalls.localMeanZeroObs_eq_addFunPairing
#print axioms HarmonicBalls.ae_mem_addFunPairing_of_ae_mem

end HarmonicBalls
